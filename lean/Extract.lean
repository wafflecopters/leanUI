/-
LeanUI extractor.

Runs the user's source through the Lean frontend and emits a single JSON object:

  { "messages":     [ {severity,startLine,startCol,endLine,endCol,text}, ... ],
    "goals":        [ {startLine,startCol,endLine,endCol,goals:[string]}, ... ],
    "declarations": [ {name,kind,prettyType,prettyValue?,line,col}, ... ] }

`messages` are the diagnostics (errors / warnings / `#check` info).
`goals` are tactic goal-states keyed by the source range of the tactic, so the
editor can show the goal at the cursor (pick the smallest range containing it).
`declarations` are the user's top-level defs/theorems/inductives in source order
(name + pretty-printed type, and value for plain `def`s) — what the results
panel renders. Auto-generated constants (recursors, constructors, internal
detail names) are filtered out.

Usage:
  lean --run lean/Extract.lean <file.lean> [mathlib]

The optional `mathlib` arg additionally imports Mathlib (requires running under
`lake env` in the Mathlib-enabled package). Without it we import only `Init`
(core Lean). NOTE: for v1 the user's own `import` lines are ignored — the import
set is fixed (Init [+ Mathlib]); this keeps each invocation deterministic.

Lines are 1-based, columns 0-based (Lean's native convention).
-/
import Lean
open Lean Elab Meta Widget

private def natJ (n : Nat) : Json := toJson n

/-- Serialize a `CodeWithInfos` (`TaggedText SubexprInfo`) tree to JSON for the
    WYSIWYG math editor. `pos` is the `SubExpr.Pos` of the subexpression — the
    stable id used as the math editor's `Group` htmlId (click-to-select target).
    The `info` RPC ref is intentionally dropped (it isn't serializable and the
    position is enough). -/
private partial def taggedToJson (tt : TaggedText SubexprInfo) : Json :=
  match tt with
  | .text s => Json.mkObj [("t", "text"), ("s", Json.str s)]
  | .append as => Json.mkObj [("t", "append"), ("kids", Json.arr (as.map taggedToJson))]
  | .tag info child =>
      Json.mkObj [("t", "tag"), ("pos", Json.str (toString info.subexprPos)),
                  ("child", taggedToJson child)]

private def sevString : MessageSeverity → String
  | .error => "error"
  | .warning => "warning"
  | .information => "information"

private def mkRangeFields (sl sc el ec : Nat) : List (String × Json) :=
  [("startLine", natJ sl), ("startCol", natJ sc), ("endLine", natJ el), ("endCol", natJ ec)]

-- `unsafe` because `enableInitializersExecution` (needed for `loadExts`) is unsafe.
unsafe def main (args : List String) : IO Unit := do
  let some path := args[0]?
    | do IO.eprintln "usage: Extract <file.lean> [mathlib]"; IO.Process.exit 1
  let input ← IO.FS.readFile (System.FilePath.mk path)
  -- Required before `importModules (loadExts := true)` so module initializers
  -- (which register parsers/notation/elaborators) may run.
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)

  -- Build the environment from the file's own header. `headerToImports` returns
  -- the auto-prelude `Init` (+ its meta import) plus any `import` lines the user
  -- wrote — exactly the import set `lean --json` uses. We import them ourselves
  -- with a high trustLevel (processHeader's default trustLevel=0 import can fail
  -- and silently fall back to an EMPTY env, which breaks `+`, numeric literals,
  -- and tactics). For Mathlib mode the source carries `import Mathlib` and we run
  -- under `lake env` so it's on the path.
  let inputCtx := Parser.mkInputContext input path
  let (header, parserState, msgLog) ← Parser.parseHeader inputCtx
  let imports := headerToImports header
  -- `loadExts := true` is essential: it loads the parser/notation/elab
  -- extensions (not just the constants), so `+`, numeric literals, and tactic
  -- syntax actually parse. Without it the command parser rejects `+` etc.
  let env ← importModules imports {} (trustLevel := 1024) (loadExts := true)

  let cmdState := Command.mkState env msgLog {}
  let cmdState := { cmdState with infoState.enabled := true }
  let frontendState ← IO.processCommands inputCtx parserState cmdState
  let cmdState := frontendState.commandState
  let fm := inputCtx.fileMap

  -- Diagnostics -------------------------------------------------------------
  let mut messages : Array Json := #[]
  for msg in cmdState.messages.toList do
    let text ← msg.data.toString
    let sp := msg.pos
    let ep := msg.endPos.getD msg.pos
    messages := messages.push <| Json.mkObj <|
      ("severity", Json.str (sevString msg.severity)) ::
      ("text", Json.str text) ::
      mkRangeFields sp.line sp.column ep.line ep.column

  -- Tactic goal states ------------------------------------------------------
  let mut pairs : Array (ContextInfo × TacticInfo) := #[]
  for t in cmdState.infoState.trees.toArray do
    pairs := InfoTree.foldInfo (init := pairs) (fun ci info acc =>
      match info with
      | .ofTacticInfo ti => acc.push (ci, ti)
      | _ => acc) t

  let mut goals : Array Json := #[]
  -- Several InfoTree nodes can share a source range (one per elaboration step);
  -- keep only the first goal-state seen per range to avoid a flood of duplicates.
  let mut seen : Std.HashSet (Nat × Nat × Nat × Nat) := {}
  for (ci, ti) in pairs do
    match ti.stx.getRange? with
    | none => pure ()
    | some range =>
      if ti.goalsBefore.isEmpty then pure () else
        let sp := fm.toPosition range.start
        let ep := fm.toPosition range.stop
        let key := (sp.line, sp.column, ep.line, ep.column)
        if seen.contains key then pure () else
        seen := seen.insert key
        let ci := { ci with mctx := ti.mctxBefore }
        let rendered ← ci.runMetaM {} do
          ti.goalsBefore.mapM fun g => do
            let fmt ← Meta.ppGoal g
            pure (toString fmt)
        goals := goals.push <| Json.mkObj <|
          ("goals", Json.arr (rendered.toArray.map Json.str)) ::
          mkRangeFields sp.line sp.column ep.line ep.column

  -- Declarations ------------------------------------------------------------
  -- The user's own top-level constants, in source order. `map₂` holds the
  -- constants added in THIS file (not imported ones). We use the env's
  -- declaration-range metadata (the same source `lean --server` uses for
  -- go-to-def) both to locate each decl and to filter out auto-generated names
  -- (recursors, `.rec`/`.casesOn`, match auxiliaries) which have no user range.
  let coreCtx : Core.Context := { fileName := path, fileMap := fm }
  let coreState : Core.State := { env := cmdState.env }
  let declAction : MetaM (Array (Nat × Nat × Json)) := do
    let mut rows : Array (Nat × Nat × Json) := #[]
    let env := cmdState.env
    for (declName, ci) in env.constants.map₂.toList do
      -- Keep only what the user wrote: drop internal names and the machinery
      -- the elaborator generates around an `inductive` (recursors, `.casesOn`/
      -- `.recOn`, `.noConfusion`, constructors, and the `.ctorIdx`/`.ctorElim`/
      -- `.elim` helpers). These are standard Lean-generated names, not domain
      -- knowledge.
      if declName.isInternal then continue
      if isAuxRecursor env declName || isNoConfusion env declName then continue
      match ci with
      | .recInfo _ => continue   -- `.rec`
      | .ctorInfo _ => continue  -- constructors (surfaced under their inductive in M3)
      | _ => pure ()
      let nameStr := declName.toString
      if nameStr.endsWith ".ctorIdx" || nameStr.endsWith ".ctorElim"
          || nameStr.endsWith ".elim" || nameStr.endsWith ".ctorElimType" then continue
      let some ranges ← findDeclarationRanges? declName | continue
      let pos := ranges.range.pos
      let kindStr :=
        match ci with
        | .inductInfo _ => "inductive"
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "def"
        | .axiomInfo _ => "axiom"
        | .opaqueInfo _ => "opaque"
        | _ => "def"
      let prettyType := toString (← Meta.ppExpr ci.type)
      -- Tagged pretty-print for the WYSIWYG math editor (text + subexpr spans).
      let typeTagged := taggedToJson (← ppExprTagged ci.type)
      let mut fields : List (String × Json) :=
        [("name", Json.str declName.toString),
         ("kind", Json.str kindStr),
         ("prettyType", Json.str prettyType),
         ("typeTagged", typeTagged),
         ("line", natJ pos.line), ("col", natJ pos.column)]
      -- Value, for plain defs only (theorems' proofs are noise here).
      match ci with
      | .defnInfo di =>
        fields := fields ++
          [("prettyValue", Json.str (toString (← Meta.ppExpr di.value))),
           ("valueTagged", taggedToJson (← ppExprTagged di.value))]
      | _ => pure ()
      rows := rows.push (pos.line, pos.column, Json.mkObj fields)
    pure rows
  let (declRows, _) ← (declAction.run' (s := {})).toIO coreCtx coreState
  -- Source order.
  let sortedRows := declRows.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1))
  let declarations := sortedRows.map (·.2.2)

  let out := Json.mkObj
    [("messages", Json.arr messages),
     ("goals", Json.arr goals),
     ("declarations", Json.arr declarations)]
  IO.println out.compress
