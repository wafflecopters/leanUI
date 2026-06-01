/-
LeanUI extractor.

Runs the user's source through the Lean frontend and emits a single JSON object:

  { "messages": [ {severity,startLine,startCol,endLine,endCol,text}, ... ],
    "goals":    [ {startLine,startCol,endLine,endCol,goals:[string]}, ... ] }

`messages` are the diagnostics (errors / warnings / `#check` info).
`goals` are tactic goal-states keyed by the source range of the tactic, so the
editor can show the goal at the cursor (pick the smallest range containing it).

Usage:
  lean --run lean/Extract.lean <file.lean> [mathlib]

The optional `mathlib` arg additionally imports Mathlib (requires running under
`lake env` in the Mathlib-enabled package). Without it we import only `Init`
(core Lean). NOTE: for v1 the user's own `import` lines are ignored — the import
set is fixed (Init [+ Mathlib]); this keeps each invocation deterministic.

Lines are 1-based, columns 0-based (Lean's native convention).
-/
import Lean
open Lean Elab

private def natJ (n : Nat) : Json := toJson n

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

  let out := Json.mkObj [("messages", Json.arr messages), ("goals", Json.arr goals)]
  IO.println out.compress
