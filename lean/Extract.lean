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
  lean --run lean/Extract.lean <file.lean>
  Extract --serve            -- one request per stdin line, env cache resident

Imports come from the FILE'S OWN header (`headerToImports`), so `import Mathlib`
works exactly like any other import — provided Mathlib's build dir is on
LEAN_PATH. That is the only thing Mathlib mode needs, and the bridge supplies it
by asking `lake env` once (see `mathlibEnv` in server/lean-bridge.ts) rather than
running Lean under `lake`. An extra trailing argument is accepted and ignored,
for compatibility with older callers that passed a literal `mathlib`.

Lines are 1-based, columns 0-based (Lean's native convention).
-/
import Lean
open Lean Elab Meta Widget

private def natJ (n : Nat) : Json := toJson n

/-- The LEAF field names of a value, flattening one-constructor structures all
    the way down: a `DPair` whose second component is itself a pair reports
    three names, not two.

    This is what a one-line destructuring needs. `cases … with | mk a b` cannot
    nest (Lean's alternatives take plain names), so destructuring such a value
    took one `cases` per level, each indenting the rest of the proof; `obtain
    ⟨a, b, c⟩ := h` does it in one step — but only if we know how many names to
    write, which is a question about the TYPE that only the environment can
    answer. Structures are the guard: `getStructureInfo?` answers only for
    single-constructor types, which are exactly the ones with nothing to case
    on. `depth` bounds the walk so a recursive structure cannot spin. -/
private partial def flatFieldNames (v : Expr) (depth : Nat) : MetaM (Array String) := do
  if depth == 0 then return #[]
  let ty ← try Meta.whnf (← Meta.inferType v) catch _ => return #[]
  let some head := ty.getAppFn.constName? | return #[]
  let some info := getStructureInfo? (← getEnv) head | return #[]
  let mut out : Array String := #[]
  for h : i in [0 : info.fieldNames.size] do
    let f := info.fieldNames[i]!
    let some proj ← (try some <$> Meta.mkProjection v f catch _ => pure none) | return #[]
    -- ONLY the last field nests. `⟨a, b, c⟩` is Lean's anonymous constructor
    -- and it associates to the RIGHT — it means `⟨a, ⟨b, c⟩⟩` — so a flat list
    -- of names can only ever describe the right spine. Flattening an earlier
    -- field describes a LEFT-nested shape and produces a pattern Lean rejects
    -- (which is how this was caught: validation trialled it and dropped it).
    let isLast := i + 1 == info.fieldNames.size
    let nested ← if isLast then flatFieldNames proj (depth - 1) else pure #[]
    out := if nested.isEmpty then out.push f.toString else out ++ nested
  return out

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

/-- Environment cache for `--serve` mode, keyed by the import set. Environments
    are immutable — `Command.mkState` extends a copy — so reusing one across
    requests is safe, and skips the `importModules` cost (the dominant cost of
    a one-shot run) whenever the import set repeats. -/
abbrev EnvCache := IO.Ref (Array (String × Environment))

/-- Analyze one file, reusing a cached environment for its import set when
    possible. Emits the same JSON as the one-shot mode always did. -/
unsafe def analyzeFile (cache : EnvCache) (path : String) : IO Json := do
  let input ← IO.FS.readFile (System.FilePath.mk path)
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
  let key := String.intercalate "," (imports.toList.map (fun i => i.module.toString))
  let cached ← cache.get
  let env ← match cached.find? (fun e => e.1 == key) with
    | some (_, e) => pure e
    | none => do
        -- `loadExts := true` is essential: it loads the parser/notation/elab
        -- extensions (not just the constants), so `+`, numeric literals, and
        -- tactic syntax actually parse (and the prefix module's notations /
        -- unexpanders survive the olean round-trip).
        let e ← importModules imports {} (trustLevel := 1024) (loadExts := true)
        -- Bounded cache (envs are large); drop the oldest import set.
        cache.modify fun a =>
          let a := a.push (key, e)
          if a.size > 4 then a.eraseIdx! 0 else a
        pure e

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
        -- Structured + tagged goals: decompose each goal into hypotheses and a
        -- target, each pretty-printed as CodeWithInfos so the goal panel renders
        -- as WYSIWYG math (same machinery as the InfoView). We also keep the
        -- plain string (ppGoal) for fallback/diagnostics.
        -- `pp.beta`: print goals BETA-REDUCED. Substituting a lambda into a
        -- statement leaves a redex — `EpsDeltaWitness (fun x => f x + g x) …`
        -- puts the applied function in the goal, and Lean's default rendering
        -- shows it literally: `rabs (((fun x => f x + g x) x - (L + M)))`. The
        -- reader wants `|f x + g x - (L + M)|`, which is the same term; beta is
        -- definitional, so this changes only how it is SPELLED, and it is Lean's
        -- own pretty-printer option rather than term surgery of ours.
        let renderedGoals ← ci.runMetaM {} <| withOptions (fun o => o.setBool `pp.beta true) do
          ti.goalsBefore.mapM fun g => do
            let ig ← Widget.goalToInteractive g
            let hypsJson := ig.hyps.map fun h =>
              Json.mkObj
                [("names", Json.arr (h.names.map Json.str)),
                 ("type", taggedToJson h.type)]
            -- STRUCTURAL FACTS about each hypothesis, straight from the
            -- elaborator. The editor used to recover these by parsing the
            -- pretty-printed type: guessing a hypothesis's structure from
            -- token overlap, testing for a function with a regex on `→`. That
            -- reads what was RENDERED for a human, so it broke on everything
            -- rendering is allowed to do — a binder named `epsilon` displaying
            -- as `ε`, `|a|` notation, an abbreviation hiding the structure it
            -- stands for. Lean knows all of it exactly.
            --
            -- `whnf` is the point: `EpsDeltaWitness f x0 L (ε/2) δ` IS a `Pair`,
            -- and only unfolding says so.
            let hypFacts ← g.withContext do
              let envH ← getEnv
              let mut rows : Array Json := #[]
              for ldecl in ← getLCtx do
                if ldecl.isImplementationDetail then continue
                let ty ← instantiateMVars ldecl.type
                let red ← try Meta.whnf ty catch _ => pure ty
                -- TWO heads, for two different jobs — conflating them is a bug
                -- we already made once. AS WRITTEN is what type-matching needs:
                -- `ℝ` is `Carrier R`, and whnf turns that into a projection with
                -- no constant head at all, so a value goal could never be
                -- matched to the values in scope. UNFOLDED is what finding a
                -- structure's fields needs: `EpsDeltaWitness …` IS a `Pair`, and
                -- only unfolding says so.
                let headName : Option Name := ty.getAppFn.constName?
                let headUnfolded : Option Name := red.getAppFn.constName?
                -- A structure's FIELDS are what "use this hypothesis" offers;
                -- asking the environment beats inferring them from a name.
                let fields : Array String :=
                  match headUnfolded with
                  | some n => match getStructureInfo? envH n with
                    | some info => info.fieldNames.map (·.toString)
                    | none => #[]
                  | none => #[]
                -- How many branches a `cases` on this hypothesis opens. Only the
                -- environment knows — a structure splits into one, an `Either`
                -- into two — and guessing it is how the editor ended up printing
                -- two Nat-shaped cases for every split regardless of the type.
                let ctors : Nat :=
                  match headUnfolded with
                  | some n => match envH.find? n with
                    | some (.inductInfo ind) => ind.ctors.length
                    | _ => 0
                  | none => 0
                -- Claim or data? "Let ε ∈ ℝ with 0 < ε" needs to know which
                -- introduced names are CONDITIONS — and only Lean can say.
                let hypIsProp ← try Meta.isProp ty catch _ => pure false
                -- Which OTHER hypotheses this type mentions. `epsPos : 0 < ε`
                -- depends on ε; that dependency (not Prop-ness, which this
                -- preset's Type-valued relations don't have) is what marks it
                -- a CONDITION on ε rather than a binding of its own.
                let depSt := collectFVars {} ty
                let mut hypDeps : Array Json := #[]
                for fv in depSt.fvarIds do
                  if let some d := (← getLCtx).find? fv then
                    unless d.isImplementationDetail do
                      hypDeps := hypDeps.push (Json.str d.userName.toString)
                -- Every name a one-line `obtain ⟨…⟩ := h` would have to bind.
                -- Depth 2 — the value and ONE level of nesting — because that
                -- is the shape these statements have ("a δ, together with the
                -- facts about it") and it is where a reader stops. Deeper is
                -- not more informative, it is less: at depth 3 this preset's
                -- `0 < δ` comes apart into the pair it is defined as, which
                -- nobody thinks of as two facts. Anyone who wants that level
                -- destructures again — which now costs a row, not an indent.
                let flat ← flatFieldNames ldecl.toExpr 2
                rows := rows.push <| Json.mkObj
                  [("name", Json.str ldecl.userName.toString),
                   ("typeHead", match headName with
                     | some n => Json.str n.toString
                     | none => Json.null),
                   ("isFun", Json.bool red.isForall),
                   ("isProp", Json.bool hypIsProp),
                   ("dependsOn", Json.arr hypDeps),
                   ("ctors", natJ ctors),
                   ("fields", Json.arr (fields.map Json.str)),
                   ("flatFields", Json.arr (flat.map Json.str))]
              pure rows
            let plain := toString (← Meta.ppGoal g)
            -- Prop targets are claims to PROVE; non-Prop targets (ℝ, ℕ, a
            -- function…) are values to CHOOSE. The UI words them differently,
            -- and only Lean can tell them apart reliably.
            let isProp ← try Meta.isProp (← g.getType) catch _ => pure true
            -- The goal's own head constant, so "which lemmas conclude something
            -- shaped like this?" is a comparison of CONSTANTS rather than of
            -- rendered operator text. `0 < x` is `rlt 0 x` however it prints.
            -- `instantiateMVars` first: an uninstantiated metavariable has no
            -- constant head, so the same goal reported at two points would
            -- answer `DPair` at one and nothing at the other — and a goal whose
            -- head is missing matches no lemma at all.
            let targetHead : Option Name := (← instantiateMVars (← g.getType)).getAppFn.constName?
            pure <| Json.mkObj <|
              (match ig.userName? with
               | some n => [("case", Json.str n)]
               | none => []) ++
              [("hyps", Json.arr hypsJson),
               ("hypFacts", Json.arr hypFacts),
               ("targetHead", match targetHead with
                 | some n => Json.str n.toString
                 | none => Json.null),
               ("targetTagged", taggedToJson ig.type),
               ("isProp", Json.bool isProp),
               ("plain", Json.str plain)]
        -- Value goals (a term to CHOOSE, not a claim to prove): a goal whose
        -- metavariable occurs in a SIBLING goal's type — e.g. the midpoint `?b`
        -- after `apply ltLeTrans`, mentioned by `0 < ?b` and `?b ≤ ε/2`.
        -- Computed from goalsAfter under mctxAfter, i.e. at the instant the
        -- tactic split its goals: later lines assign the metavariable (and it
        -- vanishes from the siblings' pretty-printed text), but THIS record
        -- never goes stale. Reported as case tags so the UI can match them to
        -- the branches. (`isProp` can't express this: from-scratch presets
        -- state claims in Type, so EVERY goal there is non-Prop.)
        let ciAfter := { ci with mctx := ti.mctxAfter }
        let valueTags ← ciAfter.runMetaM {} do
          ti.goalsAfter.filterMapM fun g => do
            let dependedOn ← ti.goalsAfter.anyM fun g2 => do
              if g2 == g then pure false else do
                let t ← instantiateMVars (← g2.getType)
                pure (t.find? (fun e => e.isMVar && e.mvarId! == g) |>.isSome)
            if !dependedOn then pure none else do
              let tag ← g.getTag
              pure (if tag.isAnonymous then none else some (Json.str tag.toString))
        goals := goals.push <| Json.mkObj <|
          ("goals", Json.arr renderedGoals.toArray) ::
          (if valueTags.isEmpty then [] else [("valueCaseTags", Json.arr valueTags.toArray)]) ++
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
      -- Drop notation/macro machinery generated by `infixl`/`notation`/`prefix`/
      -- `macro`/`syntax`: these create constants named `«term…»`/`«command…»` and
      -- `….macroRules`/`…docString` whose types are ParserDescr/Syntax — not user
      -- math. Recognized generically by name shape + result type head.
      if nameStr.startsWith "«term" || nameStr.startsWith "«command"
          || nameStr.endsWith ".macroRules" || nameStr.endsWith "docString"
          || nameStr.endsWith ".eq_def" then continue
      let typeHead := ci.type.getForallBody.getAppFn
      match typeHead with
      | .const tn _ =>
        let t := tn.toString
        if t == "Lean.ParserDescr" || t == "Lean.TrailingParserDescr"
            || t == "Lean.Macro" || t == "Lean.PrettyPrinter.Unexpander" then continue
      | _ => pure ()
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
      -- STRUCTURAL FACTS, for deciding which lemmas are worth trying. Same
      -- reason as the hypothesis facts above: the alternative is parsing this
      -- declaration's PRETTY-PRINTED type, which is written for a human and
      -- reshaped by every notation the preset defines. `convertEps` was
      -- unreachable because its binder is spelled `epsilon` and the goal says
      -- `ε` — one thing with two spellings, invisible to text matching.
      let (conclHead, conclIsInductive, conclCtors, argHeads, premises) ←
        Meta.forallTelescopeReducing ci.type fun args body => do
          let envD ← getEnv
          -- NOT unfolded, deliberately. `rlt a b` whnfs to `Pair …` — as does
          -- every other relation here — which collapses the very distinction
          -- this exists to make. The head AS WRITTEN is what tells `<` from `≤`
          -- from `=`, and it is already immune to notation.
          let bodyRed := body
          let headOf (e : Expr) : Option Name :=
            match e.getAppFn with
            | .const n _ => some n
            | _ => none
          let ch := headOf bodyRed
          let isInd :=
            match ch with
            | some n => match envD.find? n with
              | some (.inductInfo _) => true
              | _ => false
            | none => false
          -- Branches a `cases` on THIS lemma's result opens: `leTotal a b`
          -- concludes an `Either`, so splitting on it gives two. (Kept separate
          -- from `isInd` — `False` is an inductive with no constructors.)
          let ctorCount :=
            match ch with
            | some n => match envD.find? n with
              | some (.inductInfo ind) => ind.ctors.length
              | _ => 0
            | none => 0
          let mut heads : Array Json := #[]
          let mut goalsLeft := 0
          for a in args do
            let ld ← a.fvarId!.getDecl
            unless ld.binderInfo.isExplicit do continue
            heads := heads.push (match headOf ld.type with
              | some n => Json.str n.toString
              | none => Json.null)
            -- An argument the CONCLUSION mentions is solved by unifying with
            -- the goal; one it doesn't mention becomes a goal of its own. That
            -- is exactly why `apply leLtTrans` asks for a midpoint AND two
            -- proofs (3), while `apply convertEps` asks for one thing (1).
            unless bodyRed.hasAnyFVar (· == a.fvarId!) do
              goalsLeft := goalsLeft + 1
          pure (ch, isInd, ctorCount, heads, goalsLeft)
      let mut fields : List (String × Json) :=
        [("name", Json.str declName.toString),
         ("kind", Json.str kindStr),
         ("prettyType", Json.str prettyType),
         ("typeTagged", typeTagged),
         ("conclHead", match conclHead with
           | some n => Json.str n.toString
           | none => Json.null),
         ("conclIsInductive", Json.bool conclIsInductive),
         ("conclCtors", natJ conclCtors),
         ("argHeads", Json.arr argHeads),
         ("premises", natJ premises),
         ("line", natJ pos.line), ("col", natJ pos.column)]
      -- Value, for plain defs only (theorems' proofs are noise here). Skip values
      -- compiled to the recursor machinery (`brecOn`/`rec`/`WellFounded.fix`),
      -- which print as unreadable blobs — the old editor showed the surface value
      -- and we have none for equation-compiled defs, so we omit rather than show
      -- noise. Direct (non-matching) def bodies still render.
      match ci with
      | .defnInfo di =>
        -- Peek under lambda binders to the application head (equation-compiled
        -- defs are `fun … => X.brecOn …`).
        let rec stripLambdas : Expr → Expr
          | .lam _ _ b _ => stripLambdas b
          | e => e
        let valHead := (stripLambdas di.value).getAppFn
        let isCompiledBlob :=
          match valHead with
          | .const vn _ =>
            let v := vn.toString
            v.endsWith ".brecOn" || v.endsWith ".rec" || v.endsWith ".recAux"
              || v == "WellFounded.fix" || v.endsWith ".brecOnAux"
          | _ => false
        if !isCompiledBlob then
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

  return Json.mkObj
    [("messages", Json.arr messages),
     ("goals", Json.arr goals),
     ("declarations", Json.arr declarations)]

/-- `--serve` mode: a persistent request loop — the same trick `lean --server`
    uses to make the text editor fast. One file path per stdin line; one
    compressed JSON response per stdout line. The env cache persists across
    requests, so repeat analyses skip `importModules` entirely (the dominant
    per-request cost) and only elaborate the file's own commands. -/
unsafe def serveLoop (cache : EnvCache) : IO Unit := do
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  if line.isEmpty then return -- EOF: parent closed stdin, shut down.
  let path := line.trim
  if path.isEmpty then
    serveLoop cache
  else
    let out ← try
        analyzeFile cache path
      catch e =>
        pure <| Json.mkObj [("serveError", Json.str (toString e))]
    IO.println out.compress
    (← IO.getStdout).flush
    serveLoop cache

-- `unsafe` because `enableInitializersExecution` (needed for `loadExts`) is unsafe.
unsafe def main (args : List String) : IO Unit := do
  -- Required before `importModules (loadExts := true)` so module initializers
  -- (which register parsers/notation/elaborators) may run.
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  match args with
  | ["--serve"] => do
      let cache : EnvCache ← IO.mkRef #[]
      serveLoop cache
  | path :: _ => do
      let cache : EnvCache ← IO.mkRef #[]
      let out ← analyzeFile cache path
      IO.println out.compress
  | [] => do
      IO.eprintln "usage: Extract (<file.lean> [mathlib] | --serve)"
      IO.Process.exit 1
