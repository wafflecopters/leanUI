# Project Status

## Vision
Bridge between Overleaf and Lean: write LaTeX-like code with proof-correctness, or write Lean code with LaTeX presentation and WYSIWYG ergonomics. We are exploring both a custom dependently typed language (TT) and the possibility of building atop Lean itself.

## Active Branch: `lean-backend` (Lean 4 pivot)
Experiment to replace the entire custom TT/TTK engine with **Lean 4** as the sole backend (typechecking, inference, tactics), served by a Lean process that `bun run dev` launches alongside the web server. Keep only the text-editor page (source box + compiled results + WYSIWYG) and port all WYSIWYG features onto Lean. Mathlib is a toggle (off by default for now).
- **M1 — DONE (proof of life):** `server/lean-bridge.ts` runs `lean --json`; `POST /api/check` returns diagnostics; `/lean` route renders them with Monaco markers.
- **M1.5 — DONE (real proof editor on Lean, testable end-to-end):** `lean/Extract.lean` builds the env via `headerToImports` + `importModules (loadExts := true)` (with `enableInitializersExecution`, `unsafe main`), runs the frontend, and walks the InfoTree → `{messages, goals}` JSON: diagnostics + per-tactic goal states (with hypotheses + case names) keyed by source range, deduped per range. Verified messages match `lean --json` ground truth exactly. `POST /api/analyze` serves it; the `/lean` page shows live **goal-at-cursor** (InfoView-style) + diagnostics + Monaco squiggles. Confirmed through the full stack via `bun run dev` → http://localhost:3000/lean (web :3000 → proxy → bridge :3457 → lean). ~3s/analyze core mode. Bridge port 3457 (env `LEAN_BRIDGE_PORT`; 3001 squatted by another local project). Tests: `src/lean/goalAtCursor.test.ts` + `server/lean-bridge.test.ts` (11 pass); tsc clean.
- **M2 — IN PROGRESS (Lean editor is now THE editor):** Decision: rebuild the page shell on a **Lean-native contract** (not shim into the old TT `CompileResult`); reuse the deep components (Monaco config, math editor, proof tree) when WYSIWYG returns in M3. `lean/Extract.lean` now also emits **declarations** (user defs/theorems/inductives in source order: name, kind, pretty type, value for defs, position) — filtered to user-authored constants via Lean's principled predicates (isAuxRecursor/isNoConfusion/recInfo/ctorInfo/internal). The `LeanEditorPage` is rebuilt as a proper dark-themed shell (Goal / Declarations / Messages panels + Lean-native preset picker `src/lean/presets.ts` + Mathlib toggle) and is now the **default route `/`**; legacy TT page demoted to `/tt-legacy` (deleted in M5). 4 core presets verified compiling on Lean.
- **M3 — IN PROGRESS (WYSIWYG math on Lean):** The math editor renders REAL Lean expressions. `lean/Extract.lean` now emits `typeTagged`/`valueTagged` per declaration via `ppExprTagged` (Lean's `CodeWithInfos` = tagged pretty-print tree with subexpr positions). New pure converter `src/lean/codeWithInfos.ts` (`codeWithInfosToMathRow`) turns that tagged tree into the existing `MathRow` model — wrapping each subexpression in a `Group{htmlId}` (the click-to-rewrite target), tokenizing text runs into symbols, mapping Lean unicode (→, ≤, ℕ…) to LaTeX. The whole math editor (render/edit/navigate/round-trip) is reused unchanged; only the PRODUCER is new. Two render paths wired into the `/` editor's Declarations panel: `LeanMathView` (static KaTeX) and **`LeanMathEditor` (the REAL interactive structured `MathEditor`)** seeded from the Lean MathRow — click a declaration card to activate structured editing (cursor, keyboard, fractions, sub/sup, navigation) over the Lean expression. Verified end-to-end through the bridge (subexpr paths `/0`,`/1`,`/1/0/1` intact); rsbuild bundle (MathEditor + KaTeX deps) builds clean. Tests: `src/lean/codeWithInfos.test.ts` (11). Goals are WYSIWYG (`Widget.goalToInteractive` → `{case?, hyps, targetTagged, plain}`). **The REAL `ProofTreeEditor` now runs on Lean** via a dependency-injection seam — NOT a simplified rebuild. Mechanism (all unit-tested + CLI/stack-verified): proof tree → `proofTreeToLean` (Lean tactic block + per-node ranges) → `assembleProofDecl` → `/api/analyze` → `mapLeanGoalsToNodes` → `Map<ProofNodeId, NodeGoalInfo>` (drop-in for `replayEntireTree`). `ProofTreeEditor` gained optional `goalMapOverride`/`typedContextOverride` props (legacy TT path unchanged when absent). `useLeanProofGoals` is the async provider (debounced, stale-discarding). `leanTacticsToTree` seeds the editor from the user's actual proof (parse↔print round-trip stable); `extractTacticBlock` slices the proof from source. `LeanWysiwygPanel` mounts the real `ProofTreeEditor` per theorem with goals from Lean. Verified through the live stack: induction proof → goals at every tactic line with case names, 0 errors.
- **Write-back DONE:** structural proof edits reprint (`proofTreeToSource`, omits fabricated terminal `sorry`s) + splice into Monaco source (`spliceTacticBlock`) → source↔WYSIWYG stay in sync. Build loop verified live: hole → `exact rfl` solves → `exact 42` shows Lean's real type error. Preset proofs round-trip through the real-app flow with 0 errors (caught+fixed: multi-lemma `rw` dropping lemmas; `simp`-then-hole writing invalid `sorry`).
- **Still TODO:** (M4) AUTO-suggestions on Lean — suggestion pills (rewrite/apply/induction/construct, term-builder) still call the TT engine; on the Lean path they're absent-not-broken (graceful). Needs a Lean-backed suggestion source (`exact?`/`rw?`/`apply?` or InfoTree) + `interactiveGoal` populated from tagged goals for subterm click-to-select. MathRow→Lean-source for type/value edits. Validation border polish.
- **Next:** M4 Lean-backed suggestions + interactive-goal subterm selection → M5 delete TT/TTK + legacy page.
- Toolchain: Lean 4.30.0 + Lake 5.0.0 via elan (`~/.elan/bin`).

## Near-Term Goal
Live demo proving `sum(0..n, i) = n*(n+1)/2` (triangle numbers) in a WYSIWYG editor that:
- Produces real-looking math, not code-shaped proof terms
- Offers recommendations/autocomplete for speed
- Builds proof terms or tactics under the hood

## Milestone Proofs
1. Triangle numbers: `∑_{i=0}^{n} i = n(n+1)/2`
2. Limits add: `lim f + lim g = lim (f + g)`
3. Chain rule: `d/dx f(g(x)) = f'(g(x)) · g'(x)`

## Current Focus
- Keep converging text tactics, the structured tactic tree, and WYSIWYG prose onto one shared tactic/proof-tree/replay core.
- Keep hardening the Prop/Sort kernel story: proof irrelevance, singleton elimination, large-elim restrictions, and PLift/ULift-style universe behavior.
- Keep shrinking oversized adapter files, especially `goal-computation.ts` and `ProofTreeEditor.tsx`, by extracting tested pure helpers and small rendering/replay modules.
- Keep replacing domain-name heuristics in generic proof-tree/editor code with definition-backed or registry-backed classification.
- Keep the full smoke gate non-negotiable: `npx tsc --noEmit && npm test`.

## Recent Progress
- Tightened large-elimination soundness: non-singleton Prop elimination now fails closed when the motive sort cannot be proven Prop, with a narrow safe fallback for heads whose declared codomain is definitely Prop.
- Made the singleton/large-elim classifier more conservative: unknown inductive result shapes no longer grant large elimination.
- Moved the proof-irrelevance-only type classifier out of `whnf.ts` into an explicit helper module, keeping WHNF smaller and making the eventual checker-owned oracle seam clearer.
- Removed stray `debugger` statements from non-test compiler paths and gated an ungated totality case-tree log.
- Reduced proof-tree domain coupling: `isValueTypeGoal` now prefers definition-backed sort classification for real replay, with hardcoded head sets only as a no-definition fallback, and added tests for custom non-hardcoded Prop/Type heads.

## Up Next
- Replace the proof-irrelevance classifier fallback with a checker/meta-owned oracle so defeq does not duplicate inference rules.
- Split `goal-computation.ts` into replay, rendering-normalization, alias/literal folding, and case/induction modules.
- Split `ProofTreeEditor.tsx` prose rows into dedicated component modules now that the pure helper seams exist.
- Finish tactic proof-term validation by adding the `Match` case to `checkType`.
- Move remaining hardcoded proposition/value classifiers behind generic definition metadata or syntax/registry annotations.

## Open Questions
- Should we build atop Lean instead of, or alongside, the custom TT engine?
- Which large cleanup should come first after the current Prop/tactics convergence stabilizes: `goal-computation.ts`, `ProofTreeEditor.tsx`, or checker/meta proof-irrelevance ownership?
