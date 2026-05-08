# Project Status

## Vision
Bridge between Overleaf and Lean: write LaTeX-like code with proof-correctness, or write Lean code with LaTeX presentation and WYSIWYG ergonomics. Exploring both a custom dependently-typed language (TT) and potentially building atop Lean itself.

## Near-Term Goal
Live demo proving `sum(0..n, i) = n*(n+1)/2` (triangle numbers) in a WYSIWYG editor that:
- Produces real-looking math (not code)
- Offers recommendations/autocomplete for speed
- Builds proof terms or tactics under the hood

## Milestone Proofs (sequential)
1. **Triangle numbers**: `∑_{i=0}^{n} i = n(n+1)/2` — current target
2. **Limits add**: `lim_{x→x₀} f(x) + lim_{x→x₀} g(x) = lim_{x→x₀} (f(x) + g(x))`
3. **Chain rule**: `d/dx f(g(x)) = f'(g(x))·g'(x)`

## Current Focus
Upleveling the core engine while preserving the current language surface:
- Keep converting stale compiler/proof-tree TODOs into real regressions or concrete fixes
- Preserve useful editor/type-info output even when clause checking later fails
- Keep tightening `with` desugaring/abstraction coverage so helper tests become real end-to-end regressions
- Keep collapsing the gap between helper-only `with` abstraction logic and the real production desugaring path
- Keep shrinking duplicated `Match`/clause helper logic across kernel, surface, compiler, and tactics
- Decide which remaining large implementation TODO should be next: `bridge.ts`, `record.ts`, or tactic-workspace/editor gaps

## Recent Progress
- Aligned the kernel-side `with-abstraction` helper with the production fix so binder-local variables are no longer shifted when inserting fresh with-binders under lambdas or dependent families
- Generalized production `with` return-type abstraction to handle computed scrutinees, not just bare variables, and fixed the binder-shifting bug that surfaced in dependent `DPair` families
- Added direct regressions for computed-scrutinee abstraction and dependent-family binder preservation in `with.test.ts`, plus kept the nested `sigmaSum` `.tt` repro green end-to-end
- Re-verified the worktree with full `tsc --noEmit` and full `vitest run src` (`140` files, `2869` passing)
- Moved clause-pattern type-info recording earlier in `checkMatchClause`, so failing with-clauses still expose useful cursor/type info
- Turned the old `No neq` with-clause type-info TODOs into real regressions, plus adjacent branch-selection coverage
- Converted the remaining `with-abstraction.test.ts` `test.todo`s into active regression tests for single/multiple scrutinees, ill-typed abstraction, and implicit binder preservation
- Replaced the old parser-side `with` WIP smoke test with real assertions, including multi-scrutinee comma syntax coverage

## Up Next
- Get triangle numbers proof working end-to-end in WYSIWYG editor
- Improve semantic quality of application/type errors, especially around implicit arguments and partial application
- Wire ill-typed abstraction detection into the real `with` compilation path instead of leaving it helper-only
- Push the same DRY/hardening pass into the remaining generic kernel/solver walkers that still special-case `Match` or clause contexts
- Choose the next large implementation TODO to burn down: `bridge.ts` proof terms, `record.ts` checking, or editor-side tactic workspace gaps
- Add more semantic dependency edges to the incremental checker beyond token-level references
- Unify `cases` / `induction` case-goal computation between tactics and proof-tree replay
- Prove `limit_pull_scalar`: `c * lim f = lim (c * f)`
- Case-of expressions and nested casing / refinement
- Tactic proof term validation (Match case in `checkType`)

## Open Questions
- Should we build atop Lean instead of/alongside the custom TT engine? (side-branch exploration planned)
