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
- Consolidate pattern-binder accounting across elaboration, unification, substitution, recursion, and proof/tactic replay
- Keep shrinking duplicated `Match`-walker logic in compiler/tactic/proof-tree code
- Harden generic kernel transforms around clause binder depth and metadata preservation
- Expand low-level regressions before doing another round of solver/diagnostic tightening

## Recent Progress
- Added shared `pattern-binders.ts` helpers and pushed them through compile/elab/unify/subst/with-desugar/with-abstraction/record code
- Fixed generic `Match` term transforms to account for clause binders correctly, including `transformVarsInTerm` and nested substitution/renaming paths
- Hardened tactic/proof-tree walkers (`induction`, `subst`, goal replay) to use clause-wide binder counts instead of ad-hoc first-pattern logic
- Fixed structural recursion bookkeeping so named constructor arguments participate in variable collection and structurally-smaller analysis
- Added regression coverage for clause-level named-pattern depth in substitution, generic term var transforms under `Match`, and recursion named-arg traversal
- Re-verified the worktree with full `tsc --noEmit` and full `vitest run src` after the deeper pipeline pass

## Up Next
- Get triangle numbers proof working end-to-end in WYSIWYG editor
- Improve semantic quality of application/type errors, especially around implicit arguments and partial application
- Push the same DRY/hardening pass into remaining generic kernel/normalization walkers that still special-case `Match`
- Add more semantic dependency edges to the incremental checker beyond token-level references
- Unify `cases` / `induction` case-goal computation between tactics and proof-tree replay
- Prove `limit_pull_scalar`: `c * lim f = lim (c * f)`
- Case-of expressions and nested casing / refinement
- Tactic proof term validation (Match case in `checkType`)

## Open Questions
- Should we build atop Lean instead of/alongside the custom TT engine? (side-branch exploration planned)
