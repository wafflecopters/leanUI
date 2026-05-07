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
- Tighten solver/elaboration handoff so solved metas preserve usable elaborated structure
- Harden indexed-case goal computation, especially when constructor indices mention constructor params
- Keep shrinking duplicated `Match`/clause helper logic across kernel, surface, compiler, and tactics

## Recent Progress
- Added full-normalization `Match` iota reduction for constructor scrutinees, with focused normalization regressions
- Fixed `TCEnv.solveMetasAndConstraints` to preserve a zonked `elaboratedTerm`, with regression coverage in let-inference
- Turned the old `nth tail f` RHS type-info TODO into a real passing regression asserting `Fin` survives through cursor/type-info lookup
- Closed proof-tree indexed-case TODO by refining index variables against constructor parameters (synthetic `Wrap : Nat -> Type` regression)
- Converted stale eta/axiom-K TODO scaffolding into real assertions and removed outdated warnings
- Re-verified the worktree with full `tsc --noEmit` and full `vitest run src` (`139` files, `2830` passing, `9` todo)

## Up Next
- Get triangle numbers proof working end-to-end in WYSIWYG editor
- Improve semantic quality of application/type errors, especially around implicit arguments and partial application
- Push the same DRY/hardening pass into the remaining generic kernel/solver walkers that still special-case `Match` or clause contexts
- Decide which large remaining TODOs should become real implementation work next: `bridge.ts` proof terms, `record.ts` checking, or editor-side tactic workspace gaps
- Add more semantic dependency edges to the incremental checker beyond token-level references
- Unify `cases` / `induction` case-goal computation between tactics and proof-tree replay
- Prove `limit_pull_scalar`: `c * lim f = lim (c * f)`
- Case-of expressions and nested casing / refinement
- Tactic proof term validation (Match case in `checkType`)

## Open Questions
- Should we build atop Lean instead of/alongside the custom TT engine? (side-branch exploration planned)
