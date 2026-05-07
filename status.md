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
- Tighten incremental checking and cache invalidation
- Simplify tactic/checker APIs around `TacticEngine` and shared contextual inference helpers
- Harden unification, diagnostics, and regression coverage without adding new syntax
- Remove stale UI/kernel API leaks so interactive proof views use the real checker path

## Recent Progress
- Added shared checker-context helpers for non-compiler callers (`contextual-inference.ts`) and reused them in proof-tree elaboration
- Removed the fake kernel `inferType` stub from the interactive math renderer path by extracting a tested pure focused-type helper
- `TacticEngine` now owns goal-context `infer`/`check` entry points, eliminating more ad-hoc tactic checker setup
- Fixed induction motive abstraction for scrutinees that are not at de Bruijn index `0`, with regression coverage
- Incremental dependency invalidation now uses extracted identifier references instead of regexing every block against every known name
- Comment-only mentions no longer trigger incremental rechecks, reducing false invalidations

## Up Next
- Get triangle numbers proof working end-to-end in WYSIWYG editor
- Improve semantic quality of application/type errors, especially around implicit arguments
- Add more semantic dependency edges to the incremental checker beyond token-level references
- Unify `cases` / `induction` case-goal computation between tactics and proof-tree replay
- Prove `limit_pull_scalar`: `c * lim f = lim (c * f)`
- Case-of expressions and nested casing
- Tactic proof term validation (Match case in `checkType`)

## Open Questions
- Should we build atop Lean instead of/alongside the custom TT engine? (side-branch exploration planned)
