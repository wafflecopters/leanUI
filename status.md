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
- Keep shrinking `src/compiler/compile.ts` into a thin driver over explicit subsystems; the live block compiler, impl annotation registration, and incremental-state replay are now split, and the next seam is the remaining top-level full/incremental loop orchestration
- Keep extracting pure compiler helpers with direct unit tests plus end-to-end regressions, especially around block compilation, incremental contribution replay, declaration assembly, and editor-facing compile data
- Keep deleting dead parallel compiler paths and temporary callback seams when a cleaner shared production module can own the behavior, including old elaboration/checking stories that no longer drive production compilation
- Keep improving semantic quality of application/type errors, especially around implicit arguments, partial application, and unsolved constraints
- Keep tightening `with` desugaring/abstraction coverage so non-variable scrutinees, nested withs, and dependent return types stay protected by regressions
- Keep shrinking duplicated `Match` / clause-context logic across kernel, surface, compiler, proof-tree, and tactics
- Preserve useful editor/type-info output even when clause checking later fails
- Decide which remaining large implementation TODO should be next after the term/block cleanup settles: `bridge.ts`, `record.ts`, or tactic-workspace/editor gaps

## Recent Progress
- Kept the compiler architecture pass going and drove `src/compiler/compile.ts` down to 818 lines by extracting the live block compiler into `src/compiler/compile-block-processing.ts` and deleting the dead older `elabTT` / block-checking pipeline
- Split the shared compile vocabulary out of `src/compiler/compile.ts` into `src/compiler/compile-types.ts`, so helper modules no longer type-import from the monolithic top-level driver just to talk about parsed blocks, elaborated declarations, and compiled results
- Extracted impl registration into `src/compiler/compile-impl-annotations.ts` and incremental replay helpers into `src/compiler/compile-incremental-state.ts`, with focused tests for `@impl=nat` / `@natAdd` registration and block-contribution replay
- Added direct regressions in `compile-block-processing.test.ts`, `compile-impl-annotations.test.ts`, and `compile-incremental-state.test.ts`, alongside the earlier term-declaration seam tests, so this refactor is pinned by unit tests rather than only end-to-end coverage
- Re-ran full `tsc`, build, and the heavy compiler/program suites after each extraction so the architecture pass stayed green instead of accumulating hidden regressions

## Up Next
- Get triangle numbers proof working end-to-end in WYSIWYG editor
- Keep splitting `src/compiler/compile.ts` so the remaining full/incremental compile loops stop mixing cache orchestration, block traversal, and policy decisions in one file
- Pull the next clean compiler seam out of the shared block-loop orchestration now that term declarations, block compilation, impl registration, and incremental replay are all split into dedicated modules
- Improve semantic quality of application/type errors, especially around implicit arguments and partial application
- Decide whether any remaining ill-typed abstraction cases need dedicated production rejection beyond the current checker/desugaring behavior
- Push the same DRY/hardening pass into the remaining generic kernel/solver walkers that still special-case `Match` or clause contexts
- Choose the next large implementation TODO to burn down: `bridge.ts` proof terms, `record.ts` checking, or editor-side tactic workspace gaps
- Keep trimming dormant UI/editor-specific code that no longer serves the text editor flow
- Add more semantic dependency edges to the incremental checker beyond token-level references
- Unify `cases` / `induction` case-goal computation between tactics and proof-tree replay
- Prove `limit_pull_scalar`: `c * lim f = lim (c * f)`
- Case-of expressions and nested casing / refinement
- Tactic proof term validation (Match case in `checkType`)

## Open Questions
- Should we build atop Lean instead of/alongside the custom TT engine? (side-branch exploration planned)
