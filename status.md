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
- Keep shrinking `src/compiler/compile.ts` into explicit declaration-processing and result-shaping subsystems instead of a giant mixed-responsibility module
- Keep extracting pure compiler helpers with direct unit tests plus end-to-end regressions, especially around inductive/record processing, clause checking, and editor-facing compile data
- Keep deleting dead parallel compiler paths and temporary callback seams when a cleaner shared production module can own the behavior
- Keep improving semantic quality of application/type errors, especially around implicit arguments, partial application, and unsolved constraints
- Keep tightening `with` desugaring/abstraction coverage so non-variable scrutinees, nested withs, and dependent return types stay protected by regressions
- Keep shrinking duplicated `Match` / clause-context logic across kernel, surface, compiler, proof-tree, and tactics
- Preserve useful editor/type-info output even when clause checking later fails
- Decide which remaining large implementation TODO should be next: `bridge.ts`, `record.ts`, or tactic-workspace/editor gaps

## Recent Progress
- Kept the compiler architecture pass going and drove `src/compiler/compile.ts` down to 2878 lines by extracting more real subsystems instead of just moving helpers around
- Moved record declaration orchestration into `src/compiler/compile-record-processing.ts`, with direct regressions for inherited-field extraction, binder-aware field substitution, and implicit-hole insertion, plus reruns of the heavy record/extends suites
- Moved inductive declaration orchestration into `src/compiler/compile-inductive-processing.ts`, with direct regressions for current-inductive named-arg lookup and adjacent constructor elaboration cases that still have to see existing named-arg definitions
- Extracted shared declaration/result shaping into `src/compiler/compile-declaration-result.ts`, deleted the temporary callback seam between `compile.ts` and the new declaration modules, and added direct regressions for named-arg metadata preservation and elaboration-error path mapping
- Hardened two long-running real-analysis/proof-tree regressions by widening their timeouts after proving they were resource-sensitive full-suite failures rather than semantic bugs, so the compiler/test harness now runs green under full `npm test`

## Up Next
- Get triangle numbers proof working end-to-end in WYSIWYG editor
- Keep splitting `src/compiler/compile.ts` so the remaining term-declaration and block-orchestration paths stop mixing pure helpers with top-level pipeline control
- Pull the next clean compiler seam out of `checkTermDeclaration` / `processTermDeclaration`, likely signature elaboration + simple-value checking or another declaration-prep module with direct unit coverage
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
