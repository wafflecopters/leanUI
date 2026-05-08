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
- Keep shrinking duplicated `Match`/clause helper logic across kernel, surface, compiler, and tactics
- Keep simplifying structured-editor command plumbing so shared metadata/command paths replace editor-specific duplicates
- Keep turning proof-workspace keyboard navigation from placeholder wiring into real selected-item actions
- Keep replacing placeholder proof-workspace editor actions with the same tested transform path the main expression editor uses
- Decide which remaining large implementation TODO should be next: `bridge.ts`, `record.ts`, or tactic-workspace/editor gaps

## Recent Progress
- Replaced the proof-workspace let-value rule `alert(...)` stub with the real focused-expression rewrite path, so active let editors now update their expression, TT let value, and proof-history metadata instead of dead-ending
- Extracted shared proof-workspace transform helpers and added regressions covering nested focused rewrites, propagated assumptions, and let-proof-history updates
- Removed the `TTViewer` lambda-binder fallback and added rendering regressions so TT inspection no longer shows `TODO-Binder-BLamTT` for ordinary lambda terms
- Removed dead proof-workspace command plumbing: hypothesis/let keyboard actions now use real selected-item metadata and real workspace callbacks instead of no-op handlers
- Added shared proof-workspace selection metadata helpers plus focused regressions for command-tree behavior in `navigationCommands.test.ts` and `proofWorkspaceSelection.test.ts`
- Let-binding rows now publish selection metadata and support keyboard selection, so let edit/delete commands are no longer permanently gated off

## Up Next
- Get triangle numbers proof working end-to-end in WYSIWYG editor
- Improve semantic quality of application/type errors, especially around implicit arguments and partial application
- Decide whether any remaining ill-typed abstraction cases need dedicated production rejection beyond the current checker/desugaring behavior
- Push the same DRY/hardening pass into the remaining generic kernel/solver walkers that still special-case `Match` or clause contexts
- Choose the next large implementation TODO to burn down: `bridge.ts` proof terms, `record.ts` checking, or editor-side tactic workspace gaps
- Keep burning down editor-side TODOs and duplicate command plumbing in `EnhancedProofWorkspace`, especially let-value proof history / equality-mode leftovers and remaining display-only legacy state
- Add more semantic dependency edges to the incremental checker beyond token-level references
- Unify `cases` / `induction` case-goal computation between tactics and proof-tree replay
- Prove `limit_pull_scalar`: `c * lim f = lim (c * f)`
- Case-of expressions and nested casing / refinement
- Tactic proof term validation (Match case in `checkType`)

## Open Questions
- Should we build atop Lean instead of/alongside the custom TT engine? (side-branch exploration planned)
