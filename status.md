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
- Keep decomposing `TextEditorPage` now that it is the only live top-level UI, starting with pure helpers for preset selection, declaration edits, cursor queries, and source-range mapping
- Keep peeling compile-result-to-editor diagnostics out of `TextEditorPage` so marker generation, hole warnings, and other compiler-derived view state stay testable outside Monaco
- Keep extracting Monaco-facing semantic-token and inlay-hint transforms so editor providers consume shared data helpers instead of open-coding compiler-derived view state
- Keep coalescing compiler-derived editor analysis behind pure helpers so `TextEditorPage` orchestrates editor state instead of deriving declarations, token streams, holes, and cursor queries inline
- Keep moving URL/preset/WYSIWYG route-state transitions behind pure helpers so live editor navigation behavior is tested outside React event handlers
- Keep splitting `TextEditorPage` presentation into dedicated subcomponents so compile results, type-info, and Monaco wiring stop sharing one giant file
- Keep shrinking the remaining live editor shell now that compile/debounce/provider-sync orchestration, header controls, type info, and results rendering are all split out behind tested helpers/components
- Keep splitting the remaining results presentation so declaration-card rendering, pretty-print controls, and block-level error wrappers each own one concern
- Keep converting stale compiler/proof-tree TODOs into real regressions or concrete fixes
- Preserve useful editor/type-info output even when clause checking later fails
- Keep tightening `with` desugaring/abstraction coverage so helper tests become real end-to-end regressions
- Keep shrinking duplicated `Match`/clause helper logic across kernel, surface, compiler, and tactics
- Keep simplifying structured-editor command plumbing so shared metadata/command paths replace editor-specific duplicates
- Keep turning proof-workspace keyboard navigation from placeholder wiring into real selected-item actions
- Keep replacing placeholder proof-workspace editor actions with the same tested transform path the main expression editor uses
- Keep collapsing proof-workspace legacy let/claim data so equality-mode and ordinary let editing share one state model
- Keep trimming dead UI/editor surfaces now that the text editor is the only live top-level page
- Decide which remaining large implementation TODO should be next: `bridge.ts`, `record.ts`, or tactic-workspace/editor gaps

## Recent Progress
- Split `TextEditorResultsPanel` further by extracting declaration-card rendering into `src/components/TextEditorDeclarationCard.tsx`, the pretty-print toggles into `src/components/TextEditorRenderOptions.tsx`, and block-level comment/parse/name-error rendering into `src/components/TextEditorCompiledBlock.tsx`, with focused regressions for constructor/projection rendering, warning-only status, control labels, and block-wrapper edge cases
- Extracted the top-level text editor header into `src/components/TextEditorHeader.tsx`, with focused rendering regressions for WYSIWYG toggle labels and preset-menu visibility, so `TextEditorPage` no longer owns the title/control/menu block inline
- Split compile-results logic further into `src/components/TextEditorCaseTree.tsx` plus the pure helper layer in `src/components/textEditorResultsModel.ts`, with focused regressions for case-tree rendering, declaration status summaries, and param/index extraction
- Extracted semantic-token delta encoding and wildcard inlay-hint shaping into `src/components/textEditorSemanticData.ts`, with focused regression coverage, so Monaco provider callbacks no longer open-code compiler token sorting/clamping logic
- Extracted shared Monaco setup into `src/components/textEditorMonaco.ts`, including theme/language/provider registration, unicode abbreviation rewriting, and cursor-selection normalization, with focused regressions in `textEditorMonaco.test.ts`
- Extracted a shared compiler-derived analysis layer into `src/components/textEditorAnalysis.ts`, so `TextEditorPage` now asks one tested helper for declaration lists, WYSIWYG sources, wildcard hints, semantic tokens, hole locations, and cursor type-info instead of scattering that derivation across inline `useMemo`s
- Extracted the cursor/type-info presentation pane into `src/components/TextEditorTypeInfoPanel.tsx`, with focused rendering regressions for term info, expected types, context entries, and tactic goals, so `TextEditorPage` no longer owns that large conditional render block
- Extracted preset/editor URL-state transitions into `src/components/textEditorUrlState.ts`, with focused regressions covering preset slugs, editor/symbol query params, and WYSIWYG toggle behavior, so `TextEditorPage` no longer open-codes those search-param mutations
- Extracted the compile-results subtree into `src/components/TextEditorResultsPanel.tsx`, including declaration cards, totality/case-tree rendering, and named-arg display toggles, with focused rendering regressions so `TextEditorPage` no longer owns that large results presentation block
- Extracted the editor-compiler orchestration into `src/components/useTextEditorCompiler.ts` plus tested helpers in `src/components/textEditorCompiler.ts`, removing inline incremental compile timing, Monaco marker application, and provider-ref synchronization from `TextEditorPage`
- Extracted pure compile-result marker generation into `src/components/textEditorDiagnostics.ts`, including precise type-error / with-clause source mapping and hole warnings, with focused regressions in `textEditorDiagnostics.test.ts`
- Extracted the first pure `TextEditorPage` model layer into `src/components/textEditorModel.ts`, moving preset slugging, declaration collection/rename, cursor type-info lookup, and error-path-to-source-range mapping out of the React component, with focused regressions in `textEditorModel.test.ts`
- Deleted the unrouted proof/inductive/record editor subtree entirely, including the navigation context/footer, proof-workspace helpers, named-item editor helpers, and their tests, after collapsing the app shell to the text editor
- Collapsed the top-level app shell to the text editor: `/text-editor` and all fallback routes now mount `TextEditorPage`, and the old proof/inductive/record route switchboard is gone with a routing regression in `App.test.tsx`
- Removed the dead legacy let/claim fields from the structured proof editor path, switched rewrite history over to `equalityChain`, and simplified `createLetElement` to the shape the current UI actually uses
- Trimmed dead proof-workspace migration scaffolding in `EnhancedProofWorkspace`: removed the unused combined TT-proof cache, dead scroll ref, and debug-only churn that no longer fed the UI
- Replaced the proof-workspace let-value rule `alert(...)` stub with the real focused-expression rewrite path, so active let editors now update their expression, TT let value, and proof-history metadata instead of dead-ending
- Extracted shared proof-workspace transform helpers and added regressions covering nested focused rewrites, propagated assumptions, and let-proof-history updates
- Removed the `TTViewer` lambda-binder fallback and added rendering regressions so TT inspection no longer shows `TODO-Binder-BLamTT` for ordinary lambda terms
- Removed dead proof-workspace command plumbing: hypothesis/let keyboard actions now use real selected-item metadata and real workspace callbacks instead of no-op handlers
- Added shared proof-workspace selection metadata helpers plus focused regressions for command-tree behavior in `navigationCommands.test.ts` and `proofWorkspaceSelection.test.ts`
- Let-binding rows now publish selection metadata and support keyboard selection, so let edit/delete commands are no longer permanently gated off

## Up Next
- Get triangle numbers proof working end-to-end in WYSIWYG editor
- Keep splitting `TextEditorPage` so Monaco/editor lifecycle glue stays in React while the remaining header/panel wiring and composition-level state continue moving into smaller components/hooks
- Keep shrinking `TextEditorResultsPanel` so declaration cards and remaining composition-level wiring stay separate as the block wrappers and pretty-print controls settle into their own components
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
