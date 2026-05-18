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
- Keep collapsing the remaining gap between text tactics, the structured tactic tree, and the WYSIWYG proof editor so all three share one proof-tree/tactic command core instead of duplicating dispatch logic
- Keep shrinking `src/compiler/compile.ts` into a thin driver over explicit subsystems; the live block compiler, impl annotation registration, and incremental-state replay are now split, and the next seam is the remaining top-level full/incremental loop orchestration
- Keep extracting pure compiler helpers with direct unit tests plus end-to-end regressions, especially around block compilation, incremental contribution replay, declaration assembly, and editor-facing compile data
- Keep deleting dead parallel compiler paths and temporary callback seams when a cleaner shared production module can own the behavior, including old elaboration/checking stories that no longer drive production compilation
- Keep improving semantic quality of application/type errors, especially around implicit arguments, partial application, and unsolved constraints
- Keep tightening `with` desugaring/abstraction coverage so non-variable scrutinees, nested withs, and dependent return types stay protected by regressions
- Keep shrinking duplicated `Match` / clause-context logic across kernel, surface, compiler, proof-tree, and tactics
- Preserve useful editor/type-info output even when clause checking later fails
- Decide which remaining large implementation TODO should be next after the term/block cleanup settles: `bridge.ts`, `record.ts`, or tactic-workspace/editor gaps

## Recent Progress
- Extracted the remaining duplicated term-builder slot fill/clear rebuild logic into shared helpers in `src/proof-tree/term-builder.ts`, and switched both major `ProofTreeEditor` term-builder call sites to use that one pipeline instead of rebuilding slot state by hand in React. Added focused `term-builder.test.ts` coverage for fill/clear roundtrips and preserved source-expression tracking. Also fixed occurrence-targeted reverse rewrite on bare constant heads (`rewrite← mulOneRight` at occurrence 1) so the shared rewrite engine no longer misses non-`App` occurrences. Full verification green (`npx tsc --noEmit`, `npm test`: 200 files, 3141 passed, 4 skipped).
- Moved the remaining `have` rename/edit/hoist mutations out of the generic proof-tree core and into the shared tactic-edit action layer. `ProofTreeEditor` now calls shared pure helpers for `have` renames, expression edits, and term-builder hoists instead of hand-editing tree nodes directly. This deleted another chunk of bespoke proof-tree mutation code and fixed an order-dependent structured-editor regression by making the image-#32 replay test synchronous around proof-tree ID allocation. Full verification green (`npx tsc --noEmit`, `npm test`: 199 files, 3139 passed, 4 skipped).
- Turned the shared tactic-command bridge into actual code deletion: removed legacy direct proof-tree mutation helpers for source-shaped `intro`/`exact`/`apply`/`rewrite`/`unfold`/`fold` flows, migrated proof-tree/replay/suggestion tests onto the shared bridge, and removed the old `applyHave` path in favor of the same source-aligned `have` insertion used elsewhere. This is the first real “convergence dividend” instead of just adding adapters. Full verification green (`npx tsc --noEmit`, `npm test`: 199 files, 3136 passed, 4 skipped).
- Promoted `simp` into the shared text/structured tactic surface: source tactic blocks now support `simp` with explicit lemma names and bare `simp` using the registered `@simp` set, backed by the same `runSimp` engine path the structured editor already uses. The proof-tree bridge now preserves source-shaped `simp` nodes instead of only flattening them into rewrite/unfold steps. Added parser, tactic-conversion, proof-tree, replay, and `.tt` regressions. Full verification green (`npx tsc --noEmit`, `npm test`: 199 files, 3131 passed, 4 skipped).
- Parser: split prefix and infix operator profiles on shared symbols so `-` can be both binary subtraction (`sub`) and unary negation (`neg`) without one clobbering the other. `-<digit>` (no whitespace) now parses as a signed `RatLit`, routing through the elaborator's `@ofInt` path; `- x` parses as prefix `neg x`; `a - b` still parses as `sub a b`. Real-analysis preset declares `prefix 90 - := rneg`. Fixes "Type definition not found: sub" when users type `exact -1` in a `Carrier R` position (image #36). New regressions in parser tests and a structured-editor regression at the exact-tactic seam. Full verification green (`npm test`: 199 files, 3123 passed, 4 skipped).
- Rewrite tactic: alias↔projection δ-bridge so lemmas keyed under projection heads (`CompleteOrderedField.addComm`) fire on alias-headed subterms (`radd 2 (-1)`). `tryMatchPattern` and `substituteImpl` now one-step δ-unfold trivial aliases (single-clause Match with PVar/PWild patterns) to bridge the gap, without descending into the unfolded head's Match body (which would break structural matching). Two new tests cover full-arity and partial-application aliases.
- Converged another real tactic/editor seam: source tactics now support `have h : T by ...`, the proof-tree bridge serializes interactive `have` subproofs back into shared `TacticCommand`s, and the parser / tactic engine / proof-tree replay all agree on that shape. Added parser, tactic-conversion, proof-tree, goal-computation, and `.tt` regressions for both inline and multiline `have by` forms.
- Added a shared proof-tree tactic command bridge: structured editor actions can now build/consume source-aligned `TacticCommand`s for overlapping tactics, proof trees can serialize back into command sequences, and `apply`/focused-subgoal structure roundtrips through one core path. Both structured-editor views now use the same pure tactic-editing helpers instead of separate local dispatch trees. Pinned with new proof-tree bridge/action tests plus the full suite (`npx tsc --noEmit`, `npm test`: 199 files, 3107 passed, 4 skipped).
- Fixed the apply tactic's implicit-arg inference for record projections (post-hoc positional matching) — unblocks one-click closure of `(R : Real) -> rle 0 1` / `rlt 0 1` via `simp; apply CompleteOrderedField.zeroLeOne` (or `zeroLtOne`). Added `simp-then-apply-def-X` suggestion path + soundness check (`isCleanApply`) so bogus applies that leave dangling metas don't surface. Gated the simp scanner's "try-anywhere" inner pass to whole-goal selections only — fixes the bug where clicking an inner subterm surfaced rewrites of unrelated parent subterms. Relaxed simp's strict-shorter filter to allow same-length-but-different rewrites (e.g. `addComm`).
- Eliminated all 3 Rat→Real homomorphism postulates (addRealOfRat, mulRealOfRat, subRealOfRat). Decimal milestone (`185.6 - 85.7 = 99.9`) now compiles with zero postulates.

## Up Next
- Get triangle numbers proof working end-to-end in WYSIWYG editor
- Push the same shared tactic-command bridge deeper so hypothesis-level/projection actions, remaining hoist/term-builder flows, and proof-tree-only nodes stop hand-encoding behavior that text tactics already know how to express
- Keep cashing out convergence as deletions: push the same shared tactic-edit layer into the remaining proof-tree-only convenience actions and hypothesis/projection flows that still bypass the text-tactic/command bridge
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
