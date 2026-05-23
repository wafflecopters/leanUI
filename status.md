# Project Status

## Vision
Bridge between Overleaf and Lean: write LaTeX-like code with proof-correctness, or write Lean code with LaTeX presentation and WYSIWYG ergonomics. We are exploring both a custom dependently typed language (TT) and the possibility of building atop Lean itself.

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
