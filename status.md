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
Building out the proof tree editor UI and tactic engine to support the triangle numbers proof. Iterating on three parallel tracks:
- The TT language (Agda-style nested pattern refinement)
- The tactic engine
- The WYSIWYG LaTeX editor that builds terms/tactics

## Recent Progress
- Eta conversion in definitional equality (f = \x => f x) with meta solver integration
- Proof tree editor with immutable state, undo/redo, hover-reveal delete buttons
- Real TacticEngine integration for goal computation
- Draggable split pane UI, dual math editor (type + proof)
- Registry-aware command system for structured editing
- `lim` projection operator for real analysis

## Up Next
- Get triangle numbers proof working end-to-end in WYSIWYG editor
- Prove `limit_pull_scalar`: `c * lim f = lim (c * f)`
- Infix operator syntax (user-defined operators with precedence)
- Case-of expressions and nested casing
- Tactic proof term validation (Match case in `checkType`)

## Open Questions
- Should we build atop Lean instead of/alongside the custom TT engine? (side-branch exploration planned)
