# WYSIWYG Editor → Lean: Feature Inventory & Port Plan

This is the **definition of done** for porting the real structured WYSIWYG editor
(`WYSIWYGPanel` + `ProofTreeEditor` + `MathEditor` + `DualMathEditor`) onto the
Lean 4 backend. Do NOT rebuild simplified parallel components — reuse the real
ones; replace the engine beneath them.

## The architecture truth

The real components are **welded to TT data types**: `ProofTreeEditor` props are
`surfaceType: TTerm`, `kernelType: TTKTerm`, `definitions: DefinitionsMap`, and
internally it calls the TT goal engine (`computeTypedContext`, `replayEntireTree`,
`TacticEngine`). So "WYSIWYG on Lean" is **not** a producer swap — it requires
refactoring the seam so the components are parameterized over an abstract
goal/term representation, fed by Lean.

Reusable as-is (pure UI / data model): proof-tree state model (`proof-tree.ts`),
prose generation (`proof-prose.ts`), interactive-goal *interaction* state,
math editor (`input.ts`/`navigation.ts`/`render.ts`), undo/redo, syntax registry,
name rendering, all the view components' layout.

Must be Lean-backed (the seam): everything that computes proof *semantics* —
`computeTypedContext`, `replayEntireTree`, `replayToEngine`,
`computeApplySubgoalCount`, `generateCaseInfos`, and the `TacticEngine` + tactic
classes. These produce per-node `NodeGoalInfo` / `TypedProofContext` (mostly LaTeX
+ hypotheses) that the UI renders.

## Key seam types (the adapter boundary)

- `TypedProofContext { hypotheses, caseLabel?, goal (LaTeX), validation?, kernelGoal? }`
- `NodeGoalInfo { goalLatex, hypotheses, caseLabelLatex?, validation?, unifiedEquationLatex?, appliedArgsLatex?, tacticError?, proofExprLatex?, scrutineeLatex?, isValueType? }`
- `ProofNode` union: hole, intros, induction(cases), exact, unfold, fold, rewrite, apply, simp, have, suffices
- `ProofTreeEditor` props: `{history, onHistoryChange, surfaceType, kernelType, definitions, registry, inductiveMap, currentDeclName, tacticTrace}`

## The 61 features (grouped)

### Proof tree editing (tactics)
1. intros ("Given …") — names, grouped-by-type rendering
2. induction / cases — auto case labels from constructors, add/remove/collapse cases, param names
3. exact ("by EXPR") — validation ✓/✗, solved indicator
4. have — intermediate hyp, inline expr edit, nested proof subtree, term-builder
5. suffices — dual subtrees (byProof + child)
6. unfold — occurrence targeting, pre/post goal
7. fold — occurrence targeting
8. rewrite — bidirectional, occurrences, calc-chain rendering, incremental suggestions
9. apply — subgoal previews, multi-subgoal layout, compact inline mode, 0-subgoal close
10. simp — lemma list, collapsible step tree
11. hole — inline tactic buttons + manual entry

### Interactive goals
12. subterm click-to-select (GoalPath)
13. binder selection (induct-on suggestions)
14. hypothesis toggle (per-hyp action tray)
15. binder rename with live LaTeX preview (TeX input → unicode)

### Suggestions
16. suggestion system (intro/induction/unfold/rewrite/construct/refl/apply)
17. incremental rewrite scanning (progress spinner)
18. suggestion application (edit-before-apply, name normalization)

### Term builder
19. slots (empty/filled/error/implicit, type display)
20. slot filling (suggestions + math editor, type check)
21. slot hoisting (↑ to new have)
22. slot clearing

### Prose view
23. prose generation + dispatcher
24. intro prose (grouped, Oxford comma, clickable tokens)
25. exact prose (solved/error, qed ∎)
26. calc-style equational chains
27. apply prose (subgoal/compact)
28. induction header + case rendering
29. have prose (inline editors, remainder goal)
30. unfold/fold/rewrite prose (pre/post goals, occurrences)
31. simp prose (collapsible steps)
32. interactive goal display (clickable + suggestion pills)

### Math editor (pure — reuse verbatim)
33–46. structured ops (symbol/frac/sub/sup/delimiter/accent/bigop), command mode `\`,
text mode, navigation, backspace, type-inference display, KaTeX render+click-to-pos,
syntax registry integration

### Type signature editing
47. DualMathEditor + signature-parts inference

### Names
48. binder name LaTeX rendering

### Persistence
49. immutable undo/redo history
50. cursor navigation (up/down tree)

### Validation
51. goal validation (green/red)
52. tactic error indicators

### UI / misc
53. keyboard shortcuts
54. node deletion (Delete/Backspace)
55. hover delete (×)
56. split pane (resize)
57. tabs (tactics vs proof)
58. WYSIWYG panel: multi-declaration cards, editable name, expand/fullscreen, readonly inductive view
59. syntax reference panel
60. proof prefix display
61. placeholder text

## Round-trip mechanism (PROVEN at CLI)

Keystone built + tested: `src/lean/proofTreeToLean.ts` (ProofNode → Lean tactic
block + per-node source ranges) and `src/lean/leanGoalMapping.ts` (Lean InfoTree
goals by range → `Map<ProofNodeId, NodeGoalInfo>`, the drop-in for
`replayEntireTree`). `taggedToLatex` in codeWithInfos.ts renders Lean tagged
goals to the LaTeX strings the existing UI contract expects.

CLI round-trip confirmed: a printed `induction … with | zero | succ` block
elaborates with 0 errors and Lean reports a goal at every tactic line (with case
names), matching the printer's recorded ranges exactly.

GOTCHA found + to handle in the assembler: declaration signature binders
(`theorem t (a b : Nat) : …`) are ALREADY in scope, so the proof tree's leading
`intros` must NOT emit `intro a b` (Lean: "introN failed: no additional
binders"). The full-declaration assembler decides binder placement: leading
intros become signature binders OR the goal type is the un-introduced Pi and the
tactic block intros them — pick one consistently. Simplest: assemble as
`theorem <name> : <fullType> := by <block>` (no signature binders) so the tree's
intros are valid tactics; the type comes from the declaration's own tagged type.

## Port strategy (DI seam, not a rebuild)

Refactor `ProofTreeEditor` / `WYSIWYGPanel` to receive goal computation via an
injected provider interface (default = current TT impl, so the legacy page keeps
working), then supply a Lean-backed provider that produces `NodeGoalInfo` /
`TypedProofContext` from the InfoTree goal data. The proof tree ⟷ Lean tactic
source becomes the source of truth. Interactive tactic application is async
(server round-trip) — the sync `Tactic.apply` seam must become async-aware.
