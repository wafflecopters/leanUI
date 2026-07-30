# Structured Proof Editor — Overview & Design

## Vision

A tactic-style proof editor that **feels like writing math**, not code. Each proof is a tree of "steps" that correspond to tactics internally but render as natural mathematical prose. The cursor position determines what goal/context information is shown, similar to Coq/Lean's goal view but rendered with our math renderer.

## Example: What It Should Look Like

For `plusZeroRight : (n : Nat) -> Equal (plus n Zero) n`:

```
Given n ∈ ℕ,                          ← intros
  induct on n:                         ← induction
    Case n = 0:                        ← base case
      ⊢ 0 + 0 = 0                     ← goal (auto-rendered)
      by refl                          ← exact/close
    Case n = k':                       ← inductive step
      IH: k + 0 = k                   ← hypothesis (auto-shown)
      ⊢ k' + 0 = k'                   ← goal
      by congSucc(IH)                  ← exact
```

For `leqTrans : {a b c : Nat} -> Leq a b -> Leq b c -> Leq a c`:

```
Given a ≤ b and b ≤ c,                ← intros (with rendered hypotheses)
  cases on a ≤ b:                      ← case split
    Case LeqZero:                      ← constructor case
      ⊢ 0 ≤ c
      by LeqZero                       ← exact
    Case LeqSucc(p):                   ← constructor case (binding p)
      cases on b ≤ c:                  ← nested case split
        Case LeqSucc(q):
          ⊢ Succ(a') ≤ Succ(c')
          by LeqSucc(leqTrans(p, q))   ← recursive call
```

## Architecture

### Proof Tree

A proof is a **tree of tactic nodes**. Each node:
- Has a **tactic** (intros, induction, cases, exact, apply, rewrite, ...)
- Transforms one **goal** into zero or more **subgoals**
- Has **children** — one per subgoal produced
- Renders as **natural math prose** in the visual editor

```typescript
interface ProofNode {
  tactic: TacticKind;           // What this step does
  args: TacticArgs;             // Parameters (names, scrutinee, term, ...)
  goalBefore: GoalState;        // What we're trying to prove
  goalsAfter: GoalState[];      // Subgoals produced
  children: ProofNode[];        // Proofs of each subgoal
}
```

### Tactic Vocabulary (Math-First Naming)

| Internal Tactic | Math Rendering | Effect |
|-----------------|----------------|--------|
| `intros` | "Given n ∈ ℕ, f : ℕ → ℕ" | Move Pi-binders into hypotheses |
| `induction n` | "induct on n:" | Split into base + step cases |
| `cases x` | "cases on x:" | Pattern match, no IH |
| `exact e` | "by e" or just the expr | Close goal with exact proof term |
| `apply f` | "by f, it suffices to show..." | Reduce goal to f's argument types |
| `rewrite h` | "rewriting by h" | Replace LHS with RHS using equality |
| `constructor` | "we construct..." | Apply a data constructor |
| `have h : P` | "claim: P" | Introduce intermediate lemma |

### Rendering Strategy

Each node renders differently based on its tactic:

**Intros**: "Given {names} {∈ or :} {type}, ..." with same ∈-vs-: logic as type signatures (∈ for simple types, : for function types). Anonymous hypotheses render as "Suppose {type}".

**Induction/Cases**: "induct on {name}:" or "cases on {expr}:" followed by indented case blocks. Each case shows "Case {pattern}:" with the case's hypotheses (including IH for induction).

**Exact**: "by {proof-expr}" — the proof expression rendered using our math renderer and syntax registry.

**Apply**: "by {fn}, it suffices to show:" followed by the remaining subgoals.

**Rewrite**: "rewriting by {eq-name}," then continue with modified goal.

### Goal & Context Display

Wherever the cursor sits in the proof tree, we show:

1. **Current goal**: `⊢ target-type` rendered with math notation
2. **Hypotheses in scope**: each `name : type` rendered with math notation
3. **Available lemmas**: filtered by relevance (types that mention goal components)

This info panel uses the same KaTeX renderer as the math editor. The goal view updates live as the cursor moves between proof nodes.

### Cursor & Interaction Model

The proof tree is navigated like an outline:
- **Up/Down arrows**: move between sibling steps
- **Left/Right or Tab**: move between parent/child (or between editable fields within a step)
- **Enter on a goal**: open a tactic chooser (or start typing)
- **Escape**: go up to parent node

Each "leaf" of the proof tree is either:
- A **completed** exact term (goal closed)
- An **open hole** (unsolved goal — shown with `⊢` goal display, awaiting user input)

### Integration with Existing Infrastructure

**Already built:**
- `ProofState` / `GoalState` — tracks goals, hypotheses, solved metas
- `TacticExpr` — intro, intros, exact, apply, assumption, cases
- `applyTacticToState()` — executes a tactic, returns new proof state
- `TacticInfoTree` — records tactic applications with before/after goals
- `getTypeAtCursor()` — returns goal states when cursor is in tactic block
- `TypeInfoMap` — type-at-cursor for sub-expressions
- Math renderer (KaTeX + syntax registry) — renders terms as visual math
- `ttermToMathNodes` / `surfaceTypeToMathRow` — reverse conversion for display

**Needs building:**
- Proof tree UI component (renders tree of tactic nodes as math prose)
- Goal panel component (renders current goal + hypotheses)
- Tactic input system (command palette or inline editing for choosing/configuring tactics)
- Induction tactic (exists as `cases` but needs induction hypothesis generation)
- `have`/intermediate lemma tactic
- Proof tree ↔ TTK term serialization (save/load proofs)

## Open Design Questions

### 1. How does "intro" decide its rendering?

When the user does `intros`, the system moves Pi-binders into hypotheses. The rendering needs to decide:
- Group same-type binders: "Given n, m ∈ ℕ" vs separate "Given n ∈ ℕ and m ∈ ℕ"
- Anonymous hypotheses (proofs): "Suppose a ≤ b" vs "Given h : a ≤ b"
- Use ∈ vs : based on domain type (simple vs function type)

This can reuse the same logic from `surfaceTypeToMathRow`.

### 2. How does the proof tree map to a TTK term?

The proof tree is the **editing representation**. The final TTK term is extracted by:
- `intros [n, f]` → `Lambda(Nat, Lambda(Nat→Nat, body))`
- `induction n` → `Match(n, [case0, caseSucc])`
- `exact e` → `e` (the term itself)
- `apply f` → `App(f, ?subgoal1, ?subgoal2, ...)`

This is what `ProofState.term` already tracks — a TTK term with `Meta` nodes for unsolved goals.

### 3. How do we handle partially complete proofs?

Open goals appear as `Meta` nodes in the TTK term. In the UI, they render as editable holes. The user can:
- Navigate to any open hole
- Apply a tactic to make progress
- Save/resume with holes still open
- Get error markers on unresolved holes when they try to "check" the proof

### 4. What about the proof expression editor (the "by ..." part)?

When a goal is closed with `exact`, the user needs to write a proof term. This could be:
- A simple reference: "by refl" or "by IH"
- A function application: "by congSucc(IH)"
- A complex expression using the full math editor

The "by" field could be a MathEditor instance — same as the current proof editor but scoped to the current goal's context. The syntax registry + type inference would help autocomplete.

## Implementation Phases

### Phase 1: Proof Tree Display (Read-Only)
- Render an existing proof term as a proof tree (reverse-engineer from TTK term)
- Show goals at each node
- Cursor navigation through the tree
- Goal panel showing hypotheses + target at cursor position

### Phase 2: Basic Tactic Interaction
- `intros` — move binders to hypotheses
- `exact` — close goal with a term (mini math editor)
- `cases` / `induction` — split into sub-cases
- Live goal updates as tactics are applied

### Phase 3: Rich Proof Editing
- `apply`, `rewrite`, `have` tactics
- Autocomplete for hypotheses and lemmas
- Proof search / `assumption` tactic
- Undo/redo on the proof tree

### Phase 4: Polish
- Beautiful rendering with proper math typography
- Proof state diffing (highlight what changed after each tactic)
- Export to text-mode proof (for .tt files)
- Import from text-mode proof (parse existing proofs into tree)

## Current Status

- [x] Tactic infrastructure (ProofState, GoalState, TacticExpr, apply-tactic)
- [x] Type-at-cursor with goal state support
- [x] Math renderer with syntax registry
- [x] TTerm → MathNode reverse conversion (for pre-filling editors)
- [x] DualMathEditor with type + proof panes
- [ ] Proof tree UI component
- [ ] Goal panel component
- [ ] Tactic input / command system for proof mode
- [ ] Induction tactic
- [ ] Proof tree ↔ TTK term round-trip
