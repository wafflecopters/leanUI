# Proof Rendering Robustness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Fix all proof rendering issues so that compiled `by`-defined proofs show proper intermediate goals, rewrite equations, and math-rendered expressions in the prose view.

**Architecture:** Three independent fixes: (1) wire proof tree generation during compilation so the UI has a tree to render from, (2) fix the `radd(0)` rendering by ensuring carrier args are handled in alias folding, (3) add carrier-suppressed rendering for common COF projections shown in rewrite equations.

**Tech Stack:** TypeScript, Vitest, React (read-only for rendering changes)

---

## Background

### The Pipeline
```
Source → Parser → TacticCommands → TacticSession (trace) → Proof Tree → Goal Computation → Prose Items → UI
```

### Current State

1. **Compiled `by` definitions compute `tacticTrace` but not `proofTree`**: The compiler runs `TacticSession.applyCommands()` and stores the trace, but never calls `tacticCommandsToProofTree()`. The UI rebuilds the tree from `surfaceValue.tactics` — but only when `surfaceValue.tag === 'TacticBlock'`. Some declarations (like `subCancel`) have their surfaceValue as a TacticBlock with tactics, but the proof tree may still be empty when the tactic syntax doesn't match what `tactic-to-tree.ts` expects.

2. **`radd(0) = x` bug**: After rewrite chain produces a goal like `radd(R, x, rzero(R)) = x`, the rendering may show `radd(0) = x` because: (a) `foldAliases` may not fold correctly if the term structure after rewriting doesn't match the alias pattern, or (b) the intermediate goal is from a walkthrough that crashed partway.

3. **Rewrite equations show raw COF projections**: `(CompleteOrderedField.addAssoc (field R) x c (rneg c))` instead of rendered math like `(x + c) + (-c) = x + (c + (-c))`.

### Key Files
| File | Role |
|------|------|
| `src/compiler/compile.ts` | Compilation, where proofTree should be generated |
| `src/proof-tree/tactic-to-tree.ts` | `tacticCommandsToProofTree` — builds ProofNode from TacticCommand[] |
| `src/proof-tree/proof-tree.ts` | ProofNode types and tree traversals |
| `src/components/WYSIWYGPanel.tsx` | UI initialization of proof tree histories |
| `src/proof-tree/goal-computation.ts` | Goal/equation rendering, `renderGoalLatex`, `renderUnifiedEquationLatex` |
| `src/proof-tree/proof-prose.ts` | Prose item generation from proof tree + goal map |
| `src/math-editor/tt-to-math.ts` | TTerm → MathNode rendering, `CARRIER_CONST_SYMBOLS`, `buildCaptureMap` |
| `src/tactics/tactic-session.ts` | `TacticSession`, trace generation, `applyRewriteChain` |

---

### Task 1: Store proofTree on CompiledDeclaration

The compiler already computes `tacticTrace` by replaying tactics. At the same time, it should build the `proofTree` from the parsed tactic commands.

**Files:**
- Modify: `src/compiler/compile.ts:211` (add field to CompiledDeclaration)
- Modify: `src/compiler/compile.ts:3346-3356` (compute proofTree alongside tacticTrace)
- Test: `src/proof-tree/goal-computation.test.ts` (verify proofTree exists)

- [ ] **Step 1: Write failing test**

In `src/proof-tree/goal-computation.test.ts`, add:

```typescript
test('compiled tactic declaration has proofTree', () => {
  const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

addZero : (n : Nat) -> Equal (add n Zero) n := by
  intro n
  exact refl
`;
  // Need a simpler test — just check that compileTTFromText produces proofTree
  const result = compileTTFromText(source);
  const decl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'addZero');
  expect(decl).toBeDefined();
  expect(decl!.checkSuccess).toBe(true);
  // This is the new assertion — proofTree should exist for tactic-mode definitions
  expect(decl!.proofTree).toBeDefined();
  expect(decl!.proofTree!.tag).toBe('intros');
});
```

- [ ] **Step 2: Run test to verify it fails**

Run: `npx vitest run src/proof-tree/goal-computation.test.ts -t "compiled tactic declaration has proofTree"`
Expected: FAIL — `proofTree` is undefined

- [ ] **Step 3: Add `proofTree` field to CompiledDeclaration**

In `src/compiler/compile.ts`, after line 211 (`tacticTrace`), add:

```typescript
  // Proof tree built from parsed tactic commands (for proof tree rendering)
  proofTree?: import('../proof-tree/proof-tree').ProofNode;
```

- [ ] **Step 4: Import `tacticCommandsToProofTree` in compile.ts**

At the top of `src/compiler/compile.ts`, add:

```typescript
import { tacticCommandsToProofTree } from '../proof-tree/tactic-to-tree';
```

- [ ] **Step 5: Compute proofTree in `createCompiledDeclaration`**

In `src/compiler/compile.ts`, in the `createCompiledDeclaration` function, modify the tacticTrace IIFE (lines 3346-3356) to also compute proofTree. Replace:

```typescript
    tacticTrace: (() => {
      const sv = (decl.originalSurfaceValue ?? decl.value) as any;
      if (!checkSuccess || !kernelType || !sv || sv.tag !== 'TacticBlock') return undefined;
      try {
        const session = TacticSession.create(kernelType, definitions!);
        const final = session.applyCommands(sv.tactics);
        return final.trace.length > 0 ? [...final.trace] : undefined;
      } catch {
        return undefined;
      }
    })(),
```

With:

```typescript
    ...(() => {
      const sv = (decl.originalSurfaceValue ?? decl.value) as any;
      if (!checkSuccess || !kernelType || !sv || sv.tag !== 'TacticBlock') return { tacticTrace: undefined, proofTree: undefined };
      let tacticTrace: import('../tactics/tactic-session').TacticStepTrace[] | undefined;
      let proofTree: import('../proof-tree/proof-tree').ProofNode | undefined;
      try {
        const session = TacticSession.create(kernelType, definitions!);
        const final = session.applyCommands(sv.tactics);
        tacticTrace = final.trace.length > 0 ? [...final.trace] : undefined;
      } catch { /* ignore */ }
      try {
        proofTree = tacticCommandsToProofTree(sv.tactics);
      } catch { /* ignore */ }
      return { tacticTrace, proofTree };
    })(),
```

Note: this uses spread (`...`) so both `tacticTrace` and `proofTree` end up as fields on the return object. Adjust the surrounding object literal accordingly — you may need to destructure before the return object.

- [ ] **Step 6: Run test to verify it passes**

Run: `npx vitest run src/proof-tree/goal-computation.test.ts -t "compiled tactic declaration has proofTree"`
Expected: PASS

- [ ] **Step 7: Run full build and tests**

Run: `npx tsc --noEmit && npm test`
Expected: All pass

- [ ] **Step 8: Commit**

```bash
git add src/compiler/compile.ts src/proof-tree/goal-computation.test.ts
git commit -m "feat: store proofTree on CompiledDeclaration from tactic commands"
```

---

### Task 2: UI uses compiled proofTree for initial state

When the UI initializes proof tree histories, it should prefer the pre-built `proofTree` from compilation over rebuilding from tactic commands.

**Files:**
- Modify: `src/components/WYSIWYGPanel.tsx:158-171`

- [ ] **Step 1: Update proof history initialization**

In `src/components/WYSIWYGPanel.tsx`, modify the `proofHistoriesMap` initialization (lines 158-171) to check for compiled proofTree first:

```typescript
const [proofHistoriesMap, setProofHistoriesMap] = useState<Map<string, ProofTreeHistory>>(() => {
  const map = new Map<string, ProofTreeHistory>();
  for (const decl of declarations) {
    if (!decl.name) continue;
    // Prefer compiled proofTree, fall back to rebuilding from tactic commands
    let root: ProofNode | undefined;
    if (decl.proofTree) {
      root = decl.proofTree;
    } else if (decl.surfaceValue?.tag === 'TacticBlock' && decl.surfaceValue.tactics.length > 0) {
      root = tacticCommandsToProofTree(decl.surfaceValue.tactics);
    }
    if (root) {
      const firstHole = findFirstHole(root);
      map.set(decl.name, createHistory({ root, cursor: { nodeId: firstHole?.id ?? root.id } }));
    } else {
      map.set(decl.name, createHistory(createInitialState()));
    }
  }
  return map;
});
```

- [ ] **Step 2: Import ProofNode type if not already imported**

Check that `ProofNode` is imported. It should be from `../proof-tree/proof-tree`.

- [ ] **Step 3: Run full build and tests**

Run: `npx tsc --noEmit && npm test`
Expected: All pass

- [ ] **Step 4: Commit**

```bash
git add src/components/WYSIWYGPanel.tsx
git commit -m "feat: UI prefers compiled proofTree over rebuilding from tactic commands"
```

---

### Task 3: Add carrier-suppressed rendering for common COF projections

Rewrite equations show `CompleteOrderedField.addAssoc (field R) x c (rneg c)` because these projection names aren't rendered through the math pipeline. Add them to the carrier-const or alias system.

**Files:**
- Modify: `src/math-editor/tt-to-math.ts` (add entries to CARRIER_CONST_SYMBOLS)
- Test: `src/math-editor/tt-to-math.test.ts` or inline test

- [ ] **Step 1: Identify COF projections that need rendering**

The common ones from the screenshot:
- `CompleteOrderedField.addAssoc` — should show as `(a + b) + c = a + (b + c)` (but this is a proof term, not a value — so it renders as-is in "by" justification)
- `CompleteOrderedField.negRight` — `a + (-a) = 0`
- `CompleteOrderedField.addZeroRight` — `a + 0 = a`
- `CompleteOrderedField.zero` — should render as `0` (already handled by `rzero` alias + foldAliases)
- `CompleteOrderedField.neg` — should render as `-` (already handled by `rneg` alias)
- `CompleteOrderedField.add` — should render as `+` (already handled by `radd` alias)

These projections appear in the "by" justification of rewrite steps. The current "by" display shows the full expression. Since we already render the equation LaTeX separately (`c + (-c) = 0`), the raw projection name in the justification is the issue.

The cleanest fix: the rewrite `equationLatex` (rendered through the math pipeline) should be the primary display, with just the lemma name as secondary. The raw COF expression shouldn't show.

- [ ] **Step 2: Verify rewrite prose rendering uses equationLatex**

Read `src/components/ProofTreeEditor.tsx`, the `case 'rewrite':` in ProseItemView. Check that it uses `kind.equationLatex` (the rendered equation) rather than `kind.name` (the raw expression).

If it currently shows `kind.name` as the primary content, change it to show `kind.equationLatex` primarily and `kind.name` as a fallback (just the lemma name extracted from it).

- [ ] **Step 3: Update rewrite rendering to prefer equationLatex**

In the rewrite prose rendering, ensure:
- When `equationLatex` exists: show "which is true, because [equationLatex]"
- When `equationLatex` is missing: show "which is true, because of [lemmaName]" (extracted from the raw name)

- [ ] **Step 4: Run full build and tests**

Run: `npx tsc --noEmit && npm test`
Expected: All pass

- [ ] **Step 5: Commit**

```bash
git add src/components/ProofTreeEditor.tsx
git commit -m "fix: rewrite prose prefers equationLatex over raw projection names"
```

---

### Task 4: Test rewrite chain rendering end-to-end

Write an integration test that compiles a proof with an `erw` chain, generates the goal map via `replayEntireTree`, and verifies that intermediate goals and equations are present.

**Files:**
- Test: `src/proof-tree/goal-computation.test.ts`

- [ ] **Step 1: Write the test**

```typescript
describe('rewrite chain rendering', () => {
  test('erw chain produces intermediate goals and equations', () => {
    // Use a minimal proof with erw chain
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

addZero : (n : Nat) -> Equal (add n Zero) n
addZero Zero = refl
addZero (Succ n) = cong Succ (addZero n)

-- A proof using erw chain
test : Equal (add (add Zero Zero) Zero) Zero := by
  erw (addZero (add Zero Zero)), (addZero Zero)
  exact refl
`;
    const result = compileTTFromText(source);
    const decl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'test');
    expect(decl).toBeDefined();
    expect(decl!.checkSuccess).toBe(true);
    expect(decl!.proofTree).toBeDefined();
    expect(decl!.tacticTrace).toBeDefined();

    const reg = createDefaultRegistry();
    const rev = buildReverseRegistry(reg);
    const goalMap = replayEntireTree(decl!.proofTree!, decl!.kernelType!, result.definitions, rev, decl!.tacticTrace);

    // Should have multiple entries with goalLatex
    const goalsWithLatex = Array.from(goalMap.values()).filter(g => g.goalLatex);
    expect(goalsWithLatex.length).toBeGreaterThanOrEqual(2);

    // At least one entry should have unifiedEquationLatex (from the erw)
    const withEquation = Array.from(goalMap.values()).filter(g => g.unifiedEquationLatex);
    expect(withEquation.length).toBeGreaterThanOrEqual(1);
  });
});
```

- [ ] **Step 2: Run the test**

Run: `npx vitest run src/proof-tree/goal-computation.test.ts -t "erw chain produces intermediate goals"`
Expected: PASS (once Task 1 is done)

- [ ] **Step 3: Run full suite**

Run: `npx tsc --noEmit && npm test`
Expected: All pass

- [ ] **Step 4: Commit**

```bash
git add src/proof-tree/goal-computation.test.ts
git commit -m "test: verify erw chain produces intermediate goals and equations"
```

---

### Task 5: Robustify goal computation against undefined nodes

The goal computation crashes when encountering undefined nodes (e.g., when a proof tree is incomplete or malformed). Add defensive checks.

**Files:**
- Modify: `src/proof-tree/goal-computation.ts` (walkTrace and walk functions)

- [ ] **Step 1: Add null checks in walkTrace**

In `replayEntireTreeFromTrace`, the `walkTrace` function at the top of its switch statement, add:

```typescript
function walkTrace(node: ProofNode | undefined, currentEngine: TacticEngine, caseLabelLatex?: string): void {
  if (!node) return;  // Defensive: handle undefined nodes gracefully
  // ... existing switch
}
```

Do the same for the `walk` function in `replayEntireTreeViaWalk`.

- [ ] **Step 2: Run full build and tests**

Run: `npx tsc --noEmit && npm test`
Expected: All pass

- [ ] **Step 3: Commit**

```bash
git add src/proof-tree/goal-computation.ts
git commit -m "fix: defensive null checks in goal computation tree walkers"
```

---

### Task 6: Final verification

- [ ] **Step 1: Run full build and test suite**

```bash
npx tsc --noEmit && npm test
```

- [ ] **Step 2: Manual verification**

Open the UI, navigate to `subCancel` (or any proof with `erw` chains). Verify:
1. The proof tree view (Tactics tab) shows all tactic steps
2. The proof prose view (Proof tab) shows intermediate goals between rewrite steps
3. Rewrite equations render as math (not raw COF projections)
4. No `radd(0)` rendering artifacts

- [ ] **Step 3: Commit any final fixes**

```bash
git add -A
git commit -m "fix: proof rendering robustness - final adjustments"
```
