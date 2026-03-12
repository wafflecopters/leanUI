/**
 * Simp Meta-Tactic: Repeatedly apply rewrite lemmas and unfold definitions
 *
 * Unlike standard tactics, simp returns a list of individual steps it applied,
 * so the UI can show them as an expandable block.
 *
 * Algorithm:
 * 1. Loop with `changed` flag
 * 2. For each lemma: try rewrite (forward only), try unfold
 * 3. On first success: record step, update engine, restart inner loop
 * 4. When no lemma succeeds in a full pass, stop
 * 5. Return final engine + ordered list of steps
 */

import { MetaVar } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { RewriteTactic } from './rewrite-tactic';
import { UnfoldTactic } from './unfold-tactic';
import { ProofNode, mkRewrite, mkUnfold } from '../proof-tree/proof-tree';

export interface SimpStep {
  readonly type: 'rewrite' | 'unfold';
  readonly name: string;
  readonly reverse: boolean;
}

export interface SimpResult {
  readonly success: boolean;
  readonly engine: TacticEngine;
  readonly steps: SimpStep[];
  /** Proof tree nodes corresponding to the steps. */
  readonly proofNodes: ProofNode[];
  readonly error?: string;
}

/** Maximum number of simp iterations to prevent runaway simplification.
 * Commutativity/associativity lemmas can cause combinatorial explosion
 * (each rearrangement is a distinct goal), so keep this low. */
const MAX_SIMP_STEPS = 10;

/**
 * Resolve a lemma name to a TTKTerm for use with RewriteTactic.
 * Looks up in context first (like IH), then tries as a constant.
 */
function resolveName(name: string, goal: MetaVar): import('../compiler/kernel').TTKTerm {
  // Search context for matching name
  for (let i = goal.ctx.length - 1; i >= 0; i--) {
    if (goal.ctx[i].name === name) {
      return { tag: 'Var', index: goal.ctx.length - 1 - i };
    }
  }
  // Otherwise treat as a global constant
  return { tag: 'Const', name };
}

/**
 * Run the simp meta-tactic: repeatedly apply rewrites/unfolds from the given lemma list.
 */
export function runSimp(
  engine: TacticEngine,
  lemmas: readonly string[],
): SimpResult {
  if (lemmas.length === 0) {
    return { success: false, engine, steps: [], proofNodes: [], error: 'simp: no lemmas provided' };
  }

  let currentEngine = engine;
  const steps: SimpStep[] = [];
  // Track seen goal types to detect cycles (e.g. commutativity: mul a b → mul b a → ...)
  const seenGoals = new Set<string>();

  // Record initial goal
  const initGoal = engine.getFocusedGoal();
  if (initGoal) seenGoals.add(JSON.stringify(initGoal.type));

  for (let iteration = 0; iteration < MAX_SIMP_STEPS; iteration++) {
    let changed = false;

    for (const lemma of lemmas) {
      const goalId = currentEngine.getFocusedGoalId();
      const goal = currentEngine.getFocusedGoal();
      if (!goalId || !goal) break;

      // Try rewrite (left-to-right only — reverse rewrites risk infinite loops
      // since e.g. `n → plus n Zero → n → ...`).
      const rwTerm = resolveName(lemma, goal);
      const rwResult = new RewriteTactic(rwTerm, { reverse: false }).apply(currentEngine, goal, goalId);
      if (rwResult.success) {
        // Check for cycles: if the new goal was already seen, skip this rewrite
        const newGoal = rwResult.newEngine.getFocusedGoal();
        const newGoalKey = newGoal ? JSON.stringify(newGoal.type) : null;
        if (newGoalKey && seenGoals.has(newGoalKey)) {
          continue; // This rewrite leads back to a previously seen goal
        }
        steps.push({ type: 'rewrite', name: lemma, reverse: false });
        currentEngine = rwResult.newEngine;
        if (newGoalKey) seenGoals.add(newGoalKey);
        changed = true;
        break; // Restart inner loop
      }

      // Try unfold
      const unfoldResult = new UnfoldTactic([lemma]).apply(currentEngine, goal, goalId);
      if (unfoldResult.success) {
        const newGoal = unfoldResult.newEngine.getFocusedGoal();
        const newGoalKey = newGoal ? JSON.stringify(newGoal.type) : null;
        if (newGoalKey && seenGoals.has(newGoalKey)) {
          continue;
        }
        steps.push({ type: 'unfold', name: lemma, reverse: false });
        currentEngine = unfoldResult.newEngine;
        if (newGoalKey) seenGoals.add(newGoalKey);
        changed = true;
        break;
      }
    }

    if (!changed) break;
  }

  if (steps.length === 0) {
    return {
      success: false,
      engine,
      steps: [],
      proofNodes: [],
      error: `simp: no applicable lemma found among [${lemmas.join(', ')}]`,
    };
  }

  // Build proof tree nodes (dummy holes as children — they'll be replaced during tree construction)
  const proofNodes: ProofNode[] = steps.map(step => {
    if (step.type === 'rewrite') {
      // mkRewrite needs a child; use a temporary exact node (won't be used)
      return mkRewrite(step.name, { tag: 'hole', id: -1 } as any, step.reverse);
    } else {
      return mkUnfold(step.name, { tag: 'hole', id: -1 } as any);
    }
  });

  return {
    success: true,
    engine: currentEngine,
    steps,
    proofNodes,
  };
}
