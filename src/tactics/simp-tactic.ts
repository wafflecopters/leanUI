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

import { MetaVar, DefinitionsMap } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { RewriteTactic } from './rewrite-tactic';
import { UnfoldTactic } from './unfold-tactic';
import { ProofNode, mkRewrite, mkUnfold } from '../proof-tree/proof-tree';
import { whnf } from '../compiler/whnf';
import { TTKTerm } from '../compiler/kernel';

/** Walks a term, whnf-reducing any App whose head is registered as
 *  @ratAdd/@ratMul/@ratSub or natAdd/natMul, then re-wrapping bare
 *  literal results in MkRat form so simp lemmas keyed on MkRat match.
 *  This is what makes mid-proof goals with un-reduced \`ratPlus 1 -1\`
 *  become \`realOfRat R (MkRat 0 1 _)\` which then matches \`realOfRatZero\`. */
function goalMightHaveRatOp(term: TTKTerm, ratOps: Map<string, 'add' | 'mul' | 'sub'>): boolean {
  if (term.tag === 'App') {
    let head: TTKTerm = term;
    while (head.tag === 'App') head = head.fn;
    if (head.tag === 'Const' && ratOps.has(head.name)) return true;
    return goalMightHaveRatOp(term.fn, ratOps) || goalMightHaveRatOp(term.arg, ratOps);
  }
  if (term.tag === 'Binder') return goalMightHaveRatOp(term.domain, ratOps) || goalMightHaveRatOp(term.body, ratOps);
  if (term.tag === 'Match') {
    if (goalMightHaveRatOp(term.scrutinee, ratOps)) return true;
    for (const c of term.clauses) if (goalMightHaveRatOp(c.rhs, ratOps)) return true;
  }
  return false;
}

function normalizeRatOps(term: TTKTerm, definitions: DefinitionsMap): TTKTerm {
  const liftLitToMkRat = (t: TTKTerm): TTKTerm => {
    if (t.tag !== 'NatLit' && t.tag !== 'RatLit') return t;
    const impls = definitions.ratImplByCtor;
    if (!impls) return t;
    let mkRatName: string | undefined;
    let intOfNat: string | undefined;
    let intNegSucc: string | undefined;
    for (const [name, impl] of impls) {
      if (impl.intOfNatCtor && impl.intNegSuccCtor) {
        mkRatName = name;
        intOfNat = impl.intOfNatCtor;
        intNegSucc = impl.intNegSuccCtor;
        break;
      }
    }
    if (!mkRatName || !intOfNat || !intNegSucc) return t;
    const num = t.tag === 'NatLit' ? t.value : t.num;
    const den = t.tag === 'NatLit' ? 1n : t.den;
    if (den <= 0n) return t;
    const intArg: TTKTerm = num >= 0n
      ? { tag: 'App', fn: { tag: 'Const', name: intOfNat }, arg: { tag: 'NatLit', value: num } }
      : { tag: 'App', fn: { tag: 'Const', name: intNegSucc }, arg: { tag: 'NatLit', value: -num - 1n } };
    const denArg: TTKTerm = { tag: 'NatLit', value: den };
    const proof: TTKTerm = { tag: 'App', fn: { tag: 'Const', name: 'IsSucc' }, arg: { tag: 'NatLit', value: den - 1n } };
    return {
      tag: 'App',
      fn: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: mkRatName }, arg: intArg }, arg: denArg },
      arg: proof,
    };
  };
  function rec(t: TTKTerm): TTKTerm {
    if (t.tag === 'App') {
      const fn = rec(t.fn);
      const arg = rec(t.arg);
      const reb: TTKTerm = { tag: 'App', fn, arg };
      if (reb.fn.tag === 'App' && reb.fn.fn.tag === 'Const'
          && (definitions.ratOpByFn?.has(reb.fn.fn.name) || definitions.natOpByFn?.has(reb.fn.fn.name))) {
        const reduced = whnf(reb, { definitions });
        if (definitions.ratOpByFn?.has(reb.fn.fn.name)) return liftLitToMkRat(reduced);
        return reduced;
      }
      return reb;
    }
    if (t.tag === 'Binder') return { ...t, domain: rec(t.domain), body: rec(t.body) };
    if (t.tag === 'Match') return { ...t, scrutinee: rec(t.scrutinee), clauses: t.clauses.map(c => ({ ...c, rhs: rec(c.rhs) })) };
    return t;
  }
  return rec(term);
}

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

  // Pre-pass: normalize literal arithmetic in the goal (\`ratPlus 1 -1\` → 0
  // → \`MkRat 0 1 _\`) so simp lemmas keyed on MkRat-form literals can fire
  // on goals where the user just got to via rewrites that left unreduced
  // operations. Only fires when the goal contains a @ratAdd-tagged head.
  let currentEngine = engine;
  const initGoal0 = engine.getFocusedGoal();
  const initGoalId0 = engine.getFocusedGoalId();
  const ratOps = engine.definitions.ratOpByFn;
  if (initGoal0 && initGoalId0 && ratOps && ratOps.size > 0 && goalMightHaveRatOp(initGoal0.type, ratOps)) {
    const normalized = normalizeRatOps(initGoal0.type, engine.definitions);
    if (normalized !== initGoal0.type) {
      const newMetaVars = new Map(engine.metaVars);
      newMetaVars.set(initGoalId0, { ...initGoal0, type: normalized });
      currentEngine = engine.withUpdates({ metaVars: newMetaVars });
    }
  }
  const steps: SimpStep[] = [];
  // Track seen goal types to detect cycles (e.g. commutativity: mul a b → mul b a → ...)
  const seenGoals = new Set<string>();

  // Record initial goal
  const initGoal = currentEngine.getFocusedGoal();
  if (initGoal) seenGoals.add(JSON.stringify(initGoal.type, (_, v) => typeof v === 'bigint' ? `bi:${v}` : v));

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
        const newGoalKey = newGoal ? JSON.stringify(newGoal.type, (_, v) => typeof v === 'bigint' ? `bi:${v}` : v) : null;
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
        const newGoalKey = newGoal ? JSON.stringify(newGoal.type, (_, v) => typeof v === 'bigint' ? `bi:${v}` : v) : null;
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
