/**
 * Subst Tactic: Substitute a variable using an equality proof
 *
 * Given h : Equal x y in context where x is a variable,
 * replaces all occurrences of x with y in the goal and context,
 * then removes both h and x from context.
 *
 * Usage: subst h
 * Example:
 *   h : Equal a b
 *   goal : Equal a a
 *   After subst h: context loses h and a, goal becomes Equal b b
 */

import { TTKTerm, TTKContext } from '../compiler/kernel';
import { MetaVar, DefinitionsMap } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult, freshMetaName } from './tactic';
import { whnf } from '../compiler/whnf';
import { subst as termSubst } from '../compiler/subst';
import { shiftTerm } from '../compiler/subst';

/**
 * SubstTactic: Eliminate a variable using an equality proof
 */
export class SubstTactic implements Tactic {
  name = 'subst';

  constructor(public readonly equalityProof: TTKTerm) {}

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      // 1. The equalityProof should be a Var referring to a hypothesis in context
      if (this.equalityProof.tag !== 'Var') {
        return {
          success: false,
          error: `subst: argument must be a variable (hypothesis name), got ${this.equalityProof.tag}`
        };
      }

      const proofVarIndex = this.equalityProof.index;
      // Convert Var index to array position: array[ctx.length - 1 - varIndex]
      const proofArrayPos = goal.ctx.length - 1 - proofVarIndex;

      if (proofArrayPos < 0 || proofArrayPos >= goal.ctx.length) {
        return {
          success: false,
          error: `subst: variable index ${proofVarIndex} is out of context bounds`
        };
      }

      // 2. Get the type of the equality proof
      // Context entries store types prefix-relative; to get the type in full context scope,
      // shift by (ctx.length - proofArrayPos)
      const entryType = goal.ctx[proofArrayPos].type;
      const proofTypeFullScope = shiftTerm(entryType, goal.ctx.length - proofArrayPos, 0);

      // 3. WHNF to expose equality structure
      const proofTypeWhnf = whnf(proofTypeFullScope, { definitions: engine.definitions });

      // 4. Extract Equal lhs rhs
      const eqArgs = this.extractEqualityArgs(proofTypeWhnf);
      if (!eqArgs) {
        return {
          success: false,
          error: `subst: hypothesis is not an equality proof`
        };
      }

      const { lhs, rhs } = eqArgs;

      // 5. Determine which side is a variable and the direction of substitution
      let eliminatedVarIndex: number;  // de Bruijn index of the variable being eliminated
      let replacement: TTKTerm;        // what to replace it with

      if (lhs.tag === 'Var') {
        eliminatedVarIndex = lhs.index;
        replacement = rhs;
      } else if (rhs.tag === 'Var') {
        eliminatedVarIndex = rhs.index;
        replacement = lhs;
      } else {
        return {
          success: false,
          error: `subst: neither side of the equality is a variable`
        };
      }

      const eliminatedArrayPos = goal.ctx.length - 1 - eliminatedVarIndex;

      // Sanity check: don't eliminate the proof variable itself
      if (eliminatedArrayPos === proofArrayPos) {
        return {
          success: false,
          error: `subst: cannot eliminate the proof variable itself`
        };
      }

      // 6. Apply substitution to goal type: replace eliminatedVar with replacement
      const newGoalType = termSubst(eliminatedVarIndex, replacement, goal.type);

      // 7. Build new context by removing the proof and the eliminated variable
      // We need to remove two entries and adjust de Bruijn indices throughout
      //
      // Removal order matters for index adjustment. Remove the higher array position first.
      const pos1 = Math.max(proofArrayPos, eliminatedArrayPos);
      const pos2 = Math.min(proofArrayPos, eliminatedArrayPos);
      // pos1 > pos2, so pos1 has the lower de Bruijn index

      // After removing pos1, everything at or above pos1 shifts down
      // After removing pos2, everything at or above pos2 shifts down again

      // Build new context
      const newCtx: TTKContext = [];
      for (let i = 0; i < goal.ctx.length; i++) {
        if (i === proofArrayPos || i === eliminatedArrayPos) continue;

        const entry = goal.ctx[i];
        // Get type in full context scope
        let typeInFullScope = shiftTerm(entry.type, goal.ctx.length - i, 0);

        // Apply the variable substitution (replace eliminated var with replacement)
        typeInFullScope = termSubst(eliminatedVarIndex, replacement, typeInFullScope);

        // Now we need to adjust for the removal of the proof variable
        // termSubst already decrements indices above eliminatedVarIndex
        // But we also need to remove proofVarIndex
        // After termSubst, proofVarIndex may have shifted if proofVarIndex > eliminatedVarIndex
        let adjustedProofVarIndex = proofVarIndex;
        if (proofVarIndex > eliminatedVarIndex) {
          // termSubst already decremented it
          adjustedProofVarIndex = proofVarIndex - 1;
        }

        // Remove the proof variable by shifting
        typeInFullScope = removeVar(adjustedProofVarIndex, typeInFullScope);

        // Shift back to prefix-relative for the new context
        // New context has (goal.ctx.length - 2) entries total
        // This entry's new array position
        let newArrayPos: number;
        if (i < pos2) {
          newArrayPos = i;
        } else if (i < pos1) {
          newArrayPos = i - 1;
        } else {
          newArrayPos = i - 2;
        }
        const newCtxSize = goal.ctx.length - 2;
        typeInFullScope = shiftTerm(typeInFullScope, -(newCtxSize - newArrayPos), 0);

        newCtx.push({ name: entry.name, type: typeInFullScope });
      }

      // 8. Adjust the goal type for the removed proof variable
      let adjustedGoalType = newGoalType;
      // newGoalType already has eliminatedVar substituted (via termSubst which decrements above)
      // Now remove the proof variable
      let adjustedProofVarIndex = proofVarIndex;
      if (proofVarIndex > eliminatedVarIndex) {
        adjustedProofVarIndex = proofVarIndex - 1;
      }
      adjustedGoalType = removeVar(adjustedProofVarIndex, adjustedGoalType);

      // 9. Create new goal meta
      const newMetaId = freshMetaName();
      const newMeta: MetaVar = {
        ctx: newCtx,
        type: adjustedGoalType,
        solution: undefined
      };

      // 10. Set the current goal's solution to the new meta
      // (The proof term is symbolic — tactic proofs bypass kernel re-checking)
      const newMetaVars = new Map(engine.metaVars);
      newMetaVars.set(goalId, { ...goal, solution: { tag: 'Meta', id: newMetaId } });
      newMetaVars.set(newMetaId, newMeta);

      const newGoals = engine.goals.map(g => g === goalId ? newMetaId : g);

      return {
        success: true,
        newEngine: engine.withUpdates({
          metaVars: newMetaVars,
          goals: newGoals
        })
      };
    } catch (e) {
      const errorMsg = e instanceof Error ? e.message : String(e);
      return {
        success: false,
        error: `subst: ${errorMsg}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }

  /**
   * Extract LHS and RHS from an equality type: Equal A lhs rhs
   */
  private extractEqualityArgs(type: TTKTerm): { lhs: TTKTerm; rhs: TTKTerm } | null {
    if (type.tag !== 'App') return null;

    const args: TTKTerm[] = [];
    let current: TTKTerm = type;
    while (current.tag === 'App') {
      args.unshift(current.arg);
      current = current.fn;
    }

    if (current.tag !== 'Const' || current.name !== 'Equal') return null;
    if (args.length < 2) return null;

    return {
      lhs: args[args.length - 2],
      rhs: args[args.length - 1]
    };
  }
}

/**
 * Remove a free variable from a term by decrementing all variables above it.
 * This is like substitution but without providing a replacement — it assumes
 * the variable doesn't occur in the term (or has already been substituted away).
 */
function removeVar(varIndex: number, term: TTKTerm): TTKTerm {
  return removeVarHelper(varIndex, term, 0);
}

function removeVarHelper(targetIndex: number, term: TTKTerm, depth: number): TTKTerm {
  switch (term.tag) {
    case 'Var':
      if (term.index >= targetIndex + depth) {
        return { tag: 'Var', index: term.index - 1 };
      }
      return term;

    case 'App':
      return {
        tag: 'App',
        fn: removeVarHelper(targetIndex, term.fn, depth),
        arg: removeVarHelper(targetIndex, term.arg, depth)
      };

    case 'Binder':
      return {
        tag: 'Binder',
        binderKind: term.binderKind,
        name: term.name,
        domain: removeVarHelper(targetIndex, term.domain, depth),
        body: removeVarHelper(targetIndex, term.body, depth + 1)
      };

    case 'Sort': {
      const newLevel = removeVarHelper(targetIndex, term.level, depth);
      if (newLevel === term.level) return term;
      return { tag: 'Sort', level: newLevel };
    }

    case 'Match': {
      const newScrutinee = removeVarHelper(targetIndex, term.scrutinee, depth);
      const newClauses = term.clauses.map(c => ({
        patterns: c.patterns,
        rhs: removeVarHelper(targetIndex, c.rhs, depth + c.patterns.reduce((sum, p) => sum + countPatVars(p), 0))
      }));
      return { tag: 'Match', scrutinee: newScrutinee, clauses: newClauses };
    }

    case 'Annot': {
      const newTerm = removeVarHelper(targetIndex, term.term, depth);
      const newType = removeVarHelper(targetIndex, term.type, depth);
      return { tag: 'Annot', term: newTerm, type: newType };
    }

    case 'Const':
    case 'Meta':
    case 'Hole':
    case 'ULevel':
    case 'ULit':
    case 'UOmega':
      return term;

    default:
      return term;
  }
}

function countPatVars(p: import('../compiler/kernel').TTKPattern): number {
  switch (p.tag) {
    case 'PVar':
    case 'PWild':
      return 1;
    case 'PCtor':
      return p.args.reduce((sum, a) => sum + countPatVars(a), 0);
  }
}
