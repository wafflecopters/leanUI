/**
 * Cases Tactic: Pattern matching with branching
 *
 * Phase 4 of tactics redesign: Implement cases tactic that creates
 * multiple subgoals (one per constructor) enabling structured proofs
 * by case analysis.
 */

import { TTKTerm, TTKContext } from '../compiler/kernel';
import { MetaVar, DefinitionsMap } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult, freshMetaName } from './tactic';
import { inferType } from '../compiler/checker';
import { whnf } from '../compiler/whnf';
import { subst } from '../compiler/subst';

/**
 * CasesTactic: Perform case analysis on an inductive type
 *
 * Usage: cases <term>
 * Example: cases n (where n : Nat)
 *
 * Creates one subgoal per constructor of the inductive type.
 * Each subgoal is tagged with the constructor name for use with 'case' tactic.
 */
export class CasesTactic implements Tactic {
  name = 'cases';

  constructor(public readonly scrutinee: TTKTerm) {}

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      // 1. Infer type of scrutinee
      const env = engine.toTCEnv(goal, this.scrutinee);
      const inferredEnv = inferType(env);
      const scrutineeType = inferredEnv.value;

      // 2. Normalize to find inductive type
      const scrutineeTypeWhnf = whnf(scrutineeType, {
        definitions: engine.definitions
      });

      // 3. Extract inductive type name
      const inductiveName = this.getInductiveTypeName(scrutineeTypeWhnf);
      if (!inductiveName) {
        return {
          success: false,
          error: `cases: scrutinee has non-inductive type ${this.termToString(scrutineeTypeWhnf)}`
        };
      }

      // 4. Look up inductive definition
      const inductiveDef = engine.definitions.inductiveTypes.get(inductiveName);
      if (!inductiveDef) {
        return {
          success: false,
          error: `cases: inductive type '${inductiveName}' not found`
        };
      }

      // 5. For each constructor, create a branch meta
      const branchMetas: Array<{
        id: string;
        ctor: string;
        meta: MetaVar;
      }> = [];

      for (const ctor of inductiveDef.constructors) {
        // Extend context with constructor parameters
        const branchCtx = this.extendContextWithCtorParams(
          goal.ctx,
          ctor.type,
          this.scrutinee
        );

        // Create meta for this branch
        const branchId = freshMetaName();
        const branchMeta: MetaVar = {
          ctx: branchCtx,
          type: goal.type, // Same target type as original goal
          solution: undefined,
          caseTag: ctor.name // Tag with constructor name for structured cases
        };

        branchMetas.push({ id: branchId, ctor: ctor.name, meta: branchMeta });
      }

      // 6. Build eliminator/matcher application
      // For now, we'll build a simple match expression
      const elimTerm = this.buildMatchTerm(
        this.scrutinee,
        branchMetas.map(b => ({ tag: 'Meta', id: b.id } as TTKTerm))
      );

      // 7. Assign eliminator to current goal
      const newMetaVars = new Map(engine.metaVars);
      newMetaVars.set(goalId, { ...goal, solution: elimTerm });

      // Add branch metas
      for (const { id, meta } of branchMetas) {
        newMetaVars.set(id, meta);
      }

      // 8. Replace current goal with branch goals
      const newGoalIds = branchMetas.map(b => b.id);
      const newGoals = [
        ...engine.goals.slice(0, engine.focusIndex),
        ...newGoalIds,
        ...engine.goals.slice(engine.focusIndex + 1)
      ];

      return {
        success: true,
        newEngine: engine.withUpdates({
          metaVars: newMetaVars,
          goals: newGoals,
          focusIndex: engine.focusIndex // Focus first new goal
        })
      };
    } catch (e) {
      const errorMsg = e instanceof Error
        ? e.message
        : (e && typeof e === 'object' && 'message' in e)
          ? String((e as any).message)
          : String(e);

      return {
        success: false,
        error: `cases: ${errorMsg}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }

  /**
   * Extract inductive type name from a type term
   */
  private getInductiveTypeName(type: TTKTerm): string | null {
    // Handle direct constant (e.g., Nat)
    if (type.tag === 'Const') {
      return type.name;
    }

    // Handle application (e.g., List A, Vec A n)
    if (type.tag === 'App') {
      // Find the head of the application chain
      let head: TTKTerm = type;
      while (head.tag === 'App') {
        head = head.fn;
      }
      if (head.tag === 'Const') {
        return head.name;
      }
    }

    return null;
  }

  /**
   * Extend context with constructor parameters
   *
   * For a constructor like Succ : Nat -> Nat, we add 'n : Nat' to context.
   * For a constructor like Zero : Nat, we don't add anything.
   */
  private extendContextWithCtorParams(
    baseCtx: TTKContext,
    ctorType: TTKTerm,
    _scrutinee: TTKTerm
  ): TTKContext {
    let newCtx = [...baseCtx];
    let currentType = ctorType;

    // Walk through Pi binders in constructor type
    while (currentType.tag === 'Binder' && currentType.binderKind.tag === 'BPi') {
      // Add parameter to context
      // Generate name if not present
      const paramName = currentType.name || 'x';
      newCtx.push({
        name: paramName,
        type: currentType.domain
      });

      // Move to body
      currentType = currentType.body;
    }

    return newCtx;
  }

  /**
   * Build a match/eliminator term
   *
   * For now, this builds a simple match expression.
   * Future: Generate proper eliminator application.
   */
  private buildMatchTerm(_scrutinee: TTKTerm, branches: TTKTerm[]): TTKTerm {
    // Build: match scrutinee with ?branch1 | ?branch2 | ...
    // For now, we'll use a Match term (needs to be added to kernel)
    // Temporary: Just return first branch (this is a placeholder)

    // TODO: Implement proper match/eliminator term construction
    // For now, return the first branch as a placeholder
    return branches[0] || { tag: 'Const', name: 'unit' };
  }

  /**
   * Helper: Convert term to string for error messages
   */
  private termToString(term: TTKTerm): string {
    switch (term.tag) {
      case 'Const':
        return term.name;
      case 'Var':
        return `#${term.index}`;
      case 'App':
        return `(${this.termToString(term.fn)} ${this.termToString(term.arg)})`;
      case 'Binder':
        return `(${term.name} : ${this.termToString(term.domain)}) -> ${this.termToString(term.body)}`;
      default:
        return `<${term.tag}>`;
    }
  }
}

/**
 * Helper extension for TacticEngine to create TCEnv
 */
declare module './tacticsEngine' {
  interface TacticEngine {
    toTCEnv(goal: MetaVar, term: TTKTerm): any;
  }
}

// Add the method implementation
import { TCEnv } from '../compiler/term';

TacticEngine.prototype.toTCEnv = function(goal: MetaVar, term: TTKTerm): TCEnv<any> {
  return new TCEnv(
    goal.ctx,
    this.definitions,
    this.metaVars,
    this.constraints,
    [],
    [],
    term,
    new Map(),
    { mode: 'check' }
  );
};
