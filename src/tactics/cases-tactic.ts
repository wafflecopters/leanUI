/**
 * Cases Tactic: Pattern matching with branching
 *
 * Phase 4 of tactics redesign: Implement cases tactic that creates
 * multiple subgoals (one per constructor) enabling structured proofs
 * by case analysis.
 */

import { TTKTerm, TTKContext, TTKPattern, TTKClause } from '../compiler/kernel';
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

      // 5. For each constructor, create a branch meta and collect pattern info
      const branchMetas: Array<{
        id: string;
        ctor: string;
        meta: MetaVar;
        explicitParamNames: string[];
      }> = [];

      // Extract type arguments from scrutinee type (e.g., Nat from List Nat)
      const typeArgs = this.extractTypeArgs(scrutineeTypeWhnf);

      for (const ctor of inductiveDef.constructors) {
        // Extend context with constructor parameters
        const numImplicit = ctor.namedArgMap?.size ?? 0;
        const { ctx: branchCtx, paramNames } = this.extendContextWithCtorParams(
          goal.ctx,
          ctor.type,
          numImplicit,
          typeArgs
        );

        // Create meta for this branch
        const branchId = freshMetaName();
        const branchMeta: MetaVar = {
          ctx: branchCtx,
          type: goal.type, // Same target type as original goal
          solution: undefined,
          caseTag: ctor.name // Tag with constructor name for structured cases
        };

        branchMetas.push({ id: branchId, ctor: ctor.name, meta: branchMeta, explicitParamNames: paramNames });
      }

      // 6. Build a proper Match term
      const elimTerm = this.buildMatchTerm(this.scrutinee, branchMetas);

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

  private extractTypeArgs(scrutineeType: TTKTerm): TTKTerm[] {
    const args: TTKTerm[] = [];
    let current = scrutineeType;
    while (current.tag === 'App') {
      args.unshift(current.arg);
      current = current.fn;
    }
    return args;
  }

  /**
   * Extend context with constructor parameters (explicit only)
   * Returns the extended context and the names of explicit params.
   */
  private extendContextWithCtorParams(
    baseCtx: TTKContext,
    ctorType: TTKTerm,
    numImplicit: number,
    typeArgs: TTKTerm[]
  ): { ctx: TTKContext; paramNames: string[] } {
    let newCtx = [...baseCtx];
    let currentType = ctorType;
    const paramNames: string[] = [];

    // Substitute type arguments for implicit params and skip those binders
    for (let i = 0; i < numImplicit; i++) {
      if (currentType.tag === 'Binder' && currentType.binderKind.tag === 'BPi') {
        const arg = typeArgs[i] || { tag: 'Hole', id: '_implicit_' + i };
        currentType = subst(0, arg, currentType.body);
      }
    }

    // Walk through the remaining (explicit) Pi binders
    let paramIdx = 0;
    while (currentType.tag === 'Binder' && currentType.binderKind.tag === 'BPi') {
      const rawName = currentType.name;
      const paramName = (rawName && rawName !== '_') ? rawName : ('_arg' + paramIdx);
      paramIdx++;
      newCtx.push({
        name: paramName,
        type: currentType.domain
      });
      paramNames.push(paramName);

      currentType = currentType.body;
    }

    return { ctx: newCtx, paramNames };
  }

  /**
   * Build a proper Match term with clauses for each constructor.
   *
   * Each clause has a PCtor pattern with PVar args for explicit params.
   * The pattern checker will automatically pad with wildcards for implicit params.
   */
  private buildMatchTerm(
    scrutinee: TTKTerm,
    branchMetas: Array<{ id: string; ctor: string; explicitParamNames: string[] }>
  ): TTKTerm {
    const clauses: TTKClause[] = branchMetas.map(({ id, ctor, explicitParamNames }) => {
      // Build PVar patterns for explicit params only
      const patternArgs: TTKPattern[] = explicitParamNames.map(name => ({
        tag: 'PVar' as const,
        name
      }));

      const pattern: TTKPattern = {
        tag: 'PCtor',
        name: ctor,
        args: patternArgs
      };

      return {
        patterns: [pattern],
        rhs: { tag: 'Meta' as const, id }
      };
    });

    return {
      tag: 'Match',
      scrutinee,
      clauses
    };
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
