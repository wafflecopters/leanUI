/**
 * Obtain Tactic: Destructure a single-constructor inductive type
 *
 * Works with ANY inductive type that has exactly one constructor.
 * Binds the constructor's explicit parameters with user-provided names.
 *
 * Usage: obtain (x, y, z) := proof
 * Example:
 *   goal : SomeType
 *   obtain (delta, hdelta) := limitWitness
 *   -- now delta : A, hdelta : P delta are in context
 *
 * Proof term: match proof with | MkCtor x y z => ?newGoal
 */

import { TTKTerm, TTKContext, TTKPattern, TTKClause } from '../compiler/kernel';
import { MetaVar } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult, freshMetaName } from './tactic';
import { inferType } from '../compiler/checker';
import { whnf } from '../compiler/whnf';
import { subst, shiftTerm } from '../compiler/subst';

export class ObtainTactic implements Tactic {
  name = 'obtain';

  constructor(
    public readonly bindingNames: string[],
    public readonly proof: TTKTerm
  ) {}

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      // 1. Infer type of proof expression
      const env = engine.toTCEnv(goal, this.proof);
      const inferredEnv = inferType(env);
      const proofType = inferredEnv.value;

      // 2. WHNF to find inductive type
      const typeWhnf = whnf(proofType, {
        definitions: engine.definitions,
        typingContext: goal.ctx
      });

      // 3. Extract inductive type name
      const inductiveName = this.getInductiveTypeName(typeWhnf);
      if (!inductiveName) {
        return {
          success: false,
          error: `obtain: expression has non-inductive type ${this.termToString(typeWhnf)}`
        };
      }

      // 4. Look up inductive definition
      const inductiveDef = engine.definitions.inductiveTypes.get(inductiveName);
      if (!inductiveDef) {
        return {
          success: false,
          error: `obtain: inductive type '${inductiveName}' not found`
        };
      }

      // 5. Verify single constructor
      if (inductiveDef.constructors.length !== 1) {
        return {
          success: false,
          error: `obtain: '${inductiveName}' has ${inductiveDef.constructors.length} constructors (expected exactly 1)`
        };
      }

      const ctor = inductiveDef.constructors[0];
      const numImplicit = ctor.namedArgMap?.size ?? 0;
      const typeArgs = this.extractTypeArgs(typeWhnf);

      // 6. Walk constructor type to find explicit parameters
      let ctorType = ctor.type;
      for (let i = 0; i < numImplicit; i++) {
        if (ctorType.tag === 'Binder' && ctorType.binderKind.tag === 'BPi') {
          const arg = typeArgs[i] || { tag: 'Hole' as const, id: '_implicit_' + i };
          ctorType = subst(0, arg, ctorType.body);
        }
      }

      // Count explicit parameters
      const explicitParams: Array<{ name: string; type: TTKTerm }> = [];
      let walkType = ctorType;
      while (walkType.tag === 'Binder' && walkType.binderKind.tag === 'BPi') {
        explicitParams.push({ name: walkType.name, type: walkType.domain });
        walkType = walkType.body;
      }

      // 7. Validate name count
      if (this.bindingNames.length !== explicitParams.length) {
        return {
          success: false,
          error: `obtain: '${ctor.name}' has ${explicitParams.length} fields but ${this.bindingNames.length} names were provided`
        };
      }

      // 8. Build branch context with user-provided names
      const branchCtx: TTKContext = [...goal.ctx];
      let currentType = ctorType;
      const paramNames: string[] = [];
      for (let i = 0; i < explicitParams.length; i++) {
        if (currentType.tag === 'Binder' && currentType.binderKind.tag === 'BPi') {
          const userName = this.bindingNames[i];
          const paramName = (userName && userName !== '_') ? userName : explicitParams[i].name;
          branchCtx.push({ name: paramName, type: currentType.domain });
          paramNames.push(paramName);
          currentType = currentType.body;
        }
      }

      // 9. Create new goal meta for the branch body
      const numNewParams = branchCtx.length - goal.ctx.length;
      const branchGoalType = numNewParams > 0 ? shiftTerm(goal.type, numNewParams, 0) : goal.type;

      const branchId = freshMetaName();
      const branchMeta: MetaVar = {
        ctx: branchCtx,
        type: branchGoalType,
        solution: undefined
      };

      // 10. Build match term with single clause
      const patternArgs: TTKPattern[] = paramNames.map(name => ({
        tag: 'PVar' as const,
        name
      }));

      const pattern: TTKPattern = {
        tag: 'PCtor',
        name: ctor.name,
        args: patternArgs
      };

      const clause: TTKClause = {
        patterns: [pattern],
        rhs: { tag: 'Meta', id: branchId }
      };

      const elaboratedProof = inferredEnv.zonkTerm(inferredEnv.elaboratedTerm ?? this.proof);

      const matchTerm: TTKTerm = {
        tag: 'Match',
        scrutinee: elaboratedProof,
        clauses: [clause]
      };

      // 11. Update engine state
      const newMetaVars = new Map(inferredEnv.metaVars);
      newMetaVars.set(goalId, { ...goal, solution: matchTerm });
      newMetaVars.set(branchId, branchMeta);

      const newGoals = engine.goals.map(g => g === goalId ? branchId : g);

      return {
        success: true,
        newEngine: engine.withUpdates({
          metaVars: newMetaVars,
          constraints: inferredEnv.constraints,
          goals: newGoals
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
        error: `obtain: ${errorMsg}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }

  private getInductiveTypeName(type: TTKTerm): string | null {
    if (type.tag === 'Const') return type.name;
    if (type.tag === 'App') {
      let head: TTKTerm = type;
      while (head.tag === 'App') head = head.fn;
      if (head.tag === 'Const') return head.name;
    }
    return null;
  }

  private extractTypeArgs(type: TTKTerm): TTKTerm[] {
    const args: TTKTerm[] = [];
    let current = type;
    while (current.tag === 'App') {
      args.unshift(current.arg);
      current = current.fn;
    }
    return args;
  }

  private termToString(term: TTKTerm): string {
    switch (term.tag) {
      case 'Const': return term.name;
      case 'Var': return `#${term.index}`;
      case 'App': return `(${this.termToString(term.fn)} ${this.termToString(term.arg)})`;
      case 'Binder': return `(${term.name} : ${this.termToString(term.domain)}) -> ${this.termToString(term.body)}`;
      default: return `<${term.tag}>`;
    }
  }
}
