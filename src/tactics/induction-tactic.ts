/**
 * Induction Tactic: Perform induction on an inductive type
 *
 * Similar to cases, but adds induction hypotheses for recursive constructors.
 *
 * Usage: induction n
 * Example: induction n with | Zero => ... | Succ n' IH => ...
 *
 * For Nat:
 * - Zero branch: no IH
 * - Succ branch: IH : P n' (where P is the goal abstracted over n)
 */

import { TTKTerm, TTKContext, TTKPattern, TTKClause } from '../compiler/kernel';
import { countKernelClauseBindings } from '../compiler/pattern-binders';
import { MetaVar, DefinitionsMap } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult, freshMetaName } from './tactic';
import { whnf } from '../compiler/whnf';
import { shiftTerm, subst } from '../compiler/subst';

/**
 * Pick a fresh variable name: try `base`, then `base1`, `base2`, etc.
 */
function freshVarName(base: string, used: ReadonlySet<string>): string {
  if (!used.has(base)) return base;
  let i = 1;
  while (used.has(`${base}${i}`)) i++;
  return `${base}${i}`;
}

/**
 * InductionTactic: Perform induction with induction hypotheses
 *
 * Creates one subgoal per constructor. For recursive constructors,
 * adds an induction hypothesis to the context.
 */
export class InductionTactic implements Tactic {
  name = 'induction';

  constructor(public readonly scrutinee: TTKTerm) {}

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      // 1. Infer type of scrutinee
      const inferredEnv = engine.inferInGoal(goal, this.scrutinee);
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
          error: `induction: scrutinee has non-inductive type ${this.termToString(scrutineeTypeWhnf)}`
        };
      }

      // 4. Look up inductive definition
      const inductiveDef = engine.definitions.inductiveTypes.get(inductiveName);
      if (!inductiveDef) {
        return {
          success: false,
          error: `induction: inductive type '${inductiveName}' not found`
        };
      }

      // 5. For each constructor, create a branch meta (with IH if recursive)
      const branchMetas: Array<{
        id: string;
        ctor: string;
        meta: MetaVar;
        numParams: number;  // Number of constructor parameters
        ihType?: TTKTerm;
        ihValue?: TTKTerm;
      }> = [];

      // Extract type arguments from scrutinee type (e.g., Nat from List Nat)
      const typeArgs = this.extractTypeArgs(scrutineeTypeWhnf);

      for (const ctor of inductiveDef.constructors) {
        const numImplicit = ctor.namedArgMap?.size ?? 0;
        const branchPrep = this.prepareBranch(
          goal,
          goal.ctx,
          ctor.type,
          inductiveName,
          engine.definitions,
          numImplicit,
          typeArgs,
          ctor.name,
          engine.recursiveTermName,
        );
        if (!branchPrep) {
          return {
            success: false,
            error: `induction: scrutinee must be a variable or constructor-compatible term`
          };
        }

        const branchId = freshMetaName();
        const branchMeta: MetaVar = {
          ctx: branchPrep.ctx,
          type: branchPrep.goalType,
          solution: undefined,
          caseTag: ctor.name
        };

        branchMetas.push({
          id: branchId,
          ctor: ctor.name,
          meta: branchMeta,
          numParams: branchPrep.numParams,
          ihType: branchPrep.ihType,
          ihValue: branchPrep.ihValue,
        });
      }

      // 7. Build eliminator/matcher application
      const branches = branchMetas.map(b => ({ tag: 'Meta', id: b.id } as TTKTerm));
      const elimTerm = this.buildMatchTerm(
        this.scrutinee,
        branchMetas,
        branches
      );

      // 8. Assign eliminator to current goal
      const newMetaVars = new Map(engine.metaVars);
      newMetaVars.set(goalId, { ...goal, solution: elimTerm });

      // Add branch metas
      for (const { id, meta } of branchMetas) {
        newMetaVars.set(id, meta);
      }

      // 9. Replace current goal with branch goals
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
          focusIndex: engine.focusIndex
        })
      };
    } catch (e) {
      const errorMsg = e instanceof Error ? e.message : String(e);
      return {
        success: false,
        error: `induction: ${errorMsg}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }

  private prepareBranch(
    goal: MetaVar,
    baseCtx: TTKContext,
    ctorType: TTKTerm,
    inductiveName: string,
    definitions: DefinitionsMap,
    numImplicit: number,
    typeArgs: TTKTerm[],
    ctorName: string,
    recursiveTermName?: string,
  ): { ctx: TTKContext; goalType: TTKTerm; numParams: number; ihType?: TTKTerm; ihValue?: TTKTerm } | null {
    if (this.scrutinee.tag !== 'Var') {
      return null;
    }

    let withParamsCtx = [...baseCtx];
    let currentType = ctorType;
    let recursiveArgIndex: number | null = null;
    let paramCount = 0;

    // Build set of used names from existing context
    const usedNames = new Set<string>();
    for (const entry of baseCtx) {
      usedNames.add(entry.name);
    }

    // Substitute type arguments for implicit params and skip those binders
    for (let i = 0; i < numImplicit; i++) {
      if (currentType.tag === 'Binder' && currentType.binderKind.tag === 'BPi') {
        const arg = typeArgs[i] || { tag: 'Hole', id: '_implicit_' + i };
        currentType = subst(0, arg, currentType.body);
      }
    }

    // Walk through the remaining (explicit) Pi binders
    while (currentType.tag === 'Binder' && currentType.binderKind.tag === 'BPi') {
      const rawName = currentType.name;
      let paramName: string;
      if (rawName && rawName !== '_') {
        paramName = freshVarName(rawName, usedNames);
      } else {
        paramName = freshVarName('x', usedNames);
      }
      usedNames.add(paramName);
      withParamsCtx.push({
        name: paramName,
        type: currentType.domain
      });

      // Check if this parameter is recursive (has type matching the inductive type)
      const domainWhnf = whnf(currentType.domain, { definitions });
      if (this.isRecursiveArg(domainWhnf, inductiveName)) {
        recursiveArgIndex = paramCount;
      }

      paramCount++;
      currentType = currentType.body;
    }

    const scrutineeIndexInExtendedCtx = this.scrutinee.index + paramCount;
    const ctorPattern = this.buildCtorPatternTerm(ctorName, paramCount, 0);
    const shiftedGoalType = paramCount > 0 ? shiftTerm(goal.type, paramCount, 0) : goal.type;
    const branchGoalWithoutIH = this.replaceVar(
      shiftedGoalType,
      scrutineeIndexInExtendedCtx,
      ctorPattern,
    );

    if (recursiveArgIndex === null) {
      return {
        ctx: withParamsCtx,
        goalType: branchGoalWithoutIH,
        numParams: paramCount,
      };
    }

    const recursiveArg: TTKTerm = { tag: 'Var', index: paramCount - 1 - recursiveArgIndex };
    const ihType = this.replaceVar(
      shiftedGoalType,
      scrutineeIndexInExtendedCtx,
      recursiveArg,
    );
    const ihValue = recursiveTermName
      ? this.buildRecursiveHypothesisValue(
          recursiveTermName,
          baseCtx,
          withParamsCtx,
          this.scrutinee.index,
          recursiveArg,
          ihType,
        )
      : undefined;
    const branchCtx = [
      ...withParamsCtx,
      { name: 'IH', type: ihType },
    ];

    return {
      ctx: branchCtx,
      goalType: shiftTerm(branchGoalWithoutIH, 1, 0),
      numParams: paramCount,
      ihType,
      ihValue,
    };
  }

  private replaceVar(term: TTKTerm, varIndex: number, value: TTKTerm, depth: number = 0): TTKTerm {
    switch (term.tag) {
      case 'Var':
        return term.index === varIndex + depth ? shiftTerm(value, depth, 0) : term;
      case 'App': {
        const fn = this.replaceVar(term.fn, varIndex, value, depth);
        const arg = this.replaceVar(term.arg, varIndex, value, depth);
        return fn === term.fn && arg === term.arg ? term : { tag: 'App', fn, arg };
      }
      case 'Binder': {
        const domain = this.replaceVar(term.domain, varIndex, value, depth);
        const binderKind = term.binderKind.tag === 'BLet'
          ? {
              tag: 'BLet' as const,
              defVal: this.replaceVar(term.binderKind.defVal, varIndex, value, depth),
            }
          : term.binderKind;
        const body = this.replaceVar(term.body, varIndex, value, depth + 1);
        return domain === term.domain && binderKind === term.binderKind && body === term.body
          ? term
          : { tag: 'Binder', name: term.name, binderKind, domain, body };
      }
      case 'Sort': {
        const level = this.replaceVar(term.level, varIndex, value, depth);
        return level === term.level ? term : { tag: 'Sort', level };
      }
      case 'Annot': {
        const inner = this.replaceVar(term.term, varIndex, value, depth);
        const type = this.replaceVar(term.type, varIndex, value, depth);
        return inner === term.term && type === term.type ? term : { tag: 'Annot', term: inner, type };
      }
      case 'Match': {
        const scrutinee = this.replaceVar(term.scrutinee, varIndex, value, depth);
        const clauses = term.clauses.map(clause => ({
          ...clause,
          rhs: this.replaceVar(clause.rhs, varIndex, value, depth + countKernelClauseBindings(clause)),
        }));
        return scrutinee === term.scrutinee && clauses.every((clause, i) => clause === term.clauses[i])
          ? term
          : { tag: 'Match', scrutinee, clauses };
      }
      default:
        return term;
    }
  }

  private buildRecursiveHypothesisValue(
    recursiveTermName: string,
    baseCtx: TTKContext,
    withParamsCtx: TTKContext,
    scrutineeIndex: number,
    recursiveArg: TTKTerm,
    ihType: TTKTerm,
  ): TTKTerm {
    const binders = this.collectLeadingPis(ihType);
    const totalDepth = withParamsCtx.length + binders.length;
    const scrutineePosition = baseCtx.length - 1 - scrutineeIndex;

    const args: TTKTerm[] = [];
    for (let i = 0; i < baseCtx.length; i++) {
      if (i === scrutineePosition) {
        args.push(shiftTerm(recursiveArg, binders.length, 0));
        continue;
      }
      args.push({ tag: 'Var', index: totalDepth - 1 - i });
    }

    const tailStart = withParamsCtx.length;
    for (let i = 0; i < binders.length; i++) {
      args.push({ tag: 'Var', index: totalDepth - 1 - (tailStart + i) });
    }

    let result: TTKTerm = { tag: 'Const', name: recursiveTermName };
    for (const arg of args) {
      result = { tag: 'App', fn: result, arg };
    }
    for (let i = binders.length - 1; i >= 0; i--) {
      result = {
        tag: 'Binder',
        name: binders[i].name,
        binderKind: { tag: 'BLam' },
        domain: binders[i].domain,
        body: result,
      };
    }

    return result;
  }

  private collectLeadingPis(type: TTKTerm): Array<{ name: string; domain: TTKTerm }> {
    const binders: Array<{ name: string; domain: TTKTerm }> = [];
    let current = type;
    while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
      binders.push({ name: current.name, domain: current.domain });
      current = current.body;
    }
    return binders;
  }

  private buildCtorPatternTerm(ctorName: string, numParams: number, offset: number): TTKTerm {
    let ctorPattern: TTKTerm = { tag: 'Const', name: ctorName };
    for (let i = numParams - 1; i >= 0; i--) {
      ctorPattern = {
        tag: 'App',
        fn: ctorPattern,
        arg: { tag: 'Var', index: i + offset },
      };
    }
    return ctorPattern;
  }

  /**
   * Check if a type is a recursive argument (references the inductive type)
   */
  private isRecursiveArg(type: TTKTerm, inductiveName: string): boolean {
    if (type.tag === 'Const') {
      return type.name === inductiveName;
    }

    // Could also be an application like (List A) where List is the inductive
    if (type.tag === 'App') {
      let head: TTKTerm = type;
      while (head.tag === 'App') {
        head = head.fn;
      }
      if (head.tag === 'Const') {
        return head.name === inductiveName;
      }
    }

    return false;
  }

  /**
   * Extract inductive type name from a type term
   */
  private getInductiveTypeName(type: TTKTerm): string | null {
    if (type.tag === 'Const') {
      return type.name;
    }

    if (type.tag === 'App') {
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
   * Build a proper Match term for induction
   */
  private buildMatchTerm(
    scrutinee: TTKTerm,
    branchMetas: Array<{ id: string; ctor: string; meta: MetaVar; numParams: number; ihType?: TTKTerm; ihValue?: TTKTerm }>,
    _branches: TTKTerm[]
  ): TTKTerm {
    const clauses: TTKClause[] = branchMetas.map(({ id, ctor, meta, numParams, ihType, ihValue }) => {
      const usedNames = new Set(meta.ctx.map(e => e.name));
      const pattern = this.buildCtorPattern(ctor, numParams, usedNames);
      const rhs = ihType && ihValue
        ? {
            tag: 'Binder' as const,
            name: 'IH',
            binderKind: { tag: 'BLet' as const, defVal: ihValue },
            domain: ihType,
            body: { tag: 'Meta' as const, id },
          }
        : { tag: 'Meta' as const, id };
      return {
        patterns: [pattern],
        rhs,
      };
    });

    return {
      tag: 'Match',
      scrutinee,
      clauses
    };
  }

  /**
   * Build a constructor pattern for a Match clause
   */
  private buildCtorPattern(ctorName: string, numParams: number, usedNames?: Set<string>): TTKPattern {
    // Build PCtor with PVar for each parameter
    const args: TTKPattern[] = [];
    const used = usedNames ?? new Set<string>();
    for (let i = 0; i < numParams; i++) {
      const name = freshVarName('x', used);
      used.add(name);
      args.push({ tag: 'PVar', name });
    }

    return {
      tag: 'PCtor',
      name: ctorName,
      args
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
