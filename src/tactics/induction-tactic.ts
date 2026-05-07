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
import { MetaVar, DefinitionsMap } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult, freshMetaName } from './tactic';
import { whnf } from '../compiler/whnf';
import { shiftTerm, subst } from '../compiler/subst';

function abstractVar(term: TTKTerm, targetIdx: number, replacement: TTKTerm): TTKTerm {
  switch (term.tag) {
    case 'Var':
      return term.index === targetIdx ? replacement : term;
    case 'App': {
      const fn = abstractVar(term.fn, targetIdx, replacement);
      const arg = abstractVar(term.arg, targetIdx, replacement);
      return fn === term.fn && arg === term.arg ? term : { tag: 'App', fn, arg };
    }
    case 'Binder': {
      const domain = abstractVar(term.domain, targetIdx, replacement);
      const body = abstractVar(term.body, targetIdx + 1, shiftTerm(replacement, 1, 0));
      return domain === term.domain && body === term.body ? term : { ...term, domain, body };
    }
    case 'Match': {
      const scrutinee = abstractVar(term.scrutinee, targetIdx, replacement);
      let changed = scrutinee !== term.scrutinee;
      const clauses = term.clauses.map(clause => {
        const numBoundVars = countPatternsBoundVars(clause.patterns);
        const rhs = abstractVar(clause.rhs, targetIdx + numBoundVars, shiftTerm(replacement, numBoundVars, 0));
        if (rhs !== clause.rhs) changed = true;
        return rhs === clause.rhs ? clause : { ...clause, rhs };
      });
      return changed ? { ...term, scrutinee, clauses } : term;
    }
    default:
      return term;
  }
}

function countPatternBoundVars(pattern: TTKPattern): number {
  switch (pattern.tag) {
    case 'PVar':
    case 'PWild':
      return 1;
    case 'PCtor':
      return pattern.args.reduce((sum, arg) => sum + countPatternBoundVars(arg), 0);
  }
}

function countPatternsBoundVars(patterns: readonly TTKPattern[]): number {
  return patterns.reduce((sum, pattern) => sum + countPatternBoundVars(pattern), 0);
}

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

      // 5. Build the motive P: abstract the goal over the scrutinee
      // If goal is `G[n]` and we're inducting on `n : Nat`,
      // then P = λ (x : Nat). G[x]
      const motive = this.buildMotive(goal, this.scrutinee, scrutineeType);

      // 6. For each constructor, create a branch meta (with IH if recursive)
      const branchMetas: Array<{
        id: string;
        ctor: string;
        meta: MetaVar;
        numParams: number;  // Number of constructor parameters
      }> = [];

      // Extract type arguments from scrutinee type (e.g., Nat from List Nat)
      const typeArgs = this.extractTypeArgs(scrutineeTypeWhnf);

      for (const ctor of inductiveDef.constructors) {
        // Extend context with constructor parameters AND induction hypothesis
        const numImplicit = ctor.namedArgMap?.size ?? 0;
        const { branchCtx, hasRecursiveArg, numParams } = this.extendContextWithCtorParamsAndIH(
          goal.ctx,
          ctor.type,
          this.scrutinee,
          motive,
          inductiveName,
          engine.definitions,
          numImplicit,
          typeArgs
        );

        // Compute the branch goal type by applying the motive to the constructor pattern
        // For Zero: motive Zero
        // For Succ n': motive (Succ n') where n' is at index 0 (or IH index if has IH)
        const branchGoalType = this.computeBranchGoalType(
          motive,
          ctor,
          numParams,
          hasRecursiveArg
        );

        // Create meta for this branch
        const branchId = freshMetaName();
        const branchMeta: MetaVar = {
          ctx: branchCtx,
          type: branchGoalType,
          solution: undefined,
          caseTag: ctor.name
        };

        branchMetas.push({ id: branchId, ctor: ctor.name, meta: branchMeta, numParams });
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

  /**
   * Build the motive (induction principle):
   * Abstract the goal type over the scrutinee
   *
   * If goal is `Equal (plus n m) (plus m n)` and we induct on `n`,
   * motive P = λ (x : Nat). Equal (plus x m) (plus m x)
   *
   * IMPORTANT: After intro, the scrutinee is the most recent variable (index 0).
   * The motive wraps the goal type in a lambda, so the scrutinee remains at index 0.
   */
  private buildMotive(goal: MetaVar, _scrutinee: TTKTerm, scrutineeType: TTKTerm): TTKTerm {
    const body = this.abstractScrutinee(goal.type, this.scrutinee);
    return {
      tag: 'Binder',
      binderKind: { tag: 'BLam' },
      name: 'x',
      domain: scrutineeType,
      body
    };
  }

  private abstractScrutinee(goalType: TTKTerm, scrutinee: TTKTerm): TTKTerm {
    if (scrutinee.tag !== 'Var') {
      return shiftTerm(goalType, 1, 0);
    }
    const shiftedGoalType = shiftTerm(goalType, 1, 0);
    return abstractVar(shiftedGoalType, scrutinee.index + 1, { tag: 'Var', index: 0 });
  }

  /**
   * Compute the branch goal type by applying the motive to the constructor pattern
   *
   * For Zero: motive Zero
   * For Succ n': motive (Succ n')
   */
  private computeBranchGoalType(
    motive: TTKTerm,
    ctor: { name: string; type: TTKTerm },
    numParams: number,
    hasRecursiveArg: boolean
  ): TTKTerm {
    // Build the constructor pattern: ctor arg1 arg2 ... argN
    // Arguments are the constructor parameters, referenced by de Bruijn index
    // In the branch context, the most recent variable is at index 0

    // For Zero: just Zero (no parameters)
    // For Succ n': Succ n' (one parameter at index 0, or index 1 if there's an IH)

    let ctorPattern: TTKTerm = { tag: 'Const', name: ctor.name };

    // Apply constructor to its parameters
    // Parameters are at indices [numParams-1, numParams-2, ..., 1, 0] (or shifted if IH exists)
    // Actually, in the branch context after adding params and IH:
    // - If no IH: params are at [numParams-1, ..., 0]
    // - If IH: IH is at 0, params are at [numParams, ..., 1]

    const ihOffset = hasRecursiveArg ? 1 : 0;
    for (let i = numParams - 1; i >= 0; i--) {
      ctorPattern = {
        tag: 'App',
        fn: ctorPattern,
        arg: { tag: 'Var', index: i + ihOffset }
      };
    }

    // Apply motive to the constructor pattern
    return {
      tag: 'App',
      fn: motive,
      arg: ctorPattern
    };
  }

  /**
   * Extend context with constructor parameters AND induction hypothesis
   *
   * For Succ : Nat -> Nat:
   * - Add 'n' : Nat (constructor parameter)
   * - Add 'IH' : P n (induction hypothesis)
   */
  private extendContextWithCtorParamsAndIH(
    baseCtx: TTKContext,
    ctorType: TTKTerm,
    _scrutinee: TTKTerm,
    motive: TTKTerm,
    inductiveName: string,
    definitions: DefinitionsMap,
    numImplicit: number,
    typeArgs: TTKTerm[]
  ): { branchCtx: TTKContext; hasRecursiveArg: boolean; numParams: number } {
    let newCtx = [...baseCtx];
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
      newCtx.push({
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

    // If there was a recursive argument, add induction hypothesis
    if (recursiveArgIndex !== null) {
      // IH type: P (recursive_arg)
      // For Succ case with param n' : Nat, IH : P n'
      // The recursive arg is now at de Bruijn index 0 (most recent)
      const recursiveArg: TTKTerm = { tag: 'Var', index: paramCount - 1 - recursiveArgIndex };

      // Apply motive to recursive arg: P n'
      const ihType: TTKTerm = {
        tag: 'App',
        fn: motive,
        arg: recursiveArg
      };

      newCtx.push({
        name: 'IH',
        type: ihType
      });
    }

    return {
      branchCtx: newCtx,
      hasRecursiveArg: recursiveArgIndex !== null,
      numParams: paramCount
    };
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
    branchMetas: Array<{ id: string; ctor: string; meta: MetaVar; numParams: number }>,
    _branches: TTKTerm[]
  ): TTKTerm {
    const clauses: TTKClause[] = branchMetas.map(({ id, ctor, meta, numParams }) => {
      const usedNames = new Set(meta.ctx.map(e => e.name));
      const pattern = this.buildCtorPattern(ctor, numParams, usedNames);
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
