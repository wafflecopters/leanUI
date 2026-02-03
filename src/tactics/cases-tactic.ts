/**
 * Cases Tactic: Pattern matching with branching
 *
 * Supports both simple (non-indexed) and indexed inductive types.
 * For indexed types (Leq, Equal, Vec, Fin), computes refined goal types
 * per-branch by substituting constructor index values into the goal.
 */

import { TTKTerm, TTKContext, TTKPattern, TTKClause } from '../compiler/kernel';
import { MetaVar, DefinitionsMap, InductiveDefinition } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult, freshMetaName } from './tactic';
import { inferType } from '../compiler/checker';
import { whnf } from '../compiler/whnf';
import { subst, shiftTerm } from '../compiler/subst';

/**
 * CasesTactic: Perform case analysis on an inductive type
 *
 * Usage: cases <term>
 * Example: cases n (where n : Nat)
 *
 * Creates one subgoal per constructor of the inductive type.
 * For indexed types, branch goal types are refined based on constructor indices.
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

      // Extract type arguments from scrutinee type (e.g., [A, n] from Vec A n)
      const typeArgs = this.extractTypeArgs(scrutineeTypeWhnf);

      // 5. Branch based on whether the type has indices
      const hasIndices = (inductiveDef.indexPositions?.length ?? 0) > 0;
      if (hasIndices) {
        return this.applyIndexed(engine, goal, goalId, inductiveDef, typeArgs);
      }

      // === Non-indexed path (existing logic) ===
      const branchMetas: Array<{
        id: string;
        ctor: string;
        meta: MetaVar;
        explicitParamNames: string[];
      }> = [];

      for (const ctor of inductiveDef.constructors) {
        const numImplicit = ctor.namedArgMap?.size ?? 0;
        const { ctx: branchCtx, paramNames } = this.extendContextWithCtorParams(
          goal.ctx,
          ctor.type,
          numImplicit,
          typeArgs
        );

        const branchId = freshMetaName();
        const branchMeta: MetaVar = {
          ctx: branchCtx,
          type: goal.type,
          solution: undefined,
          caseTag: ctor.name
        };

        branchMetas.push({ id: branchId, ctor: ctor.name, meta: branchMeta, explicitParamNames: paramNames });
      }

      const elimTerm = this.buildMatchTerm(this.scrutinee, branchMetas);
      return this.finishApply(engine, goal, goalId, branchMetas, elimTerm);

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

  // ===========================================================================
  // Indexed (dependent) cases
  // ===========================================================================

  /**
   * Dependent cases for indexed inductive types.
   *
   * Algorithm overview:
   * 1. Walk each constructor type to extract ALL params and result indices
   * 2. Match constructor result indices against scrutinee indices:
   *    - Detect impossible branches (conflicting constructor heads)
   *    - Identify ctor params with existing context vars (when scrutinee index is non-Var)
   *    - Determine goal variable substitutions (when scrutinee index is Var)
   * 3. Build branch context with proper de Bruijn remapping
   */
  private applyIndexed(
    engine: TacticEngine,
    goal: MetaVar,
    goalId: string,
    inductiveDef: InductiveDefinition,
    typeArgs: TTKTerm[]
  ): TacticResult {
    const indexPositions = inductiveDef.indexPositions;
    const indexArgs = indexPositions.map(i => typeArgs[i]);

    const branchMetas: Array<{
      id: string;
      ctor: string;
      meta: MetaVar;
      explicitParamNames: string[];
    }> = [];

    for (const ctor of inductiveDef.constructors) {
      const ctorInfo = this.walkCtorType(
        ctor.type, ctor.namedArgMap?.size ?? 0, inductiveDef.name, indexPositions
      );
      if (!ctorInfo) continue;

      const branchResult = this.computeIndexedBranch(
        goal, ctorInfo, indexArgs, typeArgs, inductiveDef.indexPositions, engine.definitions
      );
      if (!branchResult) continue; // Impossible branch

      const branchId = freshMetaName();
      const branchMeta: MetaVar = {
        ctx: branchResult.ctx,
        type: branchResult.goalType,
        solution: undefined,
        caseTag: ctor.name
      };

      branchMetas.push({
        id: branchId,
        ctor: ctor.name,
        meta: branchMeta,
        explicitParamNames: branchResult.explicitParamNames
      });
    }

    const elimTerm = this.buildMatchTerm(this.scrutinee, branchMetas);
    return this.finishApply(engine, goal, goalId, branchMetas, elimTerm);
  }

  /**
   * Walk a constructor type, collecting ALL params (implicit + explicit)
   * and extracting result type index expressions.
   *
   * De Bruijn convention in the result: after walking N binders,
   * Var(0) = last param (innermost), Var(N-1) = first param (outermost).
   */
  private walkCtorType(
    ctorType: TTKTerm,
    numImplicit: number,
    inductiveName: string,
    indexPositions: number[]
  ): {
    allParams: Array<{ name: string; type: TTKTerm; isImplicit: boolean }>;
    resultIndices: TTKTerm[];
    resultAllArgs: TTKTerm[];
    totalParams: number;
  } | null {
    const allParams: Array<{ name: string; type: TTKTerm; isImplicit: boolean }> = [];
    let resultType = ctorType;

    while (resultType.tag === 'Binder' && resultType.binderKind.tag === 'BPi') {
      allParams.push({
        name: resultType.name,
        type: resultType.domain,
        isImplicit: allParams.length < numImplicit
      });
      resultType = resultType.body;
    }

    const resultArgs = this.extractTypeArgs(resultType);
    const resultHead = this.getInductiveTypeName(resultType);
    if (resultHead !== inductiveName) return null;

    const resultIndices = indexPositions.map(i => resultArgs[i]);

    return { allParams, resultIndices, resultAllArgs: resultArgs, totalParams: allParams.length };
  }

  /**
   * Compute the branch context and goal type for an indexed constructor.
   *
   * The algorithm works in phases:
   *
   * Phase 1 (matchIndex): For each index position, recursively match the
   * constructor's result index against the scrutinee's index to produce:
   *   - goalSubstitutions: goal de Bruijn vars to eliminate (scrutinee index was Var)
   *   - ctorParamBindings: ctor params identified with existing expressions
   *
   * Phase 2: Determine which ctor params are "new" (not identified with existing
   * vars) and split them into implicit (placed BEFORE kept entries) and explicit
   * (placed AFTER). This layout ensures kept entry types can reference implicit
   * ctor params via prefix-relative de Bruijn indices.
   *
   * Phase 3: Build variable remaps with new layout [implicit_new, kept, explicit_new]:
   *   - ctorParamRemap: translates ctor-scope de Bruijn to branch-scope
   *   - goalVarRemap: translates old goal-scope de Bruijn to branch-scope
   *
   * Phase 4: Build context with proper type conversions:
   *   - Ctor param types: shift from partial ctor scope → full ctor scope, translate,
   *     then shift to prefix-relative
   *   - Kept entry types: shift from prefix-relative → full old context, remap with
   *     goalVarRemap, then shift to prefix-relative in new context
   *
   * Returns null if the branch is impossible.
   */
  private computeIndexedBranch(
    goal: MetaVar,
    ctorInfo: {
      allParams: Array<{ name: string; type: TTKTerm; isImplicit: boolean }>;
      resultIndices: TTKTerm[];
      resultAllArgs: TTKTerm[];
      totalParams: number;
    },
    scrutineeIndexArgs: TTKTerm[],
    allTypeArgs: TTKTerm[],
    indexPositions: number[],
    definitions: DefinitionsMap
  ): { ctx: TTKContext; goalType: TTKTerm; explicitParamNames: string[] } | null {
    const oldCtxSize = goal.ctx.length;
    const totalCtorParams = ctorInfo.totalParams;

    // Phase 1: Match indices
    const goalSubstitutions = new Map<number, TTKTerm>(); // goal de Bruijn → ctor index expr
    const ctorParamBindings = new Map<number, TTKTerm>(); // ctor de Bruijn → goal-scope expr

    for (let i = 0; i < scrutineeIndexArgs.length; i++) {
      const ok = this.matchIndex(
        ctorInfo.resultIndices[i], scrutineeIndexArgs[i],
        goalSubstitutions, ctorParamBindings, totalCtorParams, definitions
      );
      if (!ok) return null; // Impossible branch
    }

    // Phase 1b: Identify ctor params that correspond to type parameters (non-indices)
    {
      const indexSet = new Set(indexPositions);
      for (let pos = 0; pos < allTypeArgs.length; pos++) {
        if (indexSet.has(pos)) continue;
        const ctorArg = ctorInfo.resultAllArgs[pos];
        if (ctorArg && ctorArg.tag === 'Var' && ctorArg.index < totalCtorParams) {
          if (!ctorParamBindings.has(ctorArg.index)) {
            ctorParamBindings.set(ctorArg.index, allTypeArgs[pos]);
          }
        }
      }
    }

    // Phase 2: Determine eliminated vars and categorize new ctor params
    const eliminatedSet = new Set<number>(); // old context array positions

    if (this.scrutinee.tag === 'Var') {
      eliminatedSet.add(oldCtxSize - 1 - this.scrutinee.index);
    }

    for (const goalVarIdx of goalSubstitutions.keys()) {
      const arrayPos = oldCtxSize - 1 - goalVarIdx;
      if (arrayPos >= 0 && arrayPos < oldCtxSize) {
        eliminatedSet.add(arrayPos);
      }
    }

    // Split new ctor params into implicit (before kept) and explicit (after kept)
    const implicitNewParams: Array<{ ctorIdx: number; param: { name: string; type: TTKTerm; isImplicit: boolean } }> = [];
    const explicitNewParams: Array<{ ctorIdx: number; param: { name: string; type: TTKTerm; isImplicit: boolean } }> = [];

    for (let i = 0; i < ctorInfo.allParams.length; i++) {
      const ctorDeBruijn = totalCtorParams - 1 - i;
      if (!ctorParamBindings.has(ctorDeBruijn)) {
        if (ctorInfo.allParams[i].isImplicit) {
          implicitNewParams.push({ ctorIdx: i, param: ctorInfo.allParams[i] });
        } else {
          explicitNewParams.push({ ctorIdx: i, param: ctorInfo.allParams[i] });
        }
      }
    }

    // Build kept entries
    const keptEntries: Array<{ oldArrayPos: number; entry: { name: string; type: TTKTerm } }> = [];
    for (let i = 0; i < oldCtxSize; i++) {
      if (!eliminatedSet.has(i)) {
        keptEntries.push({ oldArrayPos: i, entry: goal.ctx[i] });
      }
    }

    const numImplicitNew = implicitNewParams.length;
    const numKept = keptEntries.length;
    const numExplicitNew = explicitNewParams.length;
    const newCtxSize = numImplicitNew + numKept + numExplicitNew;

    // New layout: [implicit_new..., kept..., explicit_new...]
    // Array positions:
    //   implicit_new[j] at position j                              (j = 0..numImplicitNew-1)
    //   kept[k]         at position numImplicitNew + k             (k = 0..numKept-1)
    //   explicit_new[e] at position numImplicitNew + numKept + e   (e = 0..numExplicitNew-1)

    // Phase 3: Build de Bruijn remaps

    // 3a: ctorParamRemap for new ctor params (full new-context de Bruijn)
    const ctorParamRemap = new Map<number, TTKTerm>();

    for (let j = 0; j < numImplicitNew; j++) {
      const ctorDeBruijn = totalCtorParams - 1 - implicitNewParams[j].ctorIdx;
      const newArrayPos = j;
      const newDeBruijn = newCtxSize - 1 - newArrayPos;
      ctorParamRemap.set(ctorDeBruijn, { tag: 'Var', index: newDeBruijn });
    }

    for (let e = 0; e < numExplicitNew; e++) {
      const ctorDeBruijn = totalCtorParams - 1 - explicitNewParams[e].ctorIdx;
      const newArrayPos = numImplicitNew + numKept + e;
      const newDeBruijn = newCtxSize - 1 - newArrayPos;
      ctorParamRemap.set(ctorDeBruijn, { tag: 'Var', index: newDeBruijn });
    }

    // 3b: goalVarRemap for kept variables (full new-context de Bruijn)
    const goalVarRemap = new Map<number, TTKTerm>();

    for (let k = 0; k < numKept; k++) {
      const oldArrayPos = keptEntries[k].oldArrayPos;
      const oldDeBruijn = oldCtxSize - 1 - oldArrayPos;
      const newArrayPos = numImplicitNew + k;
      const newDeBruijn = newCtxSize - 1 - newArrayPos;
      goalVarRemap.set(oldDeBruijn, { tag: 'Var', index: newDeBruijn });
    }

    // 3c: Identified ctor params → translate goal-scope binding to branch scope
    for (const [ctorDeBruijn, goalExpr] of ctorParamBindings) {
      const branchExpr = this.remapVars(goalExpr, goalVarRemap);
      ctorParamRemap.set(ctorDeBruijn, branchExpr);
    }

    // 3d: Eliminated goal variables → translate ctor index expressions to branch scope
    for (const [goalVarIdx, ctorIdxExpr] of goalSubstitutions) {
      const translated = this.translateCtorExpr(ctorIdxExpr, ctorParamRemap);
      goalVarRemap.set(goalVarIdx, translated);
    }

    // Phase 4: Build context and remap goal type
    const branchGoalType = this.remapVars(goal.type, goalVarRemap);

    const newCtx: TTKContext = [];

    // Collect all names that will be in context for deconfliction
    const usedNames = new Set<string>();
    // Pre-register kept entry names (these have priority)
    for (const { entry } of keptEntries) {
      usedNames.add(entry.name);
    }

    // 4a: Implicit new ctor params
    for (const { ctorIdx, param } of implicitNewParams) {
      // Param type is in partial ctor scope (ctorIdx binders above).
      // Shift to full ctor scope, then translate to branch scope.
      const fullCtorType = shiftTerm(param.type, totalCtorParams - ctorIdx, 0);
      const translatedType = this.translateCtorExpr(fullCtorType, ctorParamRemap);
      // Convert from full new-context to prefix-relative
      const prefixSize = newCtx.length;
      const typePrefixRelative = prefixSize < newCtxSize
        ? shiftTerm(translatedType, -(newCtxSize - prefixSize), 0)
        : translatedType;
      const baseName = (param.name && param.name !== '_') ? param.name : ('_impl' + newCtx.length);
      const paramName = this.deconflictName(baseName, usedNames);
      newCtx.push({ name: paramName, type: typePrefixRelative });
    }

    // 4b: Kept entries with remapped types
    for (const { oldArrayPos, entry } of keptEntries) {
      // Convert prefix-relative → full old-context
      const shiftToFull = oldCtxSize - oldArrayPos;
      const fullOldType = shiftTerm(entry.type, shiftToFull, 0);
      // Remap from old full-context to new full-context
      const remappedType = this.remapVars(fullOldType, goalVarRemap);
      // Convert new full-context → prefix-relative at current position
      const prefixSize = newCtx.length;
      const typePrefixRelative = prefixSize < newCtxSize
        ? shiftTerm(remappedType, -(newCtxSize - prefixSize), 0)
        : remappedType;
      newCtx.push({ name: entry.name, type: typePrefixRelative });
    }

    // 4c: Explicit new ctor params
    const explicitParamNames: string[] = [];
    for (const { ctorIdx, param } of explicitNewParams) {
      const fullCtorType = shiftTerm(param.type, totalCtorParams - ctorIdx, 0);
      const translatedType = this.translateCtorExpr(fullCtorType, ctorParamRemap);
      const prefixSize = newCtx.length;
      const typePrefixRelative = prefixSize < newCtxSize
        ? shiftTerm(translatedType, -(newCtxSize - prefixSize), 0)
        : translatedType;
      const baseName = (param.name && param.name !== '_') ? param.name : ('_arg' + explicitParamNames.length);
      const paramName = this.deconflictName(baseName, usedNames);
      newCtx.push({ name: paramName, type: typePrefixRelative });
      explicitParamNames.push(paramName);
    }

    return { ctx: newCtx, goalType: branchGoalType, explicitParamNames };
  }

  /**
   * Recursively match a constructor result index against a scrutinee index.
   *
   * Populates:
   * - goalSubs: goal de Bruijn indices to eliminate (when scrutinee index is Var)
   * - ctorBindings: ctor param de Bruijn indices identified with goal-scope exprs
   *
   * Returns false if the branch is impossible (conflicting constructor heads).
   */
  private matchIndex(
    ctorIdx: TTKTerm,
    scrutIdx: TTKTerm,
    goalSubs: Map<number, TTKTerm>,
    ctorBindings: Map<number, TTKTerm>,
    totalCtorParams: number,
    definitions: DefinitionsMap
  ): boolean {
    // Case 1: ctor index is Var (references ctor param) → identify with scrutinee expr
    // This MUST come before the scrutinee Var check so that nested cases
    // correctly identify ctor params with existing context vars.
    if (ctorIdx.tag === 'Var' && ctorIdx.index < totalCtorParams) {
      if (ctorBindings.has(ctorIdx.index)) {
        // Already bound — the same ctor param appears in multiple index positions
        // (e.g., Equal a a has `a` in both positions). Match scrutinee against
        // the already-bound expression instead of rebinding.
        const existingBinding = ctorBindings.get(ctorIdx.index)!;
        // If scrutinee is a Var, eliminate it by substituting with the existing binding
        if (scrutIdx.tag === 'Var') {
          goalSubs.set(scrutIdx.index, existingBinding);
          return true;
        }
        // Otherwise check structural equality (both should match)
        return this.termsEqual(existingBinding, scrutIdx);
      }
      ctorBindings.set(ctorIdx.index, scrutIdx);
      return true;
    }

    // Case 2: scrutinee index is Var → eliminate, substitute with ctor index
    if (scrutIdx.tag === 'Var') {
      goalSubs.set(scrutIdx.index, ctorIdx);
      return true;
    }

    // Case 3: Both are constructor applications → check heads, recurse on args
    const headA = this.getConstructorHead(ctorIdx);
    const headB = this.getConstructorHead(scrutIdx);

    if (headA && headB) {
      if (headA !== headB) {
        const isCtorA = definitions.inductiveNameOfConstructor.has(headA);
        const isCtorB = definitions.inductiveNameOfConstructor.has(headB);
        if (isCtorA && isCtorB) return false; // Impossible branch
      }

      // Same head — recurse on arguments
      const argsA = this.extractAppArgs(ctorIdx);
      const argsB = this.extractAppArgs(scrutIdx);
      if (argsA.length === argsB.length) {
        for (let i = 0; i < argsA.length; i++) {
          if (!this.matchIndex(argsA[i], argsB[i], goalSubs, ctorBindings, totalCtorParams, definitions)) {
            return false;
          }
        }
      }
      return true;
    }

    // Case 4: Same constant
    if (ctorIdx.tag === 'Const' && scrutIdx.tag === 'Const' && ctorIdx.name === scrutIdx.name) {
      return true;
    }

    // Default: assume compatible (type checker will verify)
    return true;
  }

  // ===========================================================================
  // De Bruijn helpers for indexed cases
  // ===========================================================================

  /**
   * Extract the argument list from a nested App chain.
   */
  private extractAppArgs(term: TTKTerm): TTKTerm[] {
    const args: TTKTerm[] = [];
    let current = term;
    while (current.tag === 'App') {
      args.unshift(current.arg);
      current = current.fn;
    }
    return args;
  }

  /**
   * Translate a ctor-scope expression to branch scope using the ctor param remap.
   * Handles nested terms by recursing into App and Binder.
   */
  private translateCtorExpr(term: TTKTerm, ctorParamRemap: Map<number, TTKTerm>): TTKTerm {
    switch (term.tag) {
      case 'Var': {
        const replacement = ctorParamRemap.get(term.index);
        if (replacement) return replacement;
        return term;
      }
      case 'App':
        return {
          tag: 'App',
          fn: this.translateCtorExpr(term.fn, ctorParamRemap),
          arg: this.translateCtorExpr(term.arg, ctorParamRemap)
        };
      case 'Binder': {
        const newDomain = this.translateCtorExpr(term.domain, ctorParamRemap);
        const shiftedRemap = new Map<number, TTKTerm>();
        for (const [k, v] of ctorParamRemap) {
          shiftedRemap.set(k + 1, shiftTerm(v, 1, 0));
        }
        const newBody = this.translateCtorExpr(term.body, shiftedRemap);
        return { ...term, domain: newDomain, body: newBody };
      }
      default:
        return term;
    }
  }

  /**
   * Remap variables in a term from old goal scope to branch scope.
   * Used for translating goal type and kept context entry types.
   */
  private remapVars(term: TTKTerm, remap: Map<number, TTKTerm>): TTKTerm {
    switch (term.tag) {
      case 'Var': {
        const replacement = remap.get(term.index);
        if (replacement) return replacement;
        return term;
      }
      case 'App':
        return {
          tag: 'App',
          fn: this.remapVars(term.fn, remap),
          arg: this.remapVars(term.arg, remap)
        };
      case 'Binder': {
        const newDomain = this.remapVars(term.domain, remap);
        const shiftedRemap = new Map<number, TTKTerm>();
        for (const [k, v] of remap) {
          shiftedRemap.set(k + 1, shiftTerm(v, 1, 0));
        }
        const newBody = this.remapVars(term.body, shiftedRemap);
        return { ...term, domain: newDomain, body: newBody };
      }
      case 'Sort': {
        const newLevel = this.remapVars(term.level, remap);
        if (newLevel === term.level) return term;
        return { tag: 'Sort', level: newLevel };
      }
      default:
        return term;
    }
  }

  /**
   * Ensure a name is unique by appending primes if needed.
   */
  private deconflictName(baseName: string, usedNames: Set<string>): string {
    let name = baseName;
    while (usedNames.has(name)) {
      name = name + "'";
    }
    usedNames.add(name);
    return name;
  }

  /**
   * Shallow structural equality check for terms.
   */
  private termsEqual(a: TTKTerm, b: TTKTerm): boolean {
    if (a.tag !== b.tag) return false;
    switch (a.tag) {
      case 'Var': return a.index === (b as any).index;
      case 'Const': return a.name === (b as any).name;
      case 'App': return this.termsEqual(a.fn, (b as any).fn) && this.termsEqual(a.arg, (b as any).arg);
      default: return false;
    }
  }

  /**
   * Get the constructor head name from a term (if it's a constructor application).
   */
  private getConstructorHead(term: TTKTerm): string | null {
    if (term.tag === 'Const') return term.name;
    if (term.tag === 'App') {
      let head: TTKTerm = term;
      while (head.tag === 'App') head = head.fn;
      if (head.tag === 'Const') return head.name;
    }
    return null;
  }

  // ===========================================================================
  // Common helpers (used by both indexed and non-indexed paths)
  // ===========================================================================

  /**
   * Common finalization: assign eliminator to goal, update engine
   */
  private finishApply(
    engine: TacticEngine,
    goal: MetaVar,
    goalId: string,
    branchMetas: Array<{ id: string; ctor: string; meta: MetaVar; explicitParamNames: string[] }>,
    elimTerm: TTKTerm
  ): TacticResult {
    const newMetaVars = new Map(engine.metaVars);
    newMetaVars.set(goalId, { ...goal, solution: elimTerm });

    for (const { id, meta } of branchMetas) {
      newMetaVars.set(id, meta);
    }

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
  }

  /**
   * Extract inductive type name from a type term
   */
  private getInductiveTypeName(type: TTKTerm): string | null {
    if (type.tag === 'Const') return type.name;
    if (type.tag === 'App') {
      let head: TTKTerm = type;
      while (head.tag === 'App') head = head.fn;
      if (head.tag === 'Const') return head.name;
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
   * Used for non-indexed types only.
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

    for (let i = 0; i < numImplicit; i++) {
      if (currentType.tag === 'Binder' && currentType.binderKind.tag === 'BPi') {
        const arg = typeArgs[i] || { tag: 'Hole', id: '_implicit_' + i };
        currentType = subst(0, arg, currentType.body);
      }
    }

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
   */
  private buildMatchTerm(
    scrutinee: TTKTerm,
    branchMetas: Array<{ id: string; ctor: string; explicitParamNames: string[] }>
  ): TTKTerm {
    const clauses: TTKClause[] = branchMetas.map(({ id, ctor, explicitParamNames }) => {
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
