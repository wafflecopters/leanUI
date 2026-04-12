/**
 * TacticSession — unified tactic execution with trace recording.
 *
 * Wraps TacticEngine + elaboration into a single interface usable by both
 * the compilation pipeline and the interactive proof editor.
 *
 * Immutable: each applyCommand returns a new session.
 */

import { TacticEngine, createInitialEngine } from './tacticsEngine';
import { elaborateTacticArg, tacticCommandToTactic, shouldKeepArgAsName } from './elaborate-tactic-arg';
import { Tactic, UnifiedEquation } from './tactic';
import { RewriteTactic } from './rewrite-tactic';
import { ReflexivityTactic } from './reflexivity-tactic';
import { TacticCommand, TTerm, CaseBranch, allPatternVarNames } from '../compiler/surface';
import { desugarNestedCaseBranch } from '../compiler/case-pattern-desugar';
import { TTKTerm, TTKContext } from '../compiler/kernel';
import { DefinitionsMap, MetaVar } from '../compiler/term';

// ============================================================================
// Trace types
// ============================================================================

export interface TacticStepTrace {
  /** Tactic name (e.g., 'intros', 'exact', 'have'). */
  readonly tacticName: string;
  /** Engine state AFTER this tactic was applied. */
  readonly engineAfter: TacticEngine;
  /** Focused goal ID after this step. */
  readonly goalId: string;
  /** Error message if the tactic failed. */
  readonly error?: string;
  /** Branch nesting path for case branches (e.g., ['Left'], ['Right', 'Succ']). */
  readonly branchPath: readonly string[];
  /** For rewrite tactics: the unified equation (lhs = rhs) with implicit args filled in. */
  readonly unifiedEquation?: UnifiedEquation;
}

// ============================================================================
// TacticSession
// ============================================================================

export class TacticSession {
  constructor(
    readonly engine: TacticEngine,
    readonly definitions: DefinitionsMap,
    readonly trace: readonly TacticStepTrace[],
  ) {}

  /** Create a session from an existing engine (e.g., for continuing from a checkpoint). */
  static fromEngine(engine: TacticEngine, definitions: DefinitionsMap): TacticSession {
    return new TacticSession(engine, definitions, []);
  }

  /** Create a fresh session from a goal type. */
  static create(
    goalType: TTKTerm,
    definitions: DefinitionsMap,
    context: TTKContext = [],
  ): TacticSession {
    return new TacticSession(
      createInitialEngine(goalType, context, definitions),
      definitions,
      [],
    );
  }

  /** Focused goal, or null if proof is complete. */
  get goal(): MetaVar | null {
    return this.engine.getFocusedGoal();
  }

  /** Focused goal ID, or null if proof is complete. */
  get goalId(): string | null {
    return this.engine.getFocusedGoalId();
  }

  /** Whether all goals are solved. */
  get isComplete(): boolean {
    return this.engine.isComplete();
  }

  /**
   * Apply a single tactic command. Returns a new session with updated
   * engine and an appended trace entry.
   *
   * Handles elaboration of arguments, focused tactics (bullets),
   * and case branches internally.
   */
  applyCommand(cmd: TacticCommand, branchPath: readonly string[] = []): TacticSession {
    const goal = this.engine.getFocusedGoal();
    const goalId = this.engine.getFocusedGoalId();
    if (!goal || !goalId) return this;

    // 1. Elaborate arguments in the current goal's context
    const elabArgs: Array<TTerm | TTKTerm> = cmd.args.map((arg, i) => {
      if (shouldKeepArgAsName(cmd.name, i, cmd.args.length)) return arg;
      return elaborateTacticArg(arg, goal.ctx, this.definitions);
    });

    // 2. Handle focused tactics (bullet points, suffices closing)
    let focusedTactics: Tactic[] | undefined;
    if (cmd.focusedTactics && cmd.focusedTactics.length > 0) {
      const sufficesHypName = cmd.name === 'suffices' && cmd.args.length >= 1 && cmd.args[0].tag === 'Const'
        ? (cmd.args[0] as any).name as string
        : undefined;
      const focusedCtx = sufficesHypName
        ? [...goal.ctx, { name: sufficesHypName, type: { tag: 'Hole' as const, id: '_suffices_type' } }]
        : goal.ctx;

      focusedTactics = [];
      for (const ft of cmd.focusedTactics) {
        const ftArgs: Array<TTerm | TTKTerm> = ft.args.map((arg, i) => {
          if (shouldKeepArgAsName(ft.name, i, ft.args.length)) return arg;
          return elaborateTacticArg(arg, focusedCtx, this.definitions);
        });
        const t = tacticCommandToTactic({ name: ft.name, args: ftArgs });
        if (t === 'sorry') {
          // sorry in focused tactics — push a no-op
          focusedTactics.push({ name: 'sorry', apply: (eng) => ({ success: true, newEngine: eng }) } as Tactic);
        } else {
          focusedTactics.push(t);
        }
      }
    }

    // 3. Create tactic
    const tactic = tacticCommandToTactic({ name: cmd.name, args: elabArgs, focusedTactics });
    if (tactic === 'sorry') {
      return new TacticSession(this.engine, this.definitions, [
        ...this.trace,
        { tacticName: 'sorry', engineAfter: this.engine, goalId, error: undefined, branchPath },
      ]);
    }

    // 3b. For rw/erw: expand into per-rewrite trace entries so the proof tree
    //     (which has one rewrite node per arg) aligns 1:1 with trace entries.
    //     The TacticSequence applies all rewrites + reflexivity as one unit,
    //     but we need individual engine states for intermediate goal rendering.
    if ((cmd.name === 'erw' || cmd.name === 'rw') && elabArgs.length > 0) {
      return this.applyRewriteChain(elabArgs as TTKTerm[], cmd.name === 'erw', branchPath);
    }

    // 4. Apply
    const result = tactic.apply(this.engine, goal, goalId);
    const newEngine = result.success ? result.newEngine! : this.engine;
    const newGoalId = newEngine.getFocusedGoalId() ?? goalId;

    const entry: TacticStepTrace = {
      tacticName: cmd.name,
      engineAfter: newEngine,
      goalId: newGoalId,
      error: result.success ? undefined : result.error,
      branchPath,
      unifiedEquation: result.success ? result.unifiedEquation : undefined,
    };

    let session = new TacticSession(newEngine, this.definitions, [...this.trace, entry]);

    // 5. Handle case branches (cases/induction with structured branches)
    if (result.success && cmd.caseBranches && cmd.caseBranches.length > 0) {
      session = session.applyCaseBranches(cmd.caseBranches, branchPath, goal.ctx);
    }

    return session;
  }

  /**
   * Expand rw/erw into per-rewrite trace entries.
   * Each rewrite arg gets its own trace entry with the engine state AFTER that
   * individual rewrite, plus the unifiedEquation from that step.
   * This aligns 1:1 with the proof tree (which has one rewrite node per arg).
   */
  private applyRewriteChain(
    elabArgs: TTKTerm[],
    enhanced: boolean,
    branchPath: readonly string[],
  ): TacticSession {
    let currentEngine = this.engine;
    const newTrace = [...this.trace];

    for (const arg of elabArgs) {
      const goal = currentEngine.getFocusedGoal();
      const goalId = currentEngine.getFocusedGoalId();
      if (!goal || !goalId) {
        // No more goals — emit error entry for remaining rewrites
        newTrace.push({
          tacticName: enhanced ? 'erw' : 'rw',
          engineAfter: currentEngine,
          goalId: goalId ?? '',
          error: 'no focused goal',
          branchPath,
        });
        continue;
      }

      const tactic = new RewriteTactic(arg, { enhanced });
      const result = tactic.apply(currentEngine, goal, goalId);
      const nextEngine = result.success ? result.newEngine! : currentEngine;
      const nextGoalId = nextEngine.getFocusedGoalId() ?? goalId;

      newTrace.push({
        tacticName: enhanced ? 'erw' : 'rw',
        engineAfter: nextEngine,
        goalId: nextGoalId,
        error: result.success ? undefined : result.error,
        branchPath,
        unifiedEquation: result.success ? result.unifiedEquation : undefined,
      });

      currentEngine = nextEngine;
    }

    // Apply the closing reflexivity tactic (doesn't need a trace entry —
    // it corresponds to no proof tree node)
    {
      const goal = currentEngine.getFocusedGoal();
      const goalId = currentEngine.getFocusedGoalId();
      if (goal && goalId) {
        const refl = new ReflexivityTactic();
        const result = refl.apply(currentEngine, goal, goalId);
        if (result.success) {
          currentEngine = result.newEngine;
        }
      }
    }

    return new TacticSession(currentEngine, this.definitions, newTrace);
  }

  /**
   * Apply a sequence of tactic commands.
   */
  applyCommands(cmds: readonly TacticCommand[], branchPath: readonly string[] = []): TacticSession {
    let session: TacticSession = this;
    for (const cmd of cmds) {
      session = session.applyCommand(cmd, branchPath);
    }
    return session;
  }

  // ============================================================================
  // Case branch handling
  // ============================================================================

  private applyCaseBranches(
    branches: readonly CaseBranch[],
    parentPath: readonly string[],
    _parentCtx: TTKContext,
    outerParamNameMap?: Map<string, string>,
  ): TacticSession {
    let session: TacticSession = this;

    for (const rawBranch of branches) {
      // Desugar nested constructor patterns into sequential `cases` calls.
      // After this, `branch.params` is guaranteed to be flat (all `tag: 'var'`).
      const branch = desugarNestedCaseBranch(rawBranch);
      const branchPath = [...parentPath, branch.constructor];

      // Find goal with matching caseTag
      const engine = session.engine;
      const matchIdx = engine.goals.findIndex(gid => {
        const meta = engine.metaVars.get(gid);
        return meta?.caseTag === branch.constructor;
      });
      if (matchIdx < 0) continue;

      // Focus on the branch goal
      const focused = engine.withUpdates({ focusIndex: matchIdx });
      const branchGoal = focused.getFocusedGoal();
      if (!branchGoal) continue;

      // After desugarNestedCaseBranch, branch.params is flat (all tag: 'var').
      const branchParamNames = allPatternVarNames(branch.params);

      // Rename the newly-added context entries (the last N) from the
      // constructor's field names (fst, snd, fst1, ...) to the user's
      // pattern names (δF, posF, boundF, ...). De Bruijn indices are
      // position-based, so renaming is purely cosmetic at the kernel
      // level — but it makes the hypothesis panel and downstream
      // elaboration see the names the user actually wrote.
      const renamedEngine = renameLastCtxEntries(focused, branchParamNames);
      const renamedGoal = renamedEngine.getFocusedGoal() ?? branchGoal;

      // Build param name mapping — after renaming it's effectively identity
      // for this branch's own params. Still propagate outerParamNameMap so
      // nested cases under this branch can look up names from enclosing
      // scopes (for parts of the code that may bypass the ctx rename).
      const paramNameMap = new Map<string, string>(outerParamNameMap);
      const renamedCtxNames = renamedGoal.ctx.map(b => b.name);
      for (let i = 0; i < branchParamNames.length; i++) {
        const patternParamName = branchParamNames[i];
        const ctxIndex = renamedCtxNames.length - branchParamNames.length + i;
        if (ctxIndex >= 0 && ctxIndex < renamedCtxNames.length) {
          paramNameMap.set(patternParamName, renamedCtxNames[ctxIndex]);
        }
      }

      // Apply branch tactics with param name mapping
      let branchSession = new TacticSession(renamedEngine, this.definitions, session.trace);
      for (const branchTactic of branch.tactics) {
        const branchGoalNow = branchSession.engine.getFocusedGoal();
        if (!branchGoalNow) break;

        // Elaborate with param name mapping
        const branchElabArgs: Array<TTerm | TTKTerm> = branchTactic.args.map((arg, i) => {
          if (shouldKeepArgAsName(branchTactic.name, i, branchTactic.args.length)) return arg;
          return elaborateTacticArg(arg, branchGoalNow.ctx, this.definitions, 0, paramNameMap);
        });

        const t = tacticCommandToTactic({ name: branchTactic.name, args: branchElabArgs });
        if (t === 'sorry') {
          branchSession = new TacticSession(branchSession.engine, this.definitions, [
            ...branchSession.trace,
            { tacticName: 'sorry', engineAfter: branchSession.engine, goalId: branchSession.goalId ?? '', branchPath, error: undefined },
          ]);
          continue;
        }

        const branchGoalId = branchSession.engine.getFocusedGoalId();
        if (!branchGoalId) break;

        const branchResult = t.apply(branchSession.engine, branchGoalNow, branchGoalId);
        const newEngine = branchResult.success ? branchResult.newEngine! : branchSession.engine;
        const newGoalId = newEngine.getFocusedGoalId() ?? branchGoalId;

        branchSession = new TacticSession(newEngine, this.definitions, [
          ...branchSession.trace,
          {
            tacticName: branchTactic.name,
            engineAfter: newEngine,
            goalId: newGoalId,
            error: branchResult.success ? undefined : branchResult.error,
            branchPath,
          },
        ]);

        // Handle nested case branches
        if (branchResult.success && branchTactic.caseBranches && branchTactic.caseBranches.length > 0) {
          branchSession = branchSession.applyCaseBranches(branchTactic.caseBranches, branchPath, branchGoalNow.ctx, paramNameMap);
        }
      }

      session = new TacticSession(branchSession.engine, this.definitions, branchSession.trace);
    }

    return session;
  }
}

// ============================================================================
// Context entry renaming
// ============================================================================

/**
 * Rename the last `userNames.length` entries of the focused goal's context
 * to use the user-provided pattern names. Returns a new engine whose focused
 * meta has the renamed context; all other metas are preserved.
 *
 * Deconflicts against earlier context entries (before the rename window) by
 * appending a numeric suffix — e.g., if the outer context already has `n`
 * and the user's pattern also writes `n`, the new entry becomes `n1`. Entries
 * within the rename window may shadow each other freely; later wins.
 *
 * Kernel semantics are unaffected: de Bruijn indices in types reference ctx
 * entries by position, not by name, so this is purely a display-layer change
 * that also lets name-based elaboration (see elaborateTacticArg) resolve the
 * user's pattern names without going through a separate paramNameMap.
 */
export function renameLastCtxEntries(
  engine: TacticEngine,
  userNames: readonly string[],
): TacticEngine {
  if (userNames.length === 0) return engine;
  const goalId = engine.getFocusedGoalId();
  const goal = engine.getFocusedGoal();
  if (!goalId || !goal) return engine;

  const ctx = goal.ctx;
  const startIdx = ctx.length - userNames.length;
  if (startIdx < 0) return engine;

  // Names reserved by entries OUTSIDE the rename window — deconflict against these.
  const reserved = new Set<string>();
  for (let i = 0; i < startIdx; i++) reserved.add(ctx[i].name);

  const renamedCtx: typeof ctx = ctx.map((entry, i) => {
    if (i < startIdx) return entry;
    let desired = userNames[i - startIdx];
    if (reserved.has(desired)) {
      let suffix = 1;
      while (reserved.has(desired + suffix)) suffix++;
      desired = desired + suffix;
    }
    // Entries within the window may themselves be reserved-against for
    // subsequent renames (so two `n`s in one pattern get distinct names).
    reserved.add(desired);
    return { ...entry, name: desired };
  });

  const renamedGoal: MetaVar = { ...goal, ctx: renamedCtx };
  const newMetaVars = new Map(engine.metaVars);
  newMetaVars.set(goalId, renamedGoal);
  return engine.withUpdates({ metaVars: newMetaVars });
}
