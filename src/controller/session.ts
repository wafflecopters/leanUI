/**
 * `ProofSession` — the proof editor, without a user interface.
 *
 * Everything semantic about editing one declaration's proof lives here: where
 * the cursor is, what Lean says the goal is, which tactics are worth trying,
 * which of them actually work, what each would do to the goal, and what happens
 * when you take one. The React panel, the headless REPL and the test suite are
 * all just callers.
 *
 * Two properties make that possible, and both are deliberate:
 *
 *   - **Lean arrives through an injected `LeanAnalyzer`.** Nothing here calls
 *     `fetch` or spawns a process, so the same session runs in a browser,
 *     under Node against real Lean, or against a scripted fake in a unit test.
 *
 *   - **Every round-trip is awaitable.** `await session.refresh()` settles;
 *     there is no "wait for the spinner" anywhere. Tests assert on state, not
 *     on timing.
 *
 * The state a caller reads (`getState()`) is plain serializable data, including
 * `actions` — the explicit list of moves available right now. That list is the
 * contract a UI renders and an agent chooses from.
 */
import {
  createHistory,
  clearNode,
  findNode,
  linearize,
  mkCase,
  mkHole,
  pushState,
  redo as redoHistory,
  replaceNode,
  undo as undoHistory,
  updateCurrent,
  withRewriteSideGoals,
  type ProofNode,
  type ProofNodeId,
  type ProofTreeHistory,
} from '../proof-tree/proof-tree';
import { findFirstHole } from '../proof-tree/tactic-to-tree';
import {
  applyManualProofTreeTactic,
  type ProofTreeManualTacticMode,
} from '../proof-tree/tactic-editing';
import type { NodeGoalInfo, TypedProofContext } from '../proof-tree/goal-types';
import type { LeanDeclaration, LeanGoalState } from '../lean/types';
import { leanTacticsToTree } from '../lean/leanTacticsToTree';
import { proofSeedBlock } from '../lean/extractTacticBlock';
import { assembleProofInSource } from '../lean/assembleProofDecl';
import { appliedExprWithHoles, parseSlots, type ParsedSlots } from '../lean/termSlots';
import { spliceTacticBlock } from '../lean/spliceTacticBlock';
import { proofTreeToLean, proofTreeToSource } from '../lean/proofTreeToLean';
import { applySubgoalCount, rewriteSideGoalCount, unfoldableDefs } from '../lean/rewriteCandidates';
import {
  subtermTextMap,
  taggedText,
  posForGoalId,
  goalIdForPos,
  subtermLatexAtPos,
} from '../lean/leanInteractiveGoal';
import { taggedToLatex } from '../lean/codeWithInfos';
import { enrichInductionCaseNames } from '../lean/enrichInductionCases';
import { orderApplyBranches } from '../lean/orderApplyBranches';
import type { LeanSuggestion } from '../lean/leanSuggestions';
import { ACTION, availableActions, checkArgs, findAction, type ActionChoices } from './actions';
import type { LeanAnalyzer } from './analyzer';
import { PROBE_NAME, tacticCandidates } from './candidates';
import { discoverSuggestions, narrowSimpLemmas } from './discover';
import { goalRoundTrip } from './goals';
import { proofOutline } from './outline';
import type {
  ActionDescriptor,
  DispatchResult,
  GoalView,
  HypothesisView,
  ProofDiagnostic,
  SessionAction,
  SessionState,
  SubtermSelection,
} from './types';
import { dedupeByLabel, validateSuggestions, type CancelToken } from './validate';

export interface ProofSessionOptions {
  analyze: LeanAnalyzer;
  /** The full Lean source file. */
  source: string;
  /** Every declaration in the file (the lemma library + the decl to prove). */
  declarations: readonly LeanDeclaration[];
  /** Which declaration to prove. */
  declName: string;
  mathlib?: boolean;
  /**
   * Debounce and run the round-trips automatically after every mutation. On for
   * interactive callers, OFF for tests and the REPL, which call `refresh()`
   * explicitly so their assertions never race a timer.
   */
  autoRefresh?: boolean;
  /** Debounce for auto-refresh, ms. */
  refreshDelayMs?: number;
  /** Max concurrent suggestion trials. */
  concurrency?: number;
  /** Called with the full file text whenever a structural edit changes the
   *  printed proof — the write-back hook. */
  onSourceChange?: (next: string) => void;
}

/** Manual tactic ids the session accepts (`tactic.<id>`). */
const MANUAL_TACTICS = new Set<ProofTreeManualTacticMode['tactic']>([
  'intros', 'induction', 'exact', 'unfold', 'fold', 'rewrite', 'rewrite_rev', 'apply', 'simp', 'have',
]);

export class ProofSessionError extends Error {}

export class ProofSession {
  private readonly opts: ProofSessionOptions;
  private source: string;
  private decl: LeanDeclaration;
  private declarations: readonly LeanDeclaration[];
  private history: ProofTreeHistory;
  /** The seed the tree was built from — write-back only fires on a real change. */
  private seedBlock: string;

  private selectedPath: string | null = null;
  private selectedHyp: string | null = null;

  // Lean's last word, and which state it described.
  private goalMap = new Map<ProofNodeId, NodeGoalInfo>();
  private goalTexts = new Map<ProofNodeId, string>();
  /** Lean's goal state per node, so the cursor can move between refreshes
   *  without the goal panel going stale. */
  private goalStates = new Map<ProofNodeId, LeanGoalState>();
  private typedContext: TypedProofContext | null = null;
  private cursorGoal: LeanGoalState | null = null;
  private diagnostics: ProofDiagnostic[] = [];
  private suggestions: LeanSuggestion[] = [];
  private lastError: string | undefined;
  /** Holes Lean reported NO goal at — the fabricated continuations of tactics
   *  that already closed their goal. Only these may be dropped on write-back. */
  private closedHoles: ReadonlySet<ProofNodeId> = new Set();
  /** The proof text last written to the file, so write-back fires exactly when
   *  the file would actually change. */
  private lastPrinted: string;
  /** Memoized `getState()`; null means "rebuild on next read". */
  private cachedState: SessionState | null = null;
  /** Id of the node the last `insertTactic` produced, so a follow-up probe can
   *  find the step it belongs to after the tree has changed. */
  private lastInsertedId: ProofNodeId | null = null;

  private goalsBusy = false;
  private suggestionsBusy = false;
  /** True once Lean has successfully answered for the CURRENT proof. Without
   *  it, "no open goals" is indistinguishable from "we never asked" — and a
   *  session whose bridge is down would report a finished proof. */
  private goalsFresh = false;
  /** Bumped by every mutation; a round-trip whose epoch is stale is discarded. */
  private epoch = 0;
  private listeners = new Set<(state: SessionState) => void>();
  private refreshTimer: ReturnType<typeof setTimeout> | null = null;
  private disposed = false;
  /** The in-flight suggestion run, so a change can stop it mid-batch instead of
   *  paying for trials whose answers are already irrelevant. */
  private suggestionRun: CancelToken | null = null;

  private constructor(opts: ProofSessionOptions, decl: LeanDeclaration, seedBlock: string) {
    this.opts = opts;
    this.source = opts.source;
    this.declarations = opts.declarations;
    this.decl = decl;
    this.seedBlock = seedBlock;
    const root = leanTacticsToTree(seedBlock);
    const firstHole = findFirstHole(root);
    this.history = createHistory({ root, cursor: { nodeId: firstHole?.id ?? root.id } });
    this.lastPrinted = this.proofSource();
  }

  /**
   * Open a session on a declaration. Throws when the declaration isn't in the
   * file or has no interactive proof body (an inductive, an axiom, a plain
   * computational `def`) — those are edited, not proved.
   */
  static open(opts: ProofSessionOptions): ProofSession {
    const decl = opts.declarations.find((d) => d.name === opts.declName);
    if (!decl) throw new ProofSessionError(`no declaration named "${opts.declName}" in this file`);
    const seed = proofSeedBlock(opts.source, decl, nextDeclLineOf(opts.declarations, decl));
    if (seed === null) {
      throw new ProofSessionError(`"${opts.declName}" (${decl.kind}) has no interactive proof body`);
    }
    return new ProofSession(opts, decl, seed);
  }

  // ── Reading ────────────────────────────────────────────────────────────────

  get declaration(): LeanDeclaration {
    return this.decl;
  }

  /**
   * The proof block as it would be written into the file.
   *
   * Holes Lean reports NO goal at are the parser's fabricated continuations
   * (a `simp` that closed the goal) and are dropped; every other hole writes
   * its `sorry`, so an unfinished proof leaves warnings rather than errors.
   */
  proofSource(): string {
    return proofTreeToSource(this.history.current.root, 1, { closedHoles: this.closedHoles });
  }

  /** The whole file, with this session's proof spliced in. */
  fullSource(): string {
    return spliceTacticBlock(this.source, this.decl, this.nextDeclLine(), this.proofSource());
  }

  /** The proof tree (for the React editor, which renders it directly). */
  get proof(): ProofNode {
    return this.history.current.root;
  }

  get cursorId(): ProofNodeId {
    return this.history.current.cursor.nodeId;
  }

  /** Lean's per-node goal map (the React editor's `goalMapOverride`). */
  get leanGoalMap(): Map<ProofNodeId, NodeGoalInfo> {
    return this.goalMap;
  }

  get leanTypedContext(): TypedProofContext | null {
    return this.typedContext;
  }

  /** The cursor's raw Lean goal state — for renderers that need the tagged tree. */
  get leanCursorGoal(): LeanGoalState | null {
    return this.cursorGoal;
  }

  /**
   * The current state. Cached and invalidated on change, so React can use it
   * as a `useSyncExternalStore` snapshot — an object rebuilt on every read
   * would compare unequal forever and re-render without end.
   */
  getState(): SessionState {
    if (!this.cachedState) this.cachedState = this.buildState();
    return this.cachedState;
  }

  /** Invalidate the cached state. Every mutation goes through here. */
  private touch(): void {
    this.cachedState = null;
  }

  private buildState(): SessionState {
    const cursorNode = findNode(this.proof, this.cursorId);
    const isHole = cursorNode?.tag === 'hole';
    const goal = this.goalView();
    const outline = proofOutline(this.proof, this.cursorId, this.goalMap, this.goalTexts);
    const partial = {
      cursor: { nodeId: this.cursorId, tag: cursorNode?.tag ?? ('hole' as const), isHole },
      goal,
      suggestions: this.suggestions,
      selection: { subterm: this.subtermSelection(), hypothesis: this.selectedHyp },
      history: {
        canUndo: this.history.undoStack.length > 0,
        canRedo: this.history.redoStack.length > 0,
      },
      outline,
    };
    const actions = availableActions(partial, this.actionChoices());
    let openGoals = 0;
    countOpen(outline, () => openGoals++);
    return {
      decl: {
        name: this.decl.name,
        kind: this.decl.kind,
        line: this.decl.line,
        typeText: this.decl.prettyType,
      },
      ...partial,
      actions,
      status: {
        openGoals,
        // "Complete" is a claim about what Lean checked, so it requires that
        // Lean actually answered for THIS proof.
        complete:
          this.goalsFresh &&
          openGoals === 0 &&
          !this.diagnostics.some((d) => d.severity === 'error'),
        diagnostics: this.diagnostics,
      },
      busy: { goals: this.goalsBusy, suggestions: this.suggestionsBusy },
      proofSource: this.proofSource(),
      ...(this.lastError ? { error: this.lastError } : {}),
    };
  }

  subscribe(listener: (state: SessionState) => void): () => void {
    this.listeners.add(listener);
    return () => this.listeners.delete(listener);
  }

  dispose(): void {
    this.disposed = true;
    if (this.refreshTimer) clearTimeout(this.refreshTimer);
    this.refreshTimer = null;
    this.listeners.clear();
  }

  // ── Lean round-trips ───────────────────────────────────────────────────────

  /** Read Lean's goals for the current proof. */
  async refreshGoals(): Promise<void> {
    const epoch = this.epoch;
    this.goalsBusy = true;
    this.emit();
    const result = await goalRoundTrip({
      analyze: this.opts.analyze,
      source: this.source,
      declLine: this.decl.line,
      nextDeclLine: this.nextDeclLine(),
      proof: this.proof,
      cursorId: this.cursorId,
      mathlib: this.opts.mathlib,
    });
    if (this.disposed || epoch !== this.epoch) return;

    this.goalMap = result.goalMap;
    this.goalTexts = result.goalTexts;
    this.goalStates = result.goalStates;
    this.typedContext = result.typedContext;
    this.cursorGoal = result.cursorGoal;
    this.lastError = result.error;
    this.diagnostics = this.attributeDiagnostics(result.messages);
    this.goalsBusy = false;
    this.goalsFresh = result.error === undefined;
    // Which holes are FABRICATED continuations (Lean reports no goal there)
    // rather than real obligations. Only meaningful once Lean has answered.
    if (this.goalsFresh) {
      const closed = new Set<ProofNodeId>();
      for (const id of allHoleIds(this.proof)) if (!result.goalTexts.has(id)) closed.add(id);
      this.closedHoles = closed;
    }

    // Bake Lean's real case names into bullet inductions, so the proof reprints
    // as `induction n with | zero => … | succ a a_ih => …` instead of carrying
    // Lean's INACCESSIBLE `a✝` daggers. Idempotent — already-named cases are
    // left alone, so this settles after one pass.
    // Not an undo point: the user didn't do this, Lean just told us the real
    // names. It does change the printed proof, so it must reach the file.
    const enriched = enrichInductionCaseNames(this.proof, this.goalMap);
    if (enriched.changed) {
      this.history = updateCurrent(this.history, {
        root: enriched.root,
        cursor: this.history.current.cursor,
      });
    }
    // Same idea, second normalization: now that Lean has named the branches of
    // a multi-goal `apply`, put the one that supplies a value first — the
    // midpoint of a transitivity is chosen before anything can be said about
    // it. `case <tag> =>` selects by name, so the branches may be presented in
    // any order.
    const ordered = orderApplyBranches({
      root: this.proof,
      goalMap: this.goalMap,
      goalTexts: this.goalTexts,
      cursorId: this.cursorId,
    });
    if (ordered.changed) {
      this.history = updateCurrent(this.history, {
        root: ordered.root,
        cursor: { nodeId: ordered.cursorId },
      });
      // The cursor may have moved onto a different branch — re-point the goal
      // at where it now is, or the panel would describe the step we left.
      this.syncCursorGoal();
    }
    // Learning that a hole is closed changes what gets written (a fabricated
    // continuation drops out), so the file is reconciled after every read.
    this.writeBack();
    this.emit();
  }

  /** Point `cursorGoal`/`typedContext` at whatever the cursor is on now, using
   *  the goal states the last round-trip already delivered. */
  private syncCursorGoal(): void {
    this.cursorGoal = this.goalStates.get(this.cursorId) ?? null;
    const info = this.goalMap.get(this.cursorId);
    this.typedContext = info
      ? {
          hypotheses: info.hypotheses,
          goal: info.goalLatex,
          ...(info.caseLabelLatex ? { caseLabelLatex: info.caseLabelLatex } : {}),
          ...(info.validation ? { validation: info.validation } : {}),
        }
      : null;
  }

  /** Generate, trial and rank the suggestions available at the cursor. */
  async refreshSuggestions(): Promise<void> {
    const epoch = this.epoch;
    const cursorNode = findNode(this.proof, this.cursorId);
    if (cursorNode?.tag !== 'hole' || !this.cursorGoal) {
      this.suggestions = [];
      this.suggestionsBusy = false;
      this.emit();
      return;
    }
    this.suggestionsBusy = true;
    this.suggestions = [];
    this.emit();

    // Stop the previous batch mid-flight; its answers describe a goal or a
    // selection that no longer exists.
    this.cancelSuggestionRun();
    const cancel: CancelToken = { cancelled: false };
    this.suggestionRun = cancel;

    const goal = this.cursorGoal;
    const selection = this.subtermSelection();
    const isValueGoal = this.goalMap.get(this.cursorId)?.isValueType === true;
    const candidates = tacticCandidates({
      declarations: this.declarations,
      currentDeclName: this.decl.name,
      goalText: taggedText(goal.targetTagged),
      hypotheses: this.hypothesesWithTypes(),
      selectedSubtermText: selection?.text ?? '',
      selectedHypName: this.selectedHyp,
      isValueGoal,
    });

    // Two independent sources, merged as they arrive: the file's own lemmas
    // (ranked here) and whatever Lean's `exact?`/`simp?` search turns up. Both
    // go through the SAME validation, so a discovered tactic has to prove
    // itself like any other before it's offered.
    const common = {
      analyze: this.opts.analyze,
      source: this.source,
      declLine: this.decl.line,
      nextDeclLine: this.nextDeclLine(),
      proof: this.proof,
      cursorId: this.cursorId,
      mathlib: this.opts.mathlib,
    };
    let fromFile: LeanSuggestion[] = [];
    let fromLean: LeanSuggestion[] = [];
    const merge = () => {
      if (this.disposed || epoch !== this.epoch) return;
      this.suggestions = dedupeByLabel([...fromFile, ...fromLean]);
      this.emit();
    };
    const validateOpts = {
      ...common,
      focusPos: selection?.pos ?? null,
      focusOriginal: selection ? subtermLatexAtPos(goal.targetTagged, selection.pos) : null,
      goalOriginal: taggedToLatex(goal.targetTagged),
      concurrency: this.opts.concurrency,
      cancel,
    };

    await Promise.all([
      validateSuggestions({
        ...validateOpts,
        candidates,
        onProgress: (partial) => {
          fromFile = partial;
          merge();
        },
      }).then((done) => {
        fromFile = done;
      }),
      // Lean's own search is skipped at a VALUE goal. `exact?` answers "what
      // inhabits ℝ?" with the first term it can build — it offered
      // `f (f (f (f x0))) / f (f (f (f x0)))` — which type-checks, closes the
      // goal, and is not a choice anyone would make. The value list is the
      // honest answer there.
      (isValueGoal ? Promise.resolve([] as LeanSuggestion[]) : discoverSuggestions({ ...common, cancel })).then(async (found) => {
        if (found.length === 0 || cancel.cancelled) return;
        fromLean = await validateSuggestions({
          ...validateOpts,
          candidates: found,
          onProgress: (partial) => {
            fromLean = partial;
            merge();
          },
        });
      }),
    ]);

    if (this.disposed || epoch !== this.epoch) return;
    this.suggestions = dedupeByLabel([...fromFile, ...fromLean]);
    this.suggestionsBusy = false;
    this.emit();
  }

  /**
   * Goals, then suggestions. Settles — nothing is left in flight.
   *
   * A failure anywhere is reported as session state rather than thrown: an
   * unhandled rejection here would leave the busy flags stuck on and the UI
   * spinning forever with nothing to explain why.
   */
  async refresh(): Promise<void> {
    try {
      await this.refreshGoals();
      await this.refreshSuggestions();
    } catch (e) {
      this.goalsBusy = false;
      this.suggestionsBusy = false;
      this.lastError = `proof refresh failed: ${e instanceof Error ? e.message : String(e)}`;
      this.emit();
      throw e;
    }
  }

  // ── Mutations ──────────────────────────────────────────────────────────────

  /** Replace the cursor hole with a tactic, opening a branch per subgoal. */
  insertTactic(tactic: string, subgoals?: number, subgoalTags?: readonly string[]): DispatchResult {
    let replacement: ProofNode;
    try {
      replacement = leanTacticsToTree(tactic);
    } catch (e) {
      return { ok: false, error: `could not parse "${tactic}": ${e instanceof Error ? e.message : String(e)}` };
    }
    if (replacement.tag === 'hole') return { ok: false, error: `"${tactic}" is not a tactic` };

    // A conditional rewrite (a lemma with premises) leaves side goals — attach
    // holes so they show as branches immediately, rather than appearing later
    // when the main goal closes.
    if (replacement.tag === 'rewrite' && !replacement.convPattern && !replacement.sideGoals) {
      const count = rewriteSideGoalCount(this.declarations, replacement.name);
      if (count > 0) replacement = withRewriteSideGoals(replacement, count);
    }
    // A multi-subgoal opener gets one child hole PER subgoal, so every
    // obligation is visible immediately. With tags they print as `case <tag> =>`
    // blocks in DISPLAY order (witness before dependent body).
    if (
      subgoals !== undefined && subgoals > 1 &&
      replacement.tag === 'apply' &&
      replacement.children.length === 1 && replacement.children[0].tag === 'hole'
    ) {
      const children = Array.from({ length: subgoals }, () => mkHole());
      replacement =
        subgoalTags && subgoalTags.length === subgoals
          ? { ...replacement, children, childTags: [...subgoalTags] }
          : { ...replacement, children };
    }
    // Same for a case split (`cases leTotal a b`): it parses with ONE unnamed
    // placeholder case, and Lean's count says how many branches it really
    // opened. Their names arrive separately, from the goal round-trip
    // (`enrichInductionCases`).
    if (
      subgoals !== undefined && subgoals > 1 &&
      replacement.tag === 'induction' &&
      replacement.cases.length === 1 && replacement.cases[0].body.tag === 'hole'
    ) {
      // Left UNNAMED on purpose. Lean's goal tags here are full dotted paths
      // (`eps_delta.mk.mk.left`), and `cases … with | <alt> =>` wants the bare
      // constructor (`left`) — using the tag verbatim makes Lean reject the
      // alternative. `enrichInductionCaseNames` already derives the right name
      // from the same tags on the next round-trip; until then these print as
      // `·` bullets, which Lean accepts.
      const label = replacement.cases[0].label;
      replacement = {
        ...replacement,
        cases: Array.from({ length: subgoals }, () => mkCase(label, mkHole())),
      };
    }

    const newRoot = replaceNode(this.proof, this.cursorId, replacement);
    const nextHole = findFirstHole(newRoot);
    this.lastInsertedId = replacement.id;
    this.commit({ root: newRoot, cursor: { nodeId: nextHole?.id ?? newRoot.id } });
    return { ok: true };
  }

  /** Take a validated suggestion by its `LeanSuggestion.id`. */
  applySuggestion(suggestionId: string): DispatchResult {
    const s = this.suggestions.find((x) => x.id === suggestionId);
    if (!s) return { ok: false, error: `no suggestion "${suggestionId}" at this goal` };

    // The ring-solver candidate offers simp EVERY equality lemma in the file.
    // Insert it immediately so the click feels instant, then ask Lean which
    // lemmas actually fired and rewrite the step to just those — the proof
    // should record what the step depended on, not a wall of names.
    const broad = s.tactic.match(/^simp \[(.+)\]$/);
    const proofBefore = this.proof;
    const holeBefore = this.cursorId;
    const result = this.insertTactic(s.tactic, s.subgoals, s.subgoalTags);
    if (!result.ok || !broad) return result;

    const inserted = this.lastInsertedId;
    const lemmas = broad[1].split(',').map((x) => x.trim()).filter(Boolean);
    void narrowSimpLemmas({
      analyze: this.opts.analyze,
      source: this.source,
      declLine: this.decl.line,
      nextDeclLine: this.nextDeclLine(),
      // Probe against the tree as it was, with `simp?` standing in for the hole.
      proof: proofBefore,
      cursorId: holeBefore,
      lemmas,
      mathlib: this.opts.mathlib,
    })
      .then((fired) => {
        if (this.disposed || !fired?.length || inserted === null) return;
        const node = findNode(this.proof, inserted);
        // Only rewrite if that step is still the simp we inserted — the user
        // may have undone it or moved on while the probe ran.
        if (node?.tag !== 'simp') return;
        this.history = updateCurrent(this.history, {
          root: replaceNode(this.proof, inserted, { ...node, lemmas: fired }),
          cursor: this.history.current.cursor,
        });
        this.writeBack();
        this.emit();
      })
      .catch(() => {});
    return result;
  }

  /** Run one of the manual tactics with a user-supplied argument. */
  runTactic(tactic: ProofTreeManualTacticMode['tactic'], value: string): DispatchResult {
    let next = applyManualProofTreeTactic(this.history.current, { tactic } as ProofTreeManualTacticMode, value, {
      typedContext: this.typedContext,
      // Both counters read the lemma's type out of Lean's declaration list.
      computeApplySubgoalCount: (_root, _cursor, name) =>
        applySubgoalCount(this.declarations, name),
      computeRewriteSideGoalCount: (name) => rewriteSideGoalCount(this.declarations, name),
    });
    if (!next) return { ok: false, error: `${tactic} could not be applied here` };
    // A tactic that CLOSES its goal leaves the cursor on the finished step,
    // where there is nothing to suggest and nothing to do. Advance to the next
    // open goal, exactly as taking a suggestion does — the two paths shouldn't
    // disagree about where you end up.
    const landed = findNode(next.root, next.cursor.nodeId);
    if (landed?.tag !== 'hole') {
      const open = findFirstHole(next.root);
      if (open) next = { ...next, cursor: { nodeId: open.id } };
    }
    this.commit(next);
    return { ok: true };
  }

  /**
   * "Use" a term — introduce `have h := <expr> ?_ ?_ …` with one term hole per
   * argument the expression still needs.
   *
   * The holes are the point: they are what the slot builder fills, and what the
   * prose shows as □ ("since limF.eps_delta □ □"). Inserting the bare
   * expression instead gives an application that is missing its arguments with
   * nothing to say so.
   *
   * Asynchronous because the arity is Lean's answer: we probe the expression to
   * see what it is still missing.
   */
  async useTerm(expr: string): Promise<DispatchResult> {
    const probed = await this.probeTerm(expr);
    if ('error' in probed) return { ok: false, error: probed.error };
    const holes = appliedExprWithHoles(expr, Array(probed.slots.length).fill(null));
    return this.insertTactic(`have ${this.freshHypName()} := ${holes}`);
  }

  /** Revert a step back to an open goal. */
  clearStep(nodeId: ProofNodeId = this.cursorId): DispatchResult {
    const next = clearNode(this.history.current, nodeId);
    if (!next) return { ok: false, error: 'that step is already an open goal' };
    this.commit(next);
    return { ok: true };
  }

  /**
   * The proof-tree history, for a rich editor component that manipulates the
   * tree directly (renaming binders, adding induction cases, collapsing steps —
   * editing gestures the action layer doesn't model as tactics).
   */
  get treeHistory(): ProofTreeHistory {
    return this.history;
  }

  /**
   * Adopt a tree edit made by such an editor. Distinguishes a real structural
   * change (write back, re-run Lean) from a cursor move (no write-back), so
   * clicking around a proof never rewrites the user's file.
   */
  adoptHistory(next: ProofTreeHistory): void {
    const cursorMoved = next.current.cursor.nodeId !== this.cursorId;
    const structural =
      proofTreeToLean(next.current.root, 1, 1).source !== proofTreeToLean(this.proof, 1, 1).source;
    this.history = next;
    if (!structural && !cursorMoved) {
      this.emit();
      return;
    }
    this.afterMutation(structural);
  }

  /** Turn the automatic post-mutation round-trips on or off — the way a UI
   *  gives Lean to the card the user is working on and no others. */
  setAutoRefresh(on: boolean): void {
    (this.opts as { autoRefresh?: boolean }).autoRefresh = on;
    if (on) this.scheduleRefresh();
    else if (this.refreshTimer) {
      clearTimeout(this.refreshTimer);
      this.refreshTimer = null;
    }
  }

  moveCursor(nodeId: ProofNodeId): DispatchResult {
    if (!findNode(this.proof, nodeId)) return { ok: false, error: `no proof step ${nodeId}` };
    // A cursor move is NOT an undo point — undo should step back through proof
    // steps, not through where you happened to be looking.
    this.history = updateCurrent(this.history, { root: this.proof, cursor: { nodeId } });
    this.afterMutation(false);
    return { ok: true };
  }

  /** Move to the next (or previous) hole in proof order, wrapping around. */
  cursorToHole(direction: 1 | -1): DispatchResult {
    const holes = linearize(this.proof)
      .filter((e) => e.kind === 'node')
      .map((e) => findNode(this.proof, e.id))
      .filter((n): n is ProofNode => n?.tag === 'hole');
    if (holes.length === 0) return { ok: false, error: 'the proof has no open goals' };
    const at = holes.findIndex((h) => h.id === this.cursorId);
    const next = holes[(((at === -1 ? 0 : at + direction) % holes.length) + holes.length) % holes.length];
    return this.moveCursor(next.id);
  }

  /** Focus a subterm of the goal by its Lean `SubExpr.Pos` (or its goal-path id). */
  selectSubterm(posOrPath: string | null): DispatchResult {
    if (posOrPath === null) {
      this.selectedPath = null;
      this.invalidateSuggestions();
      return { ok: true };
    }
    const path = posOrPath.startsWith('goal-') ? posOrPath : goalIdForPos(posOrPath);
    if (!this.subtermTexts().has(path)) {
      return { ok: false, error: `no subterm at "${posOrPath}" in this goal` };
    }
    this.selectedPath = path;
    this.invalidateSuggestions();
    return { ok: true };
  }

  selectHypothesis(name: string | null): DispatchResult {
    if (name !== null && !this.hypothesesWithTypes().some((h) => h.name === name)) {
      return { ok: false, error: `no hypothesis "${name}" in scope` };
    }
    this.selectedHyp = name;
    this.invalidateSuggestions();
    return { ok: true };
  }

  undo(): DispatchResult {
    if (this.history.undoStack.length === 0) return { ok: false, error: 'nothing to undo' };
    this.history = undoHistory(this.history);
    this.afterMutation(true);
    return { ok: true };
  }

  redo(): DispatchResult {
    if (this.history.redoStack.length === 0) return { ok: false, error: 'nothing to redo' };
    this.history = redoHistory(this.history);
    this.afterMutation(true);
    return { ok: true };
  }

  /**
   * Adopt a new version of the file — an external edit, or our own write-back
   * after the host re-elaborated it.
   *
   * `declarations` MUST describe `next`: their line numbers are how the session
   * finds its declaration's region. Omit them only when the edit cannot have
   * moved any declaration.
   *
   * The proof tree is re-seeded only when the declaration's proof actually
   * changed — re-seeding mints fresh node ids, which would blank the goal map
   * and flicker the whole view for an edit somewhere else in the file.
   */
  setSource(next: string, declarations?: readonly LeanDeclaration[]): void {
    const previousSource = this.source;
    this.source = next;
    if (declarations) this.declarations = declarations;
    const decl = this.declarations.find((d) => d.name === this.decl.name);
    if (decl) this.decl = decl;

    // The line numbers must describe THIS text. A host that keeps source and
    // declarations in separate state hands us the new source the moment we
    // write it and the matching declarations only when the re-analyze returns —
    // so for a beat we hold new text with stale boundaries. Re-seeding then
    // slices the declaration short and silently drops the tail of the proof
    // (the last branches of the last tactic). Wait for the matching pair.
    if (!this.declarationsDescribe(next)) {
      this.source = previousSource;
      return;
    }

    const seed = proofSeedBlock(this.source, this.decl, this.nextDeclLine());
    if (seed === null) return;
    const printedNow = proofTreeToLean(this.proof, 1, 1).source;
    const printedSeed = proofTreeToLean(leanTacticsToTree(seed), 1, 1).source;
    if (printedNow === printedSeed) return; // our own write-back — keep the tree
    this.seedBlock = seed;
    const root = leanTacticsToTree(seed);
    const hole = findFirstHole(root);
    this.history = createHistory({ root, cursor: { nodeId: hole?.id ?? root.id } });
    this.afterMutation(false);
  }

  /**
   * Do `this.declarations`' line numbers actually describe `source`?
   *
   * Checked at both ends of the declaration's region: its own line must start
   * it, and the next declaration's line (which BOUNDS the region) must start a
   * declaration too. A stale upper bound is the dangerous one — it truncates
   * the proof without any other symptom.
   */
  private declarationsDescribe(source: string): boolean {
    const lines = source.split('\n');
    const startsDecl = (line: string | undefined): boolean =>
      line !== undefined &&
      /^\s*(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |unsafe |partial |scoped |local )*(?:def|theorem|lemma|example|abbrev|instance|structure|inductive|axiom|opaque|class|notation|infix|infixl|infixr|prefix|postfix|macro|syntax|open|namespace|end|section|variable|universe|attribute|deriving|set_option|import)\b/.test(line);

    const own = lines[this.decl.line - 1];
    if (own === undefined) return false;
    // Its own line must start THIS declaration, by name.
    if (!new RegExp(`\\b${this.decl.name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\b`).test(own)) return false;
    if (!startsDecl(own)) return false;

    const next = this.nextDeclLine();
    return next === undefined || startsDecl(lines[next - 1]);
  }

  // ── Dispatch ───────────────────────────────────────────────────────────────

  /**
   * Run an action from `getState().actions` by id. Unknown ids and missing
   * arguments are reported, never silently ignored — a caller that mistypes an
   * action should hear about it.
   */
  dispatch(action: SessionAction): DispatchResult {
    const actions = this.getState().actions;
    const found = findAction(actions, action.id);
    if (!found) return { ok: false, error: `"${action.id}" is not available right now` };
    const bad = checkArgs(found, action.args);
    if (bad) return { ok: false, error: bad };
    return this.perform(found, action.args ?? {});
  }

  private perform(action: ActionDescriptor, args: Record<string, string>): DispatchResult {
    const { id } = action;
    if (id.startsWith(ACTION.suggestion)) {
      return this.applySuggestion(id.slice(ACTION.suggestion.length));
    }
    if (id.startsWith(ACTION.tactic)) {
      const tactic = id.slice(ACTION.tactic.length) as ProofTreeManualTacticMode['tactic'];
      if (!MANUAL_TACTICS.has(tactic)) return { ok: false, error: `unknown tactic "${tactic}"` };
      const value = action.params[0] ? (args[action.params[0].name] ?? '') : '';
      return this.runTactic(tactic, value);
    }
    if (id.startsWith(ACTION.hypothesis)) return this.performHypothesisAction(id, action);
    switch (id) {
      case ACTION.selectSubterm:
        return this.selectSubterm(args.pos);
      case ACTION.selectHypothesis:
        return this.selectHypothesis(args.name);
      case ACTION.clearSelection:
        this.selectSubterm(null);
        return this.selectHypothesis(null);
      case ACTION.cursorNextHole:
        return this.cursorToHole(1);
      case ACTION.cursorPrevHole:
        return this.cursorToHole(-1);
      case ACTION.cursorGoto: {
        const nodeId = Number(args.nodeId);
        if (!Number.isFinite(nodeId)) return { ok: false, error: `"${args.nodeId}" is not a step id` };
        return this.moveCursor(nodeId);
      }
      case ACTION.clearNode:
        return this.clearStep();
      case ACTION.undo:
        return this.undo();
      case ACTION.redo:
        return this.redo();
    }
    return { ok: false, error: `"${id}" has no handler` };
  }

  /** The hypothesis tray: exact / apply / destructure / use a projection. */
  private performHypothesisAction(id: string, action: ActionDescriptor): DispatchResult {
    const rest = id.slice(ACTION.hypothesis.length);
    const sep = rest.indexOf(':');
    const kind = rest.slice(0, sep);
    const target = rest.slice(sep + 1);
    switch (kind) {
      case 'exact':
        return this.insertTactic(`exact ${target}`);
      case 'apply':
        return this.insertTactic(`apply ${target}`, action.detail?.subgoals);
      case 'cases':
        return this.insertTactic(`cases ${target}\n·\n  sorry`);
      case 'use':
        // How many arguments the projection still needs is Lean's answer, so
        // this can't complete synchronously. The click is accepted now and the
        // step appears when the probe lands; `useTerm` is the awaitable form.
        void this.useTerm(target);
        return { ok: true };
    }
    return { ok: false, error: `unknown hypothesis action "${kind}"` };
  }

  // ── Derived views ──────────────────────────────────────────────────────────

  private goalView(): GoalView | null {
    const g = this.cursorGoal;
    if (!g) return null;
    const hypotheses: HypothesisView[] = [];
    for (const h of g.hyps) {
      const type = taggedText(h.type);
      for (const name of h.names) {
        hypotheses.push({ name, text: type, latex: taggedToLatex(h.type), isEquation: /\s=\s/.test(type) });
      }
    }
    const subterms = [...subtermTextMap(g.targetTagged)].flatMap(([path, txt]) => {
      const pos = posForGoalId(path);
      return pos ? [{ pos, text: txt }] : [];
    });
    return {
      ...(g.case ? { case: g.case } : {}),
      hypotheses,
      targetText: taggedText(g.targetTagged),
      targetLatex: taggedToLatex(g.targetTagged),
      targetTagged: g.targetTagged,
      subterms,
    };
  }

  private subtermTexts(): Map<string, string> {
    return this.cursorGoal ? subtermTextMap(this.cursorGoal.targetTagged) : new Map();
  }

  private subtermSelection(): SubtermSelection | null {
    if (!this.selectedPath || !this.cursorGoal) return null;
    const text = this.subtermTexts().get(this.selectedPath);
    const pos = posForGoalId(this.selectedPath);
    if (text === undefined || pos === null) return null;
    return {
      path: this.selectedPath,
      pos,
      text: text.trim(),
      latex: subtermLatexAtPos(this.cursorGoal.targetTagged, pos) ?? '',
    };
  }

  /** Hypotheses flattened to one entry per name, with plain type text. */
  hypothesesWithTypes(): Array<{ name: string; type: string }> {
    return (this.cursorGoal?.hyps ?? []).flatMap((h) =>
      h.names.map((name) => ({ name, type: taggedText(h.type) })),
    );
  }

  /**
   * "What does this term still need?" — elaborate `expr` at the cursor and read
   * back the arguments it is missing.
   *
   * Implemented as a probe: splice `have <probe> := <expr>` at the hole and ask
   * Lean for the probe binder's remaining FUNCTION type; its Pi binders are the
   * open slots. That's how the term builder knows what to ask for, and how a
   * candidate projection is checked before it's offered.
   */
  async probeTerm(expr: string): Promise<ParsedSlots | { error: string }> {
    try {
      const sub = leanTacticsToTree(`have ${PROBE_NAME} := ${expr}`);
      const assembled = assembleProofInSource({
        source: this.source,
        decl: { line: this.decl.line },
        nextDeclLine: this.nextDeclLine(),
        proof: replaceNode(this.proof, this.cursorId, sub),
      });
      const tacticLine = assembled.lean.nodeRanges.get(sub.id)?.startLine;
      const data = await this.opts.analyze({
        source: assembled.source,
        prefix: assembled.prefixSource,
        body: assembled.bodySource,
        mathlib: this.opts.mathlib,
        priority: true,
      });
      if (!data) return { error: 'analyze request failed' };
      const err = data.messages.find((m) => m.severity === 'error' && m.startLine === tacticLine);
      if (err) return { error: err.text.split('\n')[0] };
      const hole = findFirstHole(sub);
      const range = hole ? assembled.lean.nodeRanges.get(hole.id) : undefined;
      const g = range
        ? data.goals.find((x) => x.startLine === range.startLine && x.startCol === range.startCol)
        : undefined;
      const hyp = g?.goals?.[0]?.hyps?.find((h) => h.names.includes(PROBE_NAME));
      if (!hyp) return { error: 'could not read the built term' };
      return parseSlots(taggedText(hyp.type));
    } catch (e) {
      return { error: e instanceof Error ? e.message : String(e) };
    }
  }

  /** Names bound in the cursor's context — for resolving what the user typed. */
  hypothesisNames(): string[] {
    return this.hypothesesWithTypes().map((h) => h.name);
  }

  /** A hypothesis name not already in scope: `h`, then `h1`, `h2`, … */
  freshHypName(): string {
    const taken = new Set(this.hypothesesWithTypes().map((h) => h.name));
    if (!taken.has('h')) return 'h';
    for (let i = 1; ; i++) if (!taken.has(`h${i}`)) return `h${i}`;
  }

  /** Valid argument values for the manual tactics, from the live context. */
  private actionChoices(): ActionChoices {
    return {
      hypotheses: this.hypothesesWithTypes().map((h) => h.name),
      lemmas: this.declarations
        .filter((d) => d.name !== this.decl.name && (d.kind === 'def' || d.kind === 'theorem'))
        .map((d) => d.name),
      definitions: unfoldableDefs(this.declarations, this.decl.name, 50),
    };
  }

  /** Attribute Lean's messages to proof nodes where the goal map already did. */
  private attributeDiagnostics(messages: readonly { severity: string; text: string; startLine: number }[]): ProofDiagnostic[] {
    const byNode = new Map<string, ProofNodeId>();
    for (const [nodeId, info] of this.goalMap) {
      if (info.tacticError) byNode.set(info.tacticError, nodeId);
    }
    const out: ProofDiagnostic[] = [];
    // Only what LEAN SAID ABOUT THIS PROOF. Everything before the declaration
    // belongs to some other part of the file and isn't this session's to report.
    messages = messages.filter((m) => m.startLine >= this.decl.line);
    for (const m of messages) {
      // The file is full of `sorry` warnings from OTHER declarations; only this
      // proof's diagnostics belong in this session's status.
      if (m.severity === 'warning' && /uses 'sorry'/.test(m.text)) continue;
      if (m.severity !== 'error' && m.severity !== 'warning') continue;
      const nodeId = byNode.get(m.text);
      out.push({
        severity: m.severity as ProofDiagnostic['severity'],
        text: m.text,
        ...(nodeId !== undefined ? { nodeId } : {}),
      });
    }
    return out;
  }

  private nextDeclLine(): number | undefined {
    return nextDeclLineOf(this.declarations, this.decl);
  }

  // ── Plumbing ───────────────────────────────────────────────────────────────

  /** Record a new tree state, invalidate Lean's answers, write back, notify. */
  private commit(next: { root: ProofNode; cursor: { nodeId: ProofNodeId } }): void {
    this.history = pushState(this.history, next);
    this.afterMutation(true);
  }

  private cancelSuggestionRun(): void {
    if (this.suggestionRun) this.suggestionRun.cancelled = true;
    this.suggestionRun = null;
  }

  private afterMutation(structural: boolean): void {
    this.epoch++;
    this.cancelSuggestionRun();
    // Lean's previous answers describe a proof that no longer exists. Keep the
    // goal MAP (the outline still renders, one step behind, and the busy flag
    // says so) but drop the suggestions — a pill from the old goal would apply
    // a tactic that was validated somewhere else entirely.
    this.suggestions = [];
    this.goalsFresh = false;
    this.selectedPath = null;
    this.selectedHyp = null;
    if (structural) this.writeBack();
    this.emit();
    this.scheduleRefresh();
  }

  /**
   * A selection change re-ranks the candidates but does NOT change the goal, so
   * the suggestions already validated here are still true and still clickable —
   * they're kept (marked busy) while the new batch is computed. Clearing them
   * would blink the pills away on every click and make `applySuggestion` fail
   * for a suggestion the user can plainly see.
   */
  private invalidateSuggestions(): void {
    this.epoch++;
    this.cancelSuggestionRun();
    this.suggestionsBusy = true;
    this.emit();
    this.scheduleRefresh({ goalsToo: false });
  }

  /**
   * Write the proof into the file — but only when the file text would change,
   * so cursor moves and re-reads never churn the user's editor.
   *
   * `this.source` deliberately stays the BASELINE it was opened with. Splicing
   * grows or shrinks the declaration, but `this.declarations`' line numbers
   * still describe the baseline; adopting our own output as the new source
   * without new line numbers would make the next splice land in the wrong
   * place. The host re-elaborates and calls `setSource` with a matching
   * declaration list — that is the only way the baseline moves.
   */
  private writeBack(): void {
    if (!this.opts.onSourceChange) return;
    const printed = this.proofSource();
    if (printed === this.lastPrinted) return;
    this.lastPrinted = printed;
    this.opts.onSourceChange(this.fullSource());
  }

  private scheduleRefresh(opts: { goalsToo?: boolean } = {}): void {
    if (!this.opts.autoRefresh || this.disposed) return;
    if (this.refreshTimer) clearTimeout(this.refreshTimer);
    this.refreshTimer = setTimeout(() => {
      this.refreshTimer = null;
      void (opts.goalsToo === false ? this.refreshSuggestions() : this.refresh());
    }, this.opts.refreshDelayMs ?? 60);
  }

  private emit(): void {
    this.touch();
    if (this.disposed || this.listeners.size === 0) return;
    const state = this.getState();
    for (const l of this.listeners) l(state);
  }
}

/** Start line of the declaration after `decl` — bounds its source region. */
function nextDeclLineOf(declarations: readonly LeanDeclaration[], decl: LeanDeclaration): number | undefined {
  return [...declarations]
    .map((d) => d.line)
    .sort((a, b) => a - b)
    .find((l) => l > decl.line);
}

function countOpen(node: { status: string; tag: string; children: unknown[] }, tick: () => void): void {
  if (node.tag === 'hole' && node.status === 'open') tick();
  for (const c of node.children as Array<typeof node>) countOpen(c, tick);
}

/** Every hole id in a proof tree. */
function allHoleIds(root: ProofNode): ProofNodeId[] {
  const out: ProofNodeId[] = [];
  const walk = (n: ProofNode): void => {
    if (n.tag === 'hole') out.push(n.id);
    const rec = n as unknown as Record<string, unknown>;
    for (const k of ['child', 'byProof', 'proofTree'] as const) {
      const v = rec[k];
      if (v && typeof v === 'object' && 'tag' in v) walk(v as ProofNode);
    }
    for (const k of ['children', 'steps', 'sideGoals'] as const) {
      const v = rec[k];
      if (Array.isArray(v)) for (const c of v as ProofNode[]) walk(c);
    }
    if (n.tag === 'induction') for (const c of n.cases) walk(c.body);
  };
  walk(root);
  return out;
}
