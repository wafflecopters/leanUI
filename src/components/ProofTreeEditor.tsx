/**
 * ProofTreeEditor — structured proof editor rendered as natural math prose.
 *
 * Each proof is a tree of tactic nodes (intros, induction, exact, hole).
 * State is fully immutable — every action produces a new state.
 * Undo/redo is built on immutable history snapshots.
 *
 * Features:
 * - KaTeX rendering for case labels, intro names, exact expressions
 * - Goal panel showing context + goal at cursor position
 */

import React, { createContext, useCallback, useContext, useEffect, useMemo, useRef, useState } from 'react';
import katex from 'katex';
import { SyntaxRegistry } from '../math-editor/syntax-registry';
import {
  ProofTreeHistory, ProofTreeState, ProofNode, CaseNode, SimpNode, ProofNodeId,
  computeContext,
  applySimp,
  moveCursorUp, moveCursorDown,
  pushState, updateCurrent, undo, redo,
  editHaveExpr,
  findNode,
  mkHave,
  mkHole,
  replaceNode,
} from '../proof-tree/proof-tree';
import type { TypedProofContext, NodeGoalInfo } from '../proof-tree/goal-types';
import { ProseItem, ProseItemKind, IntroToken, CalcChainStep, generateProofProse } from '../proof-tree/proof-prose';
import {
  buildProseGoalLead,
  findLastInteractiveGoalStepIndex,
  findNextHoleNodeId,
  proseItemShowsVisibleGoal,
  visibleLatexLength,
} from '../proof-tree/prose-view-helpers';
import { splitAnonTuple, existsBinderFromLatex,
  describeApplyProse,
  describeExactProse,
  describeInductionHeader,
  describeRewriteReference,
} from '../proof-tree/prose-row-helpers';
import type { InteractiveGoal, GoalPath } from '../proof-tree/interactive-goal-types';
import type { TacticSuggestion } from '../proof-tree/suggestion-types';
import {
  EMPTY_GOAL_INTERACTION_STATE,
  clearGoalInteractionAfterApply,
  clearGoalInteractionForCursorChange,
  selectGoalInteractionBinder,
  selectGoalInteractionPath,
  startGoalInteractionEditing,
  toggleGoalInteractionHypothesis,
  updateGoalInteractionEditingNames,
  type GoalInteractionState,
  type SelectedBinder,
} from '../proof-tree/goal-interaction-state';
import { renderNameLatex, normalizeBinderNameInput } from '../proof-tree/name-latex';
import { exprToLatex } from '../proof-tree/expr-latex';
import type { TermBuilderDisplay, TermBuilderProvider } from '../proof-tree/term-builder-types';
import {
  addInductionCaseInProofTree,
  applyManualProofTreeTactic,
  applySuggestionToProofTreeState,
  clearProofTreeNode,
  commitHaveExprSourceInProofTree,
  commitProofTreeBinderRename,
  convertMathEditorSourceToUnicode,
  removeInductionCaseInProofTree,
  toggleCaseCollapseInProofTree,
  toggleInductionCollapseInProofTree,
  toggleSimpCollapseInProofTree,
  type ProofTreeManualTacticMode,
  updateHaveExprInProofTree,
} from '../proof-tree/tactic-editing';
import { MathEditor, MathEditorHandle } from './MathEditor';
import { convertToSource } from '../math-editor/syntax-registry';
import { InteractiveGoalView } from './InteractiveGoalView';
import SplitPane from './SplitPane';

// Inject spinner keyframes for rewrite progress indicator
if (typeof document !== 'undefined' && !document.getElementById('proof-tree-spinner-style')) {
  const style = document.createElement('style');
  style.id = 'proof-tree-spinner-style';
  style.textContent = '@keyframes spin { to { transform: rotate(360deg); } }';
  document.head.appendChild(style);
}

// ============================================================================
// Props
// ============================================================================

export interface ProofTreeEditorProps {
  history: ProofTreeHistory;
  onHistoryChange: (h: ProofTreeHistory) => void;
  /** Syntax registry for structured math rendering of types/goals */
  registry?: SyntaxRegistry;
  /** Name of the declaration being proved — used to filter self-referential suggestions */
  currentDeclName?: string;
  /**
   * Lean backend overrides. When provided (by the Lean-backed WYSIWYG parent),
   * the editor renders goals from these instead of running the in-process TT
   * engine — the dependency-injection seam for the Lean port. When absent, the
   * legacy TT goal computation runs unchanged.
   */
  goalMapOverride?: Map<ProofNodeId, NodeGoalInfo>;
  typedContextOverride?: TypedProofContext | null;
  /**
   * Lean-built interactive goal (clickable subterms). When provided, it drives
   * the goal panel's InteractiveGoalView instead of the TT kernel rendering.
   */
  interactiveGoalOverride?: InteractiveGoal | null;
  /**
   * Lean subterm-selection seam: when the user clicks a subterm in the goal, the
   * editor reports its path here (instead of running TT suggestion computation),
   * and the parent supplies path-targeted suggestion pills via a render slot.
   */
  onGoalPathSelect?: (path: GoalPath | null) => void;
  /** Extra content rendered under the goal (Lean-backed suggestion pills). */
  goalExtraSlot?: React.ReactNode;
  /** Lean-backed `apply` subgoal-count estimate (the TT kernel isn't available);
   *  its presence also marks the Lean backend (hides TT-only buttons like Fold). */
  applySubgoalCount?: (name: string) => number;
  /** Branches a split on this scrutinee opens — one per constructor of its
   *  type. `null` when nothing in scope knows. */
  caseBranchCount?: (scrutinee: string) => number | null;
  /** Doc comment of a file lemma, for reason-style citations. */
  lemmaDoc?: (name: string) => string | undefined;
  /** The declaration's raw Lean signature — shown above the Tactics tree. */
  declSignature?: string;
  rewriteSideGoalCount?: (name: string) => number;
  /** Lean backend: replaces the kernel-computed hypothesis action tray
   *  (Exact/Apply/Destructure/Use …) shown under a clicked CONTEXT hypothesis. */
  hypSuggestionsOverride?: readonly TacticSuggestion[];
  /** Lean backend: reports which hypothesis is selected in the CONTEXT list. */
  onHypothesisSelect?: (name: string | null) => void;
  /** Lean backend: handle a suggestion before the kernel path; return true if
   *  handled (kernel apply is then skipped). */
  onApplySuggestionOverride?: (s: TacticSuggestion) => boolean;
  /** Lean backend: async engine for the have TERM BUILDER (probe-backed). */
  termBuilderProvider?: TermBuilderProvider;
}

// ============================================================================
// Styles
// ============================================================================

const FONT_MONO = '"JetBrains Mono", "Fira Code", Menlo, Consolas, monospace';
const FONT_UI = '-apple-system, BlinkMacSystemFont, "Segoe UI", Helvetica, Arial, sans-serif';

const containerStyle: React.CSSProperties = {
  outline: 'none',
  fontSize: '13px',
  fontFamily: FONT_UI,
  color: '#c9d1d9',
  lineHeight: '1.6',
  flex: 1,
  minHeight: 0,
  height: '100%',
};

const INITIAL_PANE_SIZES = [
  { size: 65, mode: 'percent' as const },
  { size: 35, mode: 'percent' as const },
];

// ============================================================================
// InlineKaTeX — renders a LaTeX string inline
// ============================================================================

function InlineKaTeX({ latex, style, displayMode }: { latex: string; style?: React.CSSProperties; displayMode?: boolean }) {
  const ref = useRef<HTMLSpanElement>(null);

  useEffect(() => {
    if (!ref.current) return;
    try {
      katex.render(latex, ref.current, {
        displayMode: displayMode ?? false,
        throwOnError: false,
        trust: true,
        strict: false,
      });
    } catch {
      ref.current.textContent = latex;
    }
  }, [latex, displayMode]);

  return <span ref={ref} style={style} />;
}

/** Convert a plain-text Lean expression to LaTeX. The real work lives in
 *  `proof-tree/expr-latex.ts` (pure, tested): tokenizes and sends every
 *  identifier through the same `renderNameLatex` the prose view uses, so
 *  `h2` subscripts, `eps_delta` keeps its underscore instead of becoming a
 *  spurious subscript, multi-char names render upright rather than as an
 *  italic run, and application args are separated by thin spaces. */
function textToLatex(text: string): string {
  return exprToLatex(text);
}

// ============================================================================
// Tactic input state (ephemeral, per-hole)
// ============================================================================

type TacticMode = null | ProofTreeManualTacticMode;

// ============================================================================
// Main Component
// ============================================================================

/** Stable empty list, so memo deps don't churn. */
const EMPTY_SUGGESTIONS: readonly TacticSuggestion[] = [];

export function ProofTreeEditor({ history, onHistoryChange, registry, goalMapOverride, typedContextOverride, interactiveGoalOverride, onGoalPathSelect, goalExtraSlot, applySubgoalCount, caseBranchCount, lemmaDoc, declSignature, rewriteSideGoalCount, hypSuggestionsOverride, onHypothesisSelect, onApplySuggestionOverride, termBuilderProvider }: ProofTreeEditorProps) {
  const containerRef = useRef<HTMLDivElement>(null);
  const state = history.current;

  // Once the user interactively edits the proof tree, the compiled
  // tacticTrace is stale — it was produced for the ORIGINAL proof tree
  // Ephemeral tactic input mode (not part of immutable state)
  const [tacticMode, setTacticMode] = useState<TacticMode>(null);
  const [activeTab, setActiveTab] = useState<'tactics' | 'proof'>('proof');

  // Goal interaction state (shared between GoalPanel and prose view)
  const [goalInteractionState, setGoalInteractionState] = useState<GoalInteractionState>(
    EMPTY_GOAL_INTERACTION_STATE,
  );
  // Lean backend: hypothesis-selection reporting (name resolved once
  // typedContext is available; see the effect after typedContext).
  const pendingHypSelectRef = useRef<number | null | undefined>(undefined);
  const {
    selectedPath: goalSelectedPath,
    selectedBinder,
    selectedHyp,
    editingNames: goalEditingNames,
    editingSuggestionId: goalEditingSuggestionId,
  } = goalInteractionState;

  const handleSelectBinder = useCallback((binder: SelectedBinder | null) => {
    setGoalInteractionState(prev => selectGoalInteractionBinder(prev, binder));
  }, []);

  const handleSelectGoalPath = useCallback((path: GoalPath | null) => {
    setGoalInteractionState(prev => selectGoalInteractionPath(prev, path));
    // Lean backend: report the selected subterm path so the parent can compute
    // path-targeted suggestions (rendered via goalExtraSlot).
    onGoalPathSelect?.(path);
  }, [onGoalPathSelect]);

  const handleToggleHypothesis = useCallback((hypIndex: number) => {
    setGoalInteractionState(prev => {
      const next = toggleGoalInteractionHypothesis(prev, hypIndex);
      // Report the selection to the Lean backend (name resolved by the caller
      // effect below, which sees the fresh typedContext).
      pendingHypSelectRef.current = next.selectedHyp;
      return next;
    });
  }, []);

  const emptyRegistry = useMemo<SyntaxRegistry>(() => ({ symbolMap: new Map(), entries: [] }), []);

  // The context and goal at the cursor, from the Lean round-trip. Falls back to
  // the tree's own structural context (hypothesis NAMES from intro/case nodes,
  // no types) before the first round-trip lands.
  const typedContext = useMemo<TypedProofContext | null>(() => {
    if (typedContextOverride !== undefined) return typedContextOverride;
    const ctx = computeContext(state.root, state.cursor.nodeId);
    if (!ctx) return null;
    return {
      hypotheses: ctx.hypotheses.map(h => ({ name: h.name, type: '' })),
      caseLabel: ctx.caseLabel,
      inductionVar: ctx.inductionVar,
      goal: ctx.goalDescription,
    };
  }, [typedContextOverride, state.root, state.cursor.nodeId]);

  // The clickable goal, rendered from Lean's tagged pretty-print by the parent.
  const interactiveGoal = interactiveGoalOverride ?? null;

  // Suggestions are NOT computed here. The Lean backend proposes candidates and
  // validates each one by trialling it at the real cursor, so only tactics Lean
  // accepts are ever offered; the parent panel passes the survivors in. (The TT
  // path ranked and trialled them in-process — that engine is gone.)
  const goalSuggestions: readonly TacticSuggestion[] = EMPTY_SUGGESTIONS;

  // The hypothesis tray, computed by the panel (validated round-trips).
  const hypSuggestions: readonly TacticSuggestion[] = hypSuggestionsOverride ?? EMPTY_SUGGESTIONS;

  // Report hypothesis selection (by NAME) to the Lean backend.
  useEffect(() => {
    if (pendingHypSelectRef.current === undefined || !onHypothesisSelect) return;
    const idx = pendingHypSelectRef.current;
    pendingHypSelectRef.current = undefined;
    onHypothesisSelect(idx === null ? null : (typedContext?.hypotheses[idx]?.name ?? null));
  });

  // Reset goal selection and binder selection when cursor changes
  useEffect(() => {
    setGoalInteractionState(clearGoalInteractionForCursorChange());
  }, [state.cursor.nodeId]);

  // Per-node goals, from the Lean round-trip (mapLeanGoalsToNodes).
  const goalMap = useMemo<Map<ProofNodeId, NodeGoalInfo>>(
    () => goalMapOverride ?? new Map(),
    [goalMapOverride],
  );

  // Generate prose items from proof tree + goal map
  const proseItems = useMemo<ProseItem[]>(() => {
    return generateProofProse(state.root, state.cursor.nodeId, goalMap);
  }, [state.root, state.cursor.nodeId, goalMap]);

  // Dispatch a structural change (goes on undo stack)
  const pushChange = useCallback((newState: ProofTreeState) => {
    onHistoryChange(pushState(history, newState));
    setTacticMode(null);
    setGoalInteractionState(prev => ({ ...prev, selectedBinder: null, selectedHyp: null }));
  }, [history, onHistoryChange]);

  // Dispatch a cursor-only move (does NOT go on undo stack)
  const moveCursor = useCallback((newState: ProofTreeState) => {
    onHistoryChange(updateCurrent(history, newState));
  }, [history, onHistoryChange]);

  const handleApplySuggestion = useCallback((suggestion: TacticSuggestion) => {
    // Lean backend: the panel may handle this suggestion itself (validated
    // insert / term-builder open). Clear the hypothesis selection either way.
    if (onApplySuggestionOverride?.(suggestion)) {
      setGoalInteractionState(prev => ({ ...prev, selectedHyp: null }));
      return;
    }
    const result = applySuggestionToProofTreeState(state, suggestion, {
      typedContext,
      editingNames: goalInteractionState.editingNames,
      editingSuggestionId: goalInteractionState.editingSuggestionId,
    });

    if (result) {
      pushChange(result);
      setGoalInteractionState(clearGoalInteractionAfterApply());
    }
  }, [
    state,
    typedContext,
    goalInteractionState.editingNames,
    goalInteractionState.editingSuggestionId,
    pushChange,
  , onApplySuggestionOverride]);

  const handleStartSuggestionEditing = useCallback((suggestion: TacticSuggestion) => {
    setGoalInteractionState(prev => startGoalInteractionEditing(prev, suggestion));
  }, []);

  const handleEditingNamesChange = useCallback((names: string[] | null, suggestionId?: string) => {
    setGoalInteractionState(prev => updateGoalInteractionEditingNames(prev, names, suggestionId));
  }, []);

  const handleKeyDown = useCallback((e: React.KeyboardEvent) => {
    // Don't intercept keys when typing in an input
    if ((e.target as HTMLElement).tagName === 'INPUT') return;

    switch (e.key) {
      case 'ArrowUp': {
        e.preventDefault();
        const moved = moveCursorUp(state);
        if (moved !== state) moveCursor(moved);
        setTacticMode(null);
        break;
      }
      case 'ArrowDown': {
        e.preventDefault();
        const moved = moveCursorDown(state);
        if (moved !== state) moveCursor(moved);
        setTacticMode(null);
        break;
      }
      case 'z': {
        if (e.metaKey || e.ctrlKey) {
          e.preventDefault();
          onHistoryChange(e.shiftKey ? redo(history) : undo(history));
          setTacticMode(null);
        }
        break;
      }
      case 'Backspace':
      case 'Delete': {
        const cleared = clearProofTreeNode(state, state.cursor.nodeId);
        if (cleared) {
          pushChange(cleared);
        }
        break;
      }
      case 'Escape': {
        setTacticMode(null);
        break;
      }
    }
  }, [state, history, onHistoryChange, pushChange, moveCursor]);

  const handleClickNode = useCallback((nodeId: ProofNodeId) => {
    if (state.cursor.nodeId !== nodeId) {
      moveCursor({ ...state, cursor: { nodeId } });
      setTacticMode(null);
    }
  }, [state, moveCursor]);

  const leanCounters = useMemo(
    () => ({ applySubgoalCount, caseBranchCount, rewriteSideGoalCount, lemmaDoc }),
    [applySubgoalCount, caseBranchCount, rewriteSideGoalCount, lemmaDoc],
  );
  const hypTrayValue = useMemo(
    () => ({ suggestions: hypSuggestions, onSelect: onHypothesisSelect, onApply: handleApplySuggestion }),
    [hypSuggestions, onHypothesisSelect, handleApplySuggestion],
  );

  return (
    <HypothesisTray.Provider value={hypTrayValue}>
    <LeanCounters.Provider value={leanCounters}>
    <div
      ref={containerRef}
      tabIndex={0}
      onKeyDown={handleKeyDown}
      style={containerStyle}
    >
      <SplitPane
        direction="horizontal"
        paneSizes={INITIAL_PANE_SIZES}
      >
        {/* Left: proof tree / prose */}
        <div style={{ minWidth: 0, overflowY: 'auto', height: '100%', display: 'flex', flexDirection: 'column' }}>
          {/* Tab bar */}
          <div style={{ display: 'flex', gap: '0', borderBottom: '1px solid #21262d', flexShrink: 0 }}>
            {(['proof', 'tactics'] as const).map(tab => (
              <button
                key={tab}
                onClick={() => setActiveTab(tab)}
                style={{
                  padding: '4px 12px',
                  fontSize: '11px',
                  color: activeTab === tab ? '#c9d1d9' : '#484f58',
                  background: activeTab === tab ? '#161b22' : 'transparent',
                  border: 'none',
                  borderBottom: activeTab === tab ? '2px solid #58a6ff' : '2px solid transparent',
                  cursor: 'pointer',
                  fontFamily: FONT_UI,
                  textTransform: 'capitalize',
                }}
              >
                {tab}
              </button>
            ))}
          </div>

          <div style={{ padding: '8px 0', overflowY: 'auto', flex: 1 }}>
            {activeTab === 'tactics' ? (
              <>
              {declSignature && (
                /* The Tactics tab is the CODE view — it opens with the code-
                   shaped signature, exactly as the source file states it. */
                <div style={{
                  padding: '4px 12px 8px', marginBottom: '4px',
                  borderBottom: '1px solid #21262d',
                  fontFamily: 'ui-monospace, SFMono-Regular, Menlo, monospace',
                  fontSize: '12px', color: '#8b949e', whiteSpace: 'pre-wrap',
                }}>
                  {declSignature}
                </div>
              )}
              <ProofNodeView
                node={state.root}
                depth={0}
                cursorId={state.cursor.nodeId}
                state={state}
                tacticMode={tacticMode}
                onTacticMode={setTacticMode}
                onPushChange={pushChange}
                onClickNode={handleClickNode}
                typedContext={typedContext}
                registry={registry}
                goalMap={goalMap}
              />
              </>
            ) : (
              <ProofProseView
                items={proseItems}
                cursorId={state.cursor.nodeId}
                state={state}
                tacticMode={tacticMode}
                onTacticMode={setTacticMode}
                onPushChange={pushChange}
                onClickNode={handleClickNode}
                typedContext={typedContext}
                registry={registry}
                interactiveGoal={interactiveGoal}
                suggestions={goalSuggestions}
                selectedPath={goalSelectedPath}
                onSelectPath={handleSelectGoalPath}
                editingNames={goalEditingNames}
                onEditingNames={handleEditingNamesChange}
                editingSuggestionId={goalEditingSuggestionId}
                onEditingSuggestionId={(id) => handleEditingNamesChange(goalEditingNames, id ?? undefined)}
                onApplySuggestion={handleApplySuggestion}
                onStartEditingSuggestion={handleStartSuggestionEditing}
                selectedBinder={selectedBinder}
                onSelectBinder={handleSelectBinder}
                termBuilder={null}
                onSetTermBuilder={() => {}}
                holeExtraSlot={goalExtraSlot}
                applySubgoalCount={applySubgoalCount}
            caseBranchCount={caseBranchCount}
                rewriteSideGoalCount={rewriteSideGoalCount}
                termBuilderProvider={termBuilderProvider}
              />
            )}
          </div>
        </div>

        {/* Right: goal panel */}
        <GoalPanel
          context={typedContext}
          state={state}
          onPushChange={pushChange}
          interactiveGoal={interactiveGoal}
          suggestions={goalSuggestions}
          selectedPath={goalSelectedPath}
          onSelectPath={handleSelectGoalPath}
          editingNames={goalEditingNames}
          onEditingNames={handleEditingNamesChange}
          editingSuggestionId={goalEditingSuggestionId}
          onEditingSuggestionId={(id) => handleEditingNamesChange(goalEditingNames, id ?? undefined)}
          onApplySuggestion={handleApplySuggestion}
          onStartEditingSuggestion={handleStartSuggestionEditing}
          selectedHyp={selectedHyp}
          onToggleHypothesis={handleToggleHypothesis}
          hypSuggestions={hypSuggestions}
          onOpenTermBuilder={() => {}}
          extraSlot={goalExtraSlot}
        />
      </SplitPane>
    </div>
    </LeanCounters.Provider>
    </HypothesisTray.Provider>
  );
}

// ============================================================================
// GoalPanel — shows context + goal at cursor position
// ============================================================================

// ============================================================================
// GoalInteraction — shared interactive goal + suggestion pills
// ============================================================================

interface GoalInteractionProps {
  interactiveGoal: InteractiveGoal | null;
  suggestions: readonly TacticSuggestion[];
  selectedPath: GoalPath | null;
  onSelectPath: (p: GoalPath | null) => void;
  editingNames: string[] | null;
  onEditingNames: (n: string[] | null, suggestionId?: string) => void;
  editingSuggestionId: string | null;
  onEditingSuggestionId: (id: string | null) => void;
  onApplySuggestion: (suggestion: TacticSuggestion) => void;
  onStartEditingSuggestion: (suggestion: TacticSuggestion) => void;
  /** Fallback LaTeX when interactive goal is unavailable. */
  fallbackGoalLatex?: string;
  validation?: import('../proof-tree/goal-types').ValidationResult;
  /** Font size for the interactive goal display (default '11px'). */
  goalFontSize?: string;
}

function GoalInteraction({
  interactiveGoal, suggestions,
  selectedPath, onSelectPath,
  editingNames, onEditingNames,
  editingSuggestionId, onEditingSuggestionId,
  onApplySuggestion, onStartEditingSuggestion,
  fallbackGoalLatex, validation,
  goalFontSize,
}: GoalInteractionProps) {
  return (
    <>
      {/* Goal display */}
      {validation?.status === 'solved' ? (
        <div style={{
          padding: '4px 8px',
          backgroundColor: 'rgba(63, 185, 80, 0.1)',
          borderRadius: '4px',
          border: '1px solid rgba(63, 185, 80, 0.3)',
          display: 'flex',
          alignItems: 'center',
          gap: '6px',
        }}>
          <span style={{ color: '#3fb950', fontSize: '13px' }}>&#10003;</span>
          <span style={{ color: '#3fb950', fontSize: '11px', fontWeight: 500 }}>Goal solved</span>
        </div>
      ) : interactiveGoal ? (
        <InteractiveGoalView
          goal={interactiveGoal}
          selectedPath={selectedPath}
          onSelectPath={onSelectPath}
          style={{ fontSize: goalFontSize ?? '11px' }}
        />
      ) : (
        <>
          <div style={{
            padding: '4px 8px',
            backgroundColor: '#0d1117',
            borderRadius: '4px',
            border: `1px solid ${validation?.status === 'error' ? 'rgba(248, 81, 73, 0.4)' : '#21262d'}`,
            wordBreak: 'break-word' as const,
          }}>
            {fallbackGoalLatex === '?' ? (
              <span style={{ color: '#d29922', fontStyle: 'italic' }}>unsolved</span>
            ) : fallbackGoalLatex ? (
              <InlineKaTeX latex={fallbackGoalLatex} style={{ fontSize: '11px' }} />
            ) : (
              <span style={{ color: '#484f58' }}>&mdash;</span>
            )}
          </div>
          {validation?.status === 'error' && (
            <div style={{
              marginTop: '4px',
              padding: '3px 8px',
              fontSize: '10px',
              color: '#f85149',
              lineHeight: '1.4',
            }}>
              {validation.message}
            </div>
          )}
        </>
      )}

      {/* Tactic suggestions */}
      {suggestions.length > 0 && (
        <div style={{ marginTop: '8px' }}>
          {/* Simple action buttons (unfold, rewrite, etc.) — flow in a grid */}
          {suggestions.some(s => !(s.proposedNames && s.proposedNames.length > 0)) && (
            <div style={{
              display: 'flex',
              flexWrap: 'wrap',
              gap: '4px',
              marginBottom: '4px',
            }}>
              {suggestions.filter(s => !(s.proposedNames && s.proposedNames.length > 0)).map(s => {
                const btnLabel = s.labelLatex
                  ? <InlineKaTeX latex={s.labelLatex} style={{ fontSize: '11px' }} />
                  : <>{s.label}</>;
                if (s.resultGoalLatex) {
                  return (
                    <button
                      key={s.id}
                      style={suggestionPreviewBtnStyle}
                      onClick={() => onApplySuggestion(s)}
                      title={s.description}
                    >
                      <InlineKaTeX latex={s.resultGoalLatex} style={{ fontSize: '12px' }} />
                      <span style={{ fontSize: '9px', color: '#484f58', marginTop: '2px' }}>
                        {btnLabel}
                      </span>
                    </button>
                  );
                }
                if (s.subgoalPreviews && s.subgoalPreviews.length > 0) {
                  return (
                    <button
                      key={s.id}
                      style={suggestionPreviewBtnStyle}
                      onClick={() => onApplySuggestion(s)}
                      title={s.description}
                    >
                      <div style={{ display: 'flex', flexDirection: 'column', gap: '2px', alignItems: 'flex-start' }}>
                        {s.subgoalPreviews.map((sg, i) => (
                          <div key={i} style={{ display: 'flex', alignItems: 'center', gap: '4px' }}>
                            <span style={{ fontSize: '9px', color: '#8b949e', minWidth: '12px' }}>{i + 1}.</span>
                            <InlineKaTeX latex={sg} style={{ fontSize: '11px' }} />
                          </div>
                        ))}
                      </div>
                      <span style={{ fontSize: '9px', color: '#484f58', marginTop: '2px' }}>
                        {btnLabel}
                      </span>
                    </button>
                  );
                }
                return (
                  <button
                    key={s.id}
                    style={suggestionBtnStyle}
                    onClick={() => onApplySuggestion(s)}
                    title={s.description}
                  >
                    {btnLabel}
                  </button>
                );
              })}
            </div>
          )}
          {/* Intro-style suggestions with editable name inputs — one per row */}
          {suggestions.filter(s => s.proposedNames && s.proposedNames.length > 0).map(s => {
            const isEditing = editingSuggestionId === s.id;
            const names = isEditing && editingNames ? editingNames : [...(s.proposedNames ?? [])];
            const btnLabel = s.labelLatex
              ? <InlineKaTeX latex={s.labelLatex} style={{ fontSize: '11px' }} />
              : <>{s.label}</>;
            return (
              <div key={s.id} style={{
                display: 'flex',
                alignItems: 'center',
                gap: '6px',
                padding: '3px 0',
                flexWrap: 'wrap',
              }}>
                <button
                  style={suggestionBtnStyle}
                  onClick={() => onStartEditingSuggestion(s)}
                  title={s.description}
                >
                  {btnLabel}
                </button>
                {names.map((name, i) => (
                  <input
                    key={i}
                    value={name}
                    onChange={e => {
                      const updated = [...names];
                      updated[i] = e.target.value;
                      onEditingNames(updated, isEditing ? undefined : s.id);
                      if (!isEditing) onEditingSuggestionId(s.id);
                    }}
                    onKeyDown={e => {
                      if (e.key === 'Enter') {
                        e.preventDefault();
                        onApplySuggestion(s);
                      }
                    }}
                    style={nameInputStyle}
                  />
                ))}
                <button
                  style={applyBtnStyle}
                  onClick={() => onApplySuggestion(s)}
                >
                  Apply
                </button>
              </div>
            );
          })}
        </div>
      )}
    </>
  );
}

// ============================================================================
// GoalPanel — shows context + goal at cursor position (right pane)
// ============================================================================

function GoalPanel({ context, state, onPushChange, interactiveGoal, suggestions,
  selectedPath, onSelectPath, editingNames, onEditingNames,
  editingSuggestionId, onEditingSuggestionId,
  onApplySuggestion, onStartEditingSuggestion,
  selectedHyp, onToggleHypothesis, hypSuggestions,
  onOpenTermBuilder: _onOpenTermBuilder,
  extraSlot,
}: {
  context: TypedProofContext | null;
  extraSlot?: React.ReactNode;
  state?: ProofTreeState;
  onPushChange?: (s: ProofTreeState) => void;
  /** Open the term builder inline in the prose view. */
  onOpenTermBuilder?: (builder: TermBuilderDisplay) => void;
  interactiveGoal: InteractiveGoal | null;
  suggestions: readonly TacticSuggestion[];
  selectedPath: GoalPath | null;
  onSelectPath: (p: GoalPath | null) => void;
  editingNames: string[] | null;
  onEditingNames: (n: string[] | null, suggestionId?: string) => void;
  editingSuggestionId: string | null;
  onEditingSuggestionId: (id: string | null) => void;
  onApplySuggestion: (suggestion: TacticSuggestion) => void;
  onStartEditingSuggestion: (suggestion: TacticSuggestion) => void;
  selectedHyp: number | null;
  onToggleHypothesis: (hypIndex: number) => void;
  hypSuggestions: readonly TacticSuggestion[];
}) {
  if (!context) return null;

  const { hypotheses, caseLabel, caseLabelLatex, goal, validation } = context;

  return (
    <div style={{
      padding: '8px 12px',
      fontSize: '12px',
      lineHeight: '1.5',
      overflowY: 'auto',
      height: '100%',
    }}>
      {/* Hypotheses */}
      {hypotheses.length > 0 && (
        <div style={{ marginBottom: '10px' }}>
          <div style={sectionHeaderStyle}>CONTEXT</div>
          {hypotheses.map((h, i) => (
            <div
              key={i}
              onClick={() => {
                onToggleHypothesis(i);
              }}
              style={{
                padding: '2px 4px',
                display: 'flex',
                alignItems: 'baseline',
                gap: '4px',
                flexWrap: 'wrap',
                cursor: 'pointer',
                borderRadius: '3px',
                backgroundColor: selectedHyp === i ? 'rgba(88, 166, 255, 0.12)' : 'transparent',
                borderLeft: selectedHyp === i ? '2px solid #58a6ff' : '2px solid transparent',
              }}>
              <InlineKaTeX latex={texNameForProse(h.name)} style={{ fontSize: '12px' }} />
              {h.type && (
                <>
                  <span style={{ color: '#484f58', fontSize: '11px' }}>:</span>
                  <InlineKaTeX latex={h.type} style={{ fontSize: '11px' }} />
                </>
              )}
            </div>
          ))}
          {/* Hypothesis action tray */}
          {selectedHyp !== null && hypSuggestions.length > 0 && (
            <div style={{ display: 'flex', gap: '4px', flexWrap: 'wrap', marginTop: '4px', paddingLeft: '4px' }}>
              {hypSuggestions.map(s => (
                <button
                  key={s.id}
                  style={{ ...suggestionBtnStyle, fontSize: '11px', padding: '2px 8px' }}
                  onClick={(e) => { e.stopPropagation(); onApplySuggestion(s); }}
                  title={s.description}
                >
                  <InlineKaTeX latex={s.labelLatex ?? s.label} style={{ fontSize: '11px' }} />
                </button>
              ))}
            </div>
          )}
        </div>
      )}

      {/* Case info */}
      {caseLabel && (
        <div style={{ marginBottom: '10px' }}>
          <div style={sectionHeaderStyle}>CASE</div>
          <div style={{ padding: '1px 0' }}>
            <InlineKaTeX
              latex={caseLabelLatex ?? textToLatex(caseLabel)}
              style={{ fontSize: '12px' }}
            />
          </div>
        </div>
      )}

      {/* Goal */}
      <div>
        <div style={sectionHeaderStyle}>GOAL</div>
        {state && onPushChange ? (
          <GoalInteraction
            interactiveGoal={interactiveGoal}
            suggestions={suggestions}
            selectedPath={selectedPath}
            onSelectPath={onSelectPath}
            editingNames={editingNames}
            onEditingNames={onEditingNames}
            editingSuggestionId={editingSuggestionId}
            onEditingSuggestionId={onEditingSuggestionId}
            onApplySuggestion={onApplySuggestion}
            onStartEditingSuggestion={onStartEditingSuggestion}
            fallbackGoalLatex={goal}
            validation={validation}
            />
        ) : (
          <div style={{
            padding: '4px 8px',
            backgroundColor: '#0d1117',
            borderRadius: '4px',
            border: '1px solid #21262d',
            wordBreak: 'break-word' as const,
          }}>
            {goal ? (
              <InlineKaTeX latex={goal} style={{ fontSize: '11px' }} />
            ) : (
              <span style={{ color: '#484f58' }}>&mdash;</span>
            )}
          </div>
        )}
      </div>

      {/* Lean-backed extra content (path-targeted suggestion pills) */}
      {extraSlot}
    </div>
  );
}

const sectionHeaderStyle: React.CSSProperties = {
  fontSize: '10px',
  color: '#484f58',
  letterSpacing: '0.04em',
  marginBottom: '4px',
  fontWeight: 600,
};

// ============================================================================
// HaveProseItem — editable have/let in prose view
// ============================================================================

function HaveProseItem({
  item, kind, rowStyle, rowHandlers, prose, deleteBtn, renderGoalSection, nextItem,
  state, onPushChange, registry: _registry, termBuilderProvider,
}: {
  item: ProseItem;
  kind: Extract<ProseItemKind, { tag: 'have' }>;
  rowStyle: React.CSSProperties;
  rowHandlers: { onClick: () => void; onMouseEnter: () => void; onMouseLeave: () => void };
  prose: React.CSSProperties;
  deleteBtn: React.ReactNode;
  renderGoalSection: (goalLatex: string | undefined, prefix: string) => React.ReactNode;
  nextItem?: ProseItem;
  state: ProofTreeState;
  onPushChange: (s: ProofTreeState) => void;
  registry?: SyntaxRegistry;
  typedContext: TypedProofContext | null;
  /** Lean backend: probe-backed builder engine (replaces the kernel path). */
  termBuilderProvider?: TermBuilderProvider;
}) {
  const [builderState, setBuilderState] = useState<TermBuilderDisplay | null>(null);
  const [editingName, setEditingName] = useState(false);
  const [editingExpr, setEditingExpr] = useState(false);
  const nameCommittedRef = useRef(false);
  const showHaveGoal = !nextItem;
  // Don't show proofExprLatex if the expr is just "?" (hole) — it can't render
  const isHole = kind.expr.trim() === '?';
  const proofLatex = isHole ? undefined : kind.proofExprLatex;

  // Inline name editor — committed flag prevents double-fire from Enter + blur
  const commitName = useCallback((val: string) => {
    if (nameCommittedRef.current) return;
    nameCommittedRef.current = true;
    const updated = commitProofTreeBinderRename(state, { tag: 'have', nodeId: item.nodeId }, val);
    if (updated) onPushChange(updated);
    setEditingName(false);
  }, [state, item.nodeId, onPushChange]);

  // Open the term builder by parsing the have expression into slots.
  // Lean backend: the async provider probes Lean instead of the kernel.
  // The expression as it stood when the builder opened, so ✕ can put it back.
  // Each fill writes into the proof immediately (that is what keeps the goal
  // below in step with the term you are assembling), which also means there is
  // something to undo if you change your mind.
  const exprBeforeBuild = useRef<string | null>(null);
  const openBuilder = useCallback(() => {
    if (!termBuilderProvider) return;
    exprBeforeBuild.current = kind.expr;
    void termBuilderProvider.open(kind.expr).then((d) => {
      if (d) setBuilderState(d);
    });
  }, [kind.expr, termBuilderProvider]);

  const closeBuilder = useCallback((discard: boolean) => {
    if (discard && exprBeforeBuild.current !== null && exprBeforeBuild.current !== kind.expr) {
      const reverted = editHaveExpr(state, item.nodeId, exprBeforeBuild.current);
      if (reverted) onPushChange(reverted);
    }
    exprBeforeBuild.current = null;
    setBuilderState(null);
  }, [state, item.nodeId, onPushChange, kind.expr]);

  if (builderState) {
    return (
      <div style={rowStyle}>
        <ProofTreeTermBuilderPanel
          builderState={builderState}
          registry={_registry}
          onFillSlot={(slotIndex, sourceExpr) => {
            if (!termBuilderProvider) return;
            // Probe-validate the fill, then write the updated expression into
            // the have node so it updates live. The MathEditor emits
            // `\epsilon`; Lean wants `ε`.
            void termBuilderProvider.fill(builderState, slotIndex, convertMathEditorSourceToUnicode(sourceExpr)).then((r) => {
              if (!r) return;
              setBuilderState(r.display);
              const updated = editHaveExpr(state, item.nodeId, r.expr);
              if (updated) onPushChange(updated);
            });
          }}
          onClearSlot={(slotIndex) => {
            if (!termBuilderProvider) return;
            void termBuilderProvider.clear(builderState, slotIndex).then((r) => {
              if (!r) return;
              setBuilderState(r.display);
              const updated = editHaveExpr(state, item.nodeId, r.expr);
              if (updated) onPushChange(updated);
            });
          }}
          onConfirm={() => closeBuilder(false)}
          onCancel={() => closeBuilder(true)}
          onHoistToHave={(slotIndex) => {
            {
              // Insert `have hN : <slot type>` with its own interactive proof
              // subtree above this have, and fill the slot with hN.
              const r = termBuilderProvider?.hoist?.(builderState, slotIndex);
              if (!r) return;
              const target = findNode(state.root, item.nodeId);
              if (!target || target.tag !== 'have') return;
              const inserted = mkHave(r.haveName, '?', target, r.haveTypeExpr, mkHole());
              const withInsert: ProofTreeState = {
                root: replaceNode(state.root, item.nodeId, inserted),
                cursor: state.cursor,
              };
              setBuilderState(r.display);
              onPushChange(editHaveExpr(withInsert, item.nodeId, r.expr) ?? withInsert);
            }
          }}
        />
        {deleteBtn}
      </div>
    );
  }

  const hasError = !!kind.error;
  const errorStyle = hasError ? { color: '#f85149' } : {};
  // Use typeLatex from child context or explicit type annotation
  const displayType = kind.typeLatex;

  const nameEditor = editingName ? (
    <InlineTextEditInput
      autoFocus
      defaultValue={kind.name}
      width={`${Math.max(kind.name.length, 3) + 2}ch`}
      commitOnTab
      onCommit={(value) => commitName(value.trim())}
      onCancel={() => {
        nameCommittedRef.current = true;
        setEditingName(false);
      }}
    />
  ) : (
    <span
      onClick={(e) => {
        e.stopPropagation();
        nameCommittedRef.current = false;
        setEditingName(true);
      }}
      style={{ cursor: 'pointer', borderBottom: '1px dashed rgba(88, 166, 255, 0.3)' }}
      title="Click to rename"
    >
      <InlineKaTeX latex={texNameForProse(kind.name)} style={{ fontSize: '13px', fontWeight: 600 }} />
    </span>
  );

  // Inline expression editor for have proof
  const exprEditor = editingExpr ? (
    <InlineTextEditInput
      autoFocus
      defaultValue={kind.expr}
      width={`${Math.max(kind.expr.length, 10) + 4}ch`}
      minWidth="120px"
      onCommit={(value) => {
        const updated = commitHaveExprSourceInProofTree(state, item.nodeId, value);
        if (updated) onPushChange(updated);
        setEditingExpr(false);
      }}
      onCancel={() => setEditingExpr(false)}
    />
  ) : null;

  return (
    <div style={{ ...rowStyle, ...(hasError ? { backgroundColor: 'rgba(248, 81, 73, 0.06)', borderLeft: '2px solid #f85149' } : {}) }} {...rowHandlers}>
      {/* `h : T`, the order mathematics writes it in — name first, then what it
          says. This read backwards ("Observe that 0 < ε/2 (h₂)"): the fact came
          first and the name it is being given trailed behind in parentheses,
          which is the shape of an aside, not of a definition. */}
      <span style={{ ...prose, ...errorStyle }}>Observe that{' '}</span>
      {nameEditor}
      {displayType && (
        <>
          <span style={prose}>{' : '}</span>
          <InlineKaTeX latex={displayType} style={{ fontSize: '13px' }} />
        </>
      )}
      {kind.hasProofTree ? (
        /* Interactive proof subtree — the subgoal is rendered as a child prose item */
        null
      ) : (
        <HaveExprBlock
          editingExpr={editingExpr}
          exprEditor={exprEditor}
          isHole={isHole}
          proofLatex={proofLatex}
          expr={kind.expr}
          prose={prose}
          onStartEditing={(e) => {
            e.stopPropagation();
            setEditingExpr(true);
          }}
          onOpenBuilder={(e) => {
            e.stopPropagation();
            openBuilder();
          }}
        />
      )}
      {kind.error && (
        <div style={{ fontSize: '11px', color: '#f85149', paddingLeft: '20px', paddingTop: '2px' }}>
          ({kind.error.substring(0, 120)})
        </div>
      )}
      {showHaveGoal && !hasError && renderGoalSection(kind.goalLatex, ' It remains to show')}
      {deleteBtn}
    </div>
  );
}

// ============================================================================
// TermBuilderView — interactive slot-filling for function application
// ============================================================================

/** Registry fallback for the builder's MathEditor on the Lean path (no TT
 *  registry there): plain identifiers/applications convert generically. */
const EMPTY_BUILDER_REGISTRY: SyntaxRegistry = { symbolMap: new Map(), entries: [] };

function TermBuilderView({
  builderState,
  onFillSlot,
  onClearSlot,
  onConfirm,
  onCancel,
  registry,
  onHoistToHave,
}: {
  /** Display contract — satisfied by both TT's TermBuilderState (kernel) and
   *  the Lean provider's probe-backed display. */
  builderState: TermBuilderDisplay;
  onFillSlot: (slotIndex: number, value: string) => void;
  onClearSlot: (slotIndex: number) => void;
  onConfirm: () => void;
  onCancel: () => void;
  registry?: SyntaxRegistry;
  /** Hoist a slot's obligation to a have above: creates `have name := ?` before the current node. */
  onHoistToHave?: (slotIndex: number) => void;
}) {
  const [activeSlot, setActiveSlot] = useState<number | null>(null);
  const mathEditorRef = useRef<MathEditorHandle>(null);

  const explicitSlots = builderState.slots.filter(s => !s.implicit);
  const allFilled = explicitSlots.every(s => s.value !== null);

  return (
    <div style={{
      padding: '8px 12px',
      backgroundColor: 'rgba(88, 166, 255, 0.06)',
      border: '1px solid rgba(88, 166, 255, 0.2)',
      borderRadius: '6px',
      marginBottom: '8px',
    }}>
      {/* Header.
          There was no way to SUBMIT: the only control was the ✕, which reads as
          "discard", so a finished term left you unsure whether clicking it kept
          your work. (It did — each fill is written into the proof as you go —
          but nothing said so.) `allFilled` was even computed here and never
          used; the button was simply never built. */}
      <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center', marginBottom: '6px' }}>
        <span style={{ fontSize: '11px', color: '#8b949e', letterSpacing: '0.03em' }}>
          BUILDING TERM
        </span>
        <span style={{ display: 'flex', alignItems: 'center', gap: '8px' }}>
          <button
            onClick={onConfirm}
            disabled={!allFilled}
            title={allFilled ? 'Use this term' : 'Fill every slot first'}
            style={{
              background: allFilled ? 'rgba(63, 185, 80, 0.15)' : 'none',
              border: `1px solid ${allFilled ? '#3fb950' : '#30363d'}`,
              borderRadius: '4px',
              color: allFilled ? '#3fb950' : '#484f58',
              cursor: allFilled ? 'pointer' : 'default',
              fontSize: '11px',
              padding: '1px 8px',
              fontFamily: 'inherit',
            }}
          >
            ✓ Done
          </button>
          <button
            onClick={onCancel}
            title="Discard this term"
            style={{ background: 'none', border: 'none', color: '#f85149', cursor: 'pointer', fontSize: '11px' }}
          >
            ✕
          </button>
        </span>
      </div>

      {/* Function name + slots */}
      <div style={{ display: 'flex', flexWrap: 'wrap', alignItems: 'center', gap: '4px', fontSize: '13px' }}>
        <InlineKaTeX latex={`\\operatorname{${builderState.fnDisplayName.replace(/_/g, '\\_')}}`} style={{ fontSize: '13px' }} />
        {explicitSlots.map(slot => (
          <span key={slot.index} style={{ display: 'inline-flex', alignItems: 'center', gap: '2px' }}>
          <span
            onClick={() => {
              if (slot.value !== null && activeSlot !== slot.index) {
                onClearSlot(slot.index);
                setActiveSlot(slot.index);
                return;
              }
              setActiveSlot(prev => prev === slot.index ? null : slot.index);
            }}
            style={{
              display: 'inline-block',
              padding: '2px 8px',
              borderRadius: '4px',
              cursor: 'pointer',
              border: activeSlot === slot.index
                ? '1px solid #58a6ff'
                : slot.error
                  ? '1px solid #f85149'
                  : slot.value !== null
                    ? '1px solid #238636'
                    : '1px dashed #484f58',
              backgroundColor: activeSlot === slot.index
                ? 'rgba(88, 166, 255, 0.12)'
                : slot.error
                  ? 'rgba(248, 81, 73, 0.08)'
                  : slot.value !== null
                    ? 'rgba(35, 134, 54, 0.08)'
                    : 'rgba(110, 118, 129, 0.06)',
              fontSize: '12px',
            }}
            title={slot.error ?? undefined}
          >
            {slot.value !== null ? (
              <InlineKaTeX latex={slot.valueLatex ?? '?'} style={{ fontSize: '12px' }} />
            ) : (
              <span style={{ color: '#8b949e' }}>
                <InlineKaTeX latex={slot.typeLatex} style={{ fontSize: '11px', color: '#8b949e' }} />
              </span>
            )}
            {slot.error && (
              <div style={{ fontSize: '9px', color: '#f85149', maxWidth: '150px', overflow: 'hidden', textOverflow: 'ellipsis', whiteSpace: 'nowrap' }}>
                {slot.error.substring(0, 50)}
              </div>
            )}
          </span>
          {/* Hoist button: extract this slot's obligation to a have above */}
          {slot.value === null && onHoistToHave && (
            <button
              onClick={(e) => { e.stopPropagation(); onHoistToHave(slot.index); }}
              style={{ background: 'none', border: '1px solid #30363d', borderRadius: '3px', color: '#79c0ff', fontSize: '10px', padding: '0 3px', cursor: 'pointer', lineHeight: '1.4' }}
              title={`Work on this obligation separately in a have above`}
            >↑</button>
          )}
          </span>
        ))}
      </div>

      {/* Active slot: suggestions + input */}
      {activeSlot !== null && (
        <div style={{ marginTop: '6px', paddingLeft: '4px' }}>
          <div style={{ fontSize: '10px', color: '#8b949e', marginBottom: '3px' }}>
            Fill <strong>{builderState.slots[activeSlot]?.name}</strong>:
          </div>
          {/* Suggestion buttons */}
          <div style={{ display: 'flex', gap: '3px', flexWrap: 'wrap', marginBottom: '4px' }}>
            {(builderState.slotSuggestions.get(activeSlot) ?? []).slice(0, 12).map(name => (
              <button
                key={name}
                style={{ ...suggestionBtnStyle, fontSize: '10px', padding: '1px 6px' }}
                onClick={() => { onFillSlot(activeSlot, name); setActiveSlot(null); }}
              >
                {name}
              </button>
            ))}
          </div>
          {/* Math editor for typing expressions with LaTeX rendering */}
          <div style={{ display: 'flex', gap: '4px', alignItems: 'center' }}>
            <div
              style={{
                flex: 1,
                background: '#0d1117',
                border: '1px solid #30363d',
                borderRadius: '4px',
                padding: '4px 8px',
                minHeight: '28px',
              }}
              onKeyDown={(e) => {
                if (e.key === 'Enter') {
                  e.preventDefault();
                  e.stopPropagation();
                  const editorState = mathEditorRef.current?.getState();
                  const reg = registry ?? EMPTY_BUILDER_REGISTRY;
                  if (editorState) {
                    const result = convertToSource(reg, editorState.root.children);
                    if (result.source && result.source !== '?') {
                      onFillSlot(activeSlot, result.source);
                      setActiveSlot(null);
                    }
                  }
                }
                if (e.key === 'Escape') {
                  e.stopPropagation();
                  setActiveSlot(null);
                }
              }}
            >
              <MathEditor
                ref={mathEditorRef}
                registry={registry}
                placeholder="type expression..."
                showTypeInference={false}
                containerStyle={{ fontSize: '13px' }}
              />
            </div>
            {/* Confirm button */}
            <button
              onClick={() => {
                const editorState = mathEditorRef.current?.getState();
                const reg = registry ?? EMPTY_BUILDER_REGISTRY;
                if (editorState) {
                  const result = convertToSource(reg, editorState.root.children);
                  if (result.source && result.source !== '?') {
                    onFillSlot(activeSlot, result.source);
                    setActiveSlot(null);
                  }
                }
              }}
              style={{
                background: '#238636',
                border: '1px solid #2ea043',
                borderRadius: '4px',
                color: '#fff',
                fontSize: '13px',
                padding: '4px 8px',
                cursor: 'pointer',
                fontWeight: 600,
                flexShrink: 0,
              }}
              title="Fill this slot (or press Enter)"
            >
              ✓
            </button>
          </div>
        </div>
      )}

      {/* Return type preview */}
      {builderState.returnTypeLatex && (
        <div style={{ marginTop: '6px', fontSize: '10px', color: '#8b949e' }}>
          returns: <InlineKaTeX latex={builderState.returnTypeLatex} style={{ fontSize: '10px' }} />
        </div>
      )}

      {/* Confirm button — always visible; unfilled slots become ? */}
      {/* No confirm button — the have updates live on each slot fill */}
    </div>
  );
}

const suggestionBtnStyle: React.CSSProperties = {
  background: 'none',
  border: '1px solid #30363d',
  borderRadius: '4px',
  color: '#d2a8ff',
  fontSize: '11px',
  padding: '2px 8px',
  cursor: 'pointer',
  fontFamily: 'system-ui, -apple-system, sans-serif',
  fontWeight: 500,
};

const suggestionPreviewBtnStyle: React.CSSProperties = {
  background: 'none',
  border: '1px solid #30363d',
  borderRadius: '6px',
  color: '#e6edf3',
  padding: '6px 12px',
  cursor: 'pointer',
  display: 'flex',
  flexDirection: 'column',
  alignItems: 'center',
  gap: '0',
};

const nameInputStyle: React.CSSProperties = {
  background: '#0d1117',
  border: '1px solid #30363d',
  borderRadius: '4px',
  color: '#e6edf3',
  fontFamily: '"SF Mono", "Fira Code", "Cascadia Code", monospace',
  fontSize: '11px',
  padding: '2px 6px',
  outline: 'none',
  width: '50px',
};

const applyBtnStyle: React.CSSProperties = {
  background: 'rgba(88, 166, 255, 0.15)',
  border: '1px solid rgba(88, 166, 255, 0.3)',
  borderRadius: '4px',
  color: '#58a6ff',
  fontSize: '10px',
  padding: '2px 8px',
  cursor: 'pointer',
  fontFamily: 'system-ui, -apple-system, sans-serif',
  fontWeight: 500,
};

// ============================================================================
// Node Dispatcher
// ============================================================================

/**
 * The Lean-backed subgoal counters, for the TREE view.
 *
 * The prose view gets these as props; the tree view drills `ProofNodeView`
 * through ten call sites, and `HoleView` — the only consumer — sat at the
 * bottom with no way to reach them. Without them it fell back to the TT kernel
 * path, which has no kernel on the Lean backend and so answered "1": every
 * `apply` from the Tactics tab opened a single branch no matter how many
 * subgoals the lemma actually leaves, and every conditional rewrite lost its
 * side goals.
 */
/**
 * The hypothesis action tray, for names shown in the PROSE.
 *
 * A case pattern (`Case (mk (deltaG, gProof))`) names hypotheses the proof then
 * works with, and those names are right there in the sentence — but clicking
 * one only ever renamed it, so "destructure gProof" meant leaving the prose and
 * finding the name again in the context panel. The tray is the same one that
 * panel uses, and it is safe to offer anywhere: every action in it was
 * validated at the real cursor, and selecting a name that isn't in scope there
 * yields nothing to show.
 */
const HypothesisTray = createContext<{
  suggestions?: readonly TacticSuggestion[];
  onSelect?: (name: string | null) => void;
  onApply?: (s: TacticSuggestion) => void;
}>({});

const LeanCounters = createContext<{
  applySubgoalCount?: (name: string) => number;
  /** Branches a split on this scrutinee opens — one per constructor of its
   *  type. `null` when nothing in scope knows. */
  caseBranchCount?: (scrutinee: string) => number | null;
  /** Doc comment of a file lemma, for reason-style citations. */
  lemmaDoc?: (name: string) => string | undefined;
  /** The declaration's raw Lean signature — shown above the Tactics tree. */
  declSignature?: string;
  rewriteSideGoalCount?: (name: string) => number;
}>({});

/** Head identifier of an expression: `divTwoPos ε epsPos` → `divTwoPos`.
 *  Dotted projections (`limF.eps_delta`) return the dotted name, which has no
 *  file declaration — so they keep their term form, correctly. */
function exprHeadName(expr: string): string | undefined {
  return expr.trim().replace(/^\(+/, '').match(/^[A-Za-z_][A-Za-z0-9_'.]*/)?.[0];
}

interface NodeViewProps {
  node: ProofNode;
  depth: number;
  cursorId: ProofNodeId;
  state: ProofTreeState;
  tacticMode: TacticMode;
  onTacticMode: (m: TacticMode) => void;
  onPushChange: (s: ProofTreeState) => void;
  onClickNode: (id: ProofNodeId) => void;
  typedContext?: TypedProofContext | null;
  registry?: SyntaxRegistry;
  goalMap?: Map<ProofNodeId, NodeGoalInfo>;
}

function ProofNodeView(props: NodeViewProps) {
  switch (props.node.tag) {
    case 'hole': return <HoleView {...props} />;
    case 'intros': return <IntrosView {...props} />;
    case 'destructure': return <DestructureView {...props} />;
    case 'induction': return <InductionView {...props} />;
    case 'exact': return <ExactView {...props} />;
    case 'unfold': return <UnfoldView {...props} />;
    case 'fold': return <FoldView {...props} />;
    case 'rewrite': return <RewriteView {...props} />;
    case 'apply': return <ApplyView {...props} />;
    case 'simp': return <SimpView {...props} />;
    case 'have': return <HaveView {...props} />;
    case 'suffices': return <SufficesView {...props} />;
  }
}

// ============================================================================
// Shared Styles
// ============================================================================

function nodeRowStyle(depth: number, isFocused: boolean): React.CSSProperties {
  return {
    paddingLeft: `${depth * 20 + 8}px`,
    paddingRight: '8px',
    paddingTop: '2px',
    paddingBottom: '2px',
    backgroundColor: isFocused ? 'rgba(88, 166, 255, 0.08)' : 'transparent',
    borderLeft: isFocused ? '2px solid #58a6ff' : '2px solid transparent',
    cursor: 'pointer',
    transition: 'background-color 0.1s',
  };
}

const keywordStyle: React.CSSProperties = {
  color: '#d2a8ff',
  fontWeight: 500,
  fontStyle: 'italic',
};

const mutedStyle: React.CSSProperties = {
  color: '#484f58',
};

const btnStyle: React.CSSProperties = {
  background: 'none',
  border: '1px solid #30363d',
  borderRadius: '4px',
  color: '#8b949e',
  fontSize: '11px',
  padding: '1px 8px',
  cursor: 'pointer',
  fontFamily: FONT_UI,
};

const inputStyle: React.CSSProperties = {
  background: '#0d1117',
  border: '1px solid #30363d',
  borderRadius: '4px',
  color: '#e6edf3',
  fontFamily: FONT_MONO,
  fontSize: '12px',
  padding: '2px 6px',
  outline: 'none',
  width: '150px',
};

const deleteBtnStyle: React.CSSProperties = {
  background: 'none',
  border: 'none',
  color: '#f85149',
  fontSize: '13px',
  cursor: 'pointer',
  padding: '0 4px',
  marginLeft: '4px',
  opacity: 0.7,
  lineHeight: 1,
};

// ============================================================================
// TacticRow — shared row wrapper with hover-reveal delete button
// ============================================================================

function TacticRow({
  nodeId, depth, isFocused, onClickNode, onDelete, hasError, children,
}: {
  nodeId: ProofNodeId;
  depth: number;
  isFocused: boolean;
  onClickNode: (id: ProofNodeId) => void;
  onDelete: () => void;
  hasError?: boolean;
  children: React.ReactNode;
}) {
  const [hovered, setHovered] = useState(false);

  const style: React.CSSProperties = hasError
    ? {
        ...nodeRowStyle(depth, isFocused),
        borderLeftColor: '#f85149',
        backgroundColor: isFocused ? 'rgba(248, 81, 73, 0.12)' : 'rgba(248, 81, 73, 0.06)',
      }
    : nodeRowStyle(depth, isFocused);

  return (
    <div
      style={style}
      onClick={() => onClickNode(nodeId)}
      onMouseEnter={() => setHovered(true)}
      onMouseLeave={() => setHovered(false)}
    >
      {children}
      {hovered && (
        <button
          style={deleteBtnStyle}
          onClick={(e) => { e.stopPropagation(); onDelete(); }}
          title="Delete this tactic"
        >
          {'\u00d7'}
        </button>
      )}
    </div>
  );
}

// ============================================================================
// HoleView
// ============================================================================

function HoleView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, registry }: NodeViewProps) {
  const isFocused = cursorId === node.id;
  const inputRef = useRef<HTMLInputElement>(null);
  const counters = useContext(LeanCounters);

  const handleSubmit = useCallback((value: string) => {
    const result = applyManualProofTreeTactic(state, tacticMode, value, {
      typedContext,
      computeApplySubgoalCount: (_root, _cursorNodeId, name) =>
        counters.applySubgoalCount ? counters.applySubgoalCount(name) : 1,
      computeRewriteSideGoalCount: counters.rewriteSideGoalCount,
      computeCaseBranchCount: (scrutinee) =>
        counters.caseBranchCount ? counters.caseBranchCount(scrutinee) : null,
    });
    if (result) onPushChange(result);
    onTacticMode(null);
  }, [tacticMode, state, onPushChange, onTacticMode, typedContext, registry, counters]);

  const handleKeyDown = useCallback((e: React.KeyboardEvent<HTMLInputElement>) => {
    if (e.key === 'Enter') {
      e.preventDefault();
      e.stopPropagation();
      handleSubmit(e.currentTarget.value);
    }
    if (e.key === 'Escape') {
      e.preventDefault();
      e.stopPropagation();
      onTacticMode(null);
    }
  }, [handleSubmit, onTacticMode]);

  const activeTactic = isFocused ? tacticMode?.tactic ?? null : null;

  return (
    <div style={nodeRowStyle(depth, isFocused)} onClick={() => onClickNode(node.id)}>
      {isFocused && !tacticMode && (
        <span style={{ display: 'inline-flex', gap: '4px', alignItems: 'center', flexWrap: 'wrap' }}>
          <span style={{ ...mutedStyle, fontSize: '12px', marginRight: '4px' }}>?</span>
          <button style={btnStyle} onClick={(e) => { e.stopPropagation(); onTacticMode({ tactic: 'intros' }); }}>
            Given...
          </button>
          <button style={btnStyle} onClick={(e) => { e.stopPropagation(); onTacticMode({ tactic: 'induction' }); }}>
            Induct...
          </button>
          <button style={btnStyle} onClick={(e) => { e.stopPropagation(); onTacticMode({ tactic: 'cases' }); }}>
            Cases...
          </button>
          <button style={btnStyle} onClick={(e) => { e.stopPropagation(); onTacticMode({ tactic: 'exact' }); }}>
            Exact...
          </button>
          <button style={btnStyle} onClick={(e) => { e.stopPropagation(); onTacticMode({ tactic: 'unfold' }); }}>
            Unfold...
          </button>
          <button style={btnStyle} onClick={(e) => { e.stopPropagation(); onTacticMode({ tactic: 'fold' }); }}>
            Fold...
          </button>
          <button style={btnStyle} onClick={(e) => { e.stopPropagation(); onTacticMode({ tactic: 'rewrite' }); }}>
            Rewrite...
          </button>
          <button style={btnStyle} onClick={(e) => { e.stopPropagation(); onTacticMode({ tactic: 'rewrite_rev' }); }}>
            Rewrite←...
          </button>
          <button style={btnStyle} onClick={(e) => { e.stopPropagation(); onTacticMode({ tactic: 'apply' }); }}>
            Apply...
          </button>
          <button style={btnStyle} onClick={(e) => { e.stopPropagation(); onTacticMode({ tactic: 'simp' }); }}>
            Simp...
          </button>
        </span>
      )}

      {isFocused && activeTactic && (
        <span style={{ display: 'inline-flex', gap: '4px', alignItems: 'center' }}>
          <span style={keywordStyle}>
            {activeTactic === 'intros' ? 'Given' :
             activeTactic === 'induction' ? 'Induct on' :
             activeTactic === 'cases' ? 'By cases on' :
             activeTactic === 'unfold' ? 'Unfold' :
             activeTactic === 'fold' ? 'Fold' :
             activeTactic === 'rewrite' ? 'Rewrite' :
             activeTactic === 'rewrite_rev' ? 'Rewrite\u2190' :
             activeTactic === 'apply' ? 'Apply' :
             activeTactic === 'simp' ? 'Simp' :
             'by'}
          </span>
          <input
            ref={inputRef}
            autoFocus
            style={inputStyle}
            placeholder={
              activeTactic === 'intros' ? 'n, m, f' :
              activeTactic === 'induction' ? 'variable name' :
              activeTactic === 'cases' ? 'hF   or   leTotal a b' :
              activeTactic === 'unfold' ? 'definition name' :
              activeTactic === 'fold' ? 'definition name' :
              activeTactic === 'rewrite' ? 'lemma name' :
              activeTactic === 'rewrite_rev' ? 'lemma name' :
              activeTactic === 'apply' ? 'lemma name' :
              activeTactic === 'simp' ? '(empty = all @simp lemmas)' :
              activeTactic === 'have' ? 'h : 0 < \u03b5 / 2   or   h := proof' :
              'proof expression'
            }
            onKeyDown={handleKeyDown}
            onClick={(e) => e.stopPropagation()}
          />
          <button
            style={btnStyle}
            onClick={(e) => {
              e.stopPropagation();
              if (inputRef.current) handleSubmit(inputRef.current.value);
            }}
          >
            {'\u21B5'}
          </button>
        </span>
      )}

      {!isFocused && (
        <span style={{ ...mutedStyle, fontSize: '12px' }}>?</span>
      )}
    </div>
  );
}

// ============================================================================
// IntrosView — renders "Given n, m, and f,"
// ============================================================================

/** `obtain ⟨a, b⟩ := e` in the TREE view. Without it the node fell out of
 *  `ProofNodeView`'s switch and rendered nothing — taking the whole subtree
 *  below it off the Tactics tab. */
function DestructureView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, registry, goalMap }: NodeViewProps) {
  if (node.tag !== 'destructure') return null;
  const isFocused = cursorId === node.id;

  const handleDelete = useCallback(() => {
    const result = clearProofTreeNode(state, node.id);
    if (result) onPushChange(result);
  }, [state, node.id, onPushChange]);

  return (
    <>
      <TacticRow nodeId={node.id} depth={depth} isFocused={isFocused} onClickNode={onClickNode} onDelete={handleDelete}>
        <span style={keywordStyle}>obtain </span>
        <InlineKaTeX
          latex={`\\langle ${node.names.map((n) => texNameForProse(n)).join(',\\, ')} \\rangle`}
          style={{ fontSize: '13px' }}
        />
        <span style={mutedStyle}> := </span>
        <InlineProseName name={node.scrutinee} />
      </TacticRow>
      <ProofNodeView
        node={node.child}
        depth={depth}
        cursorId={cursorId}
        state={state}
        tacticMode={tacticMode}
        onTacticMode={onTacticMode}
        onPushChange={onPushChange}
        onClickNode={onClickNode}
        typedContext={typedContext}
        registry={registry}
        goalMap={goalMap}
      />
    </>
  );
}

function IntrosView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, registry, goalMap }: NodeViewProps) {
  if (node.tag !== 'intros') return null;
  const isFocused = cursorId === node.id;

  // Build a single KaTeX expression for all names with Oxford comma
  const namesLatex = (names: readonly string[]): string => {
    const parts = names.map(n => texNameForProse(n));
    if (parts.length === 0) return '';
    if (parts.length === 1) return parts[0];
    if (parts.length === 2) return `${parts[0]} \\text{ and } ${parts[1]}`;
    return parts.slice(0, -1).join(',\\, ') + ',\\, \\text{and } ' + parts[parts.length - 1];
  };

  const handleDelete = useCallback(() => {
    const result = clearProofTreeNode(state, node.id);
    if (result) onPushChange(result);
  }, [state, node.id, onPushChange]);

  return (
    <>
      <TacticRow nodeId={node.id} depth={depth} isFocused={isFocused} onClickNode={onClickNode} onDelete={handleDelete}>
        <span style={keywordStyle}>Given </span>
        <InlineKaTeX latex={namesLatex(node.names)} style={{ fontSize: '13px' }} />
        <span style={mutedStyle}>,</span>
      </TacticRow>
      <ProofNodeView
        node={node.child}
        depth={depth}
        cursorId={cursorId}
        state={state}
        tacticMode={tacticMode}
        onTacticMode={onTacticMode}
        onPushChange={onPushChange}
        onClickNode={onClickNode}
        typedContext={typedContext}
        registry={registry}
        goalMap={goalMap}
      />
    </>
  );
}

// ============================================================================
// InductionView
// ============================================================================

function InductionView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, registry, goalMap }: NodeViewProps) {
  if (node.tag !== 'induction') return null;
  const isFocused = cursorId === node.id;

  const handleToggleCollapse = useCallback((e: React.MouseEvent) => {
    e.stopPropagation();
    const result = toggleInductionCollapseInProofTree(state, node.id);
    if (result) onPushChange(result);
  }, [state, node.id, onPushChange]);

  const handleAddCase = useCallback((e: React.MouseEvent) => {
    e.stopPropagation();
    const result = addInductionCaseInProofTree(state, node.id, 'new case');
    if (result) onPushChange(result);
  }, [state, node.id, onPushChange]);

  const handleDelete = useCallback(() => {
    const result = clearProofTreeNode(state, node.id);
    if (result) onPushChange(result);
  }, [state, node.id, onPushChange]);

  return (
    <>
      <TacticRow nodeId={node.id} depth={depth} isFocused={isFocused} onClickNode={onClickNode} onDelete={handleDelete}>
        <span
          onClick={handleToggleCollapse}
          style={{ cursor: 'pointer', fontSize: '10px', marginRight: '4px', color: '#484f58', userSelect: 'none' as const }}
        >
          {node.collapsed ? '\u25B6' : '\u25BC'}
        </span>
        <span style={keywordStyle}>{node.isCases ? 'cases ' : 'induct on '}</span>
        {(() => {
          // Prefer rendered scrutineeLatex from goalMap, fall back to plain name
          const scrutineeLatex = goalMap?.get(node.id)?.scrutineeLatex;
          if (scrutineeLatex) {
            return <InlineKaTeX latex={scrutineeLatex} style={{ fontSize: '13px' }} />;
          }
          // For simple variable names, use texNameForProse; for complex expressions, plain text
          const isSimple = /^[a-zA-Z_][a-zA-Z0-9_']*$/.test(node.scrutinee);
          return isSimple
            ? <InlineKaTeX latex={texNameForProse(node.scrutinee)} style={{ fontSize: '13px' }} />
            : <span style={{ fontFamily: 'monospace', fontSize: '12px' }}>{node.scrutinee}</span>;
        })()}
        <span style={mutedStyle}>:</span>
      </TacticRow>

      {!node.collapsed && node.cases.map((c, i) => (
        <CaseView
          key={c.id}
          caseNode={c}
          caseIndex={i}
          inductionId={node.id}
          depth={depth + 1}
          cursorId={cursorId}
          state={state}
          tacticMode={tacticMode}
          onTacticMode={onTacticMode}
          onPushChange={onPushChange}
          onClickNode={onClickNode}
          typedContext={typedContext}
          registry={registry}
          goalMap={goalMap}
        />
      ))}

      {!node.collapsed && (
        <div style={{ paddingLeft: `${(depth + 1) * 20 + 8}px`, paddingTop: '2px', paddingBottom: '2px' }}>
          <button
            style={{ ...btnStyle, fontSize: '10px', color: '#484f58' }}
            onClick={handleAddCase}
          >
            + Add case
          </button>
        </div>
      )}
    </>
  );
}

// ============================================================================
// CaseView
// ============================================================================

interface CaseViewProps {
  caseNode: CaseNode;
  caseIndex: number;
  inductionId: ProofNodeId;
  depth: number;
  cursorId: ProofNodeId;
  state: ProofTreeState;
  tacticMode: TacticMode;
  onTacticMode: (m: TacticMode) => void;
  onPushChange: (s: ProofTreeState) => void;
  onClickNode: (id: ProofNodeId) => void;
  typedContext?: TypedProofContext | null;
  registry?: SyntaxRegistry;
  goalMap?: Map<ProofNodeId, NodeGoalInfo>;
}

function CaseView({
  caseNode, caseIndex, inductionId, depth,
  cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode,
  typedContext, registry, goalMap,
}: CaseViewProps) {
  const isFocused = cursorId === caseNode.id;

  const handleToggleCollapse = useCallback((e: React.MouseEvent) => {
    e.stopPropagation();
    onPushChange(toggleCaseCollapseInProofTree(state, caseNode.id));
  }, [state, caseNode.id, onPushChange]);

  const handleDelete = useCallback((e: React.MouseEvent) => {
    e.stopPropagation();
    const result = removeInductionCaseInProofTree(state, inductionId, caseIndex);
    if (result) onPushChange(result);
  }, [state, inductionId, caseIndex, onPushChange]);

  return (
    <>
      <div style={nodeRowStyle(depth, isFocused)} onClick={() => onClickNode(caseNode.id)}>
        <span
          onClick={handleToggleCollapse}
          style={{ cursor: 'pointer', fontSize: '10px', marginRight: '4px', color: '#484f58', userSelect: 'none' as const }}
        >
          {caseNode.collapsed ? '\u25B6' : '\u25BC'}
        </span>
        <span style={{ color: '#7ee787', fontWeight: 500 }}>Case </span>
        <InlineKaTeX
          latex={caseNode.labelLatex ?? textToLatex(caseNode.label)}
          style={{ fontSize: '13px' }}
        />
        <span style={mutedStyle}>:</span>

        {isFocused && (
          <button
            style={{ ...btnStyle, marginLeft: '8px', fontSize: '10px', color: '#f85149' }}
            onClick={handleDelete}
          >
            {'\u00d7'}
          </button>
        )}
      </div>

      {!caseNode.collapsed && (
        <ProofNodeView
          node={caseNode.body}
          depth={depth + 1}
          cursorId={cursorId}
          state={state}
          tacticMode={tacticMode}
          onTacticMode={onTacticMode}
          onPushChange={onPushChange}
          onClickNode={onClickNode}
          typedContext={typedContext}
          registry={registry}
          goalMap={goalMap}
        />
      )}
    </>
  );
}

// ============================================================================
// UnfoldView — renders "unfold <name>,"
// ============================================================================

function UnfoldView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, registry, goalMap }: NodeViewProps) {
  if (node.tag !== 'unfold') return null;
  const isFocused = cursorId === node.id;
  const hasError = !!goalMap?.get(node.id)?.tacticError;

  const handleDelete = useCallback(() => {
    const result = clearProofTreeNode(state, node.id);
    if (result) onPushChange(result);
  }, [state, node.id, onPushChange]);

  return (
    <>
      <TacticRow nodeId={node.id} depth={depth} isFocused={isFocused} onClickNode={onClickNode} onDelete={handleDelete} hasError={hasError}>
        <span style={keywordStyle}>unfold </span>
        <span style={{ color: '#79c0ff' }}>{node.name}</span>
        {node.occurrence != null && <span style={mutedStyle}> #{node.occurrence}</span>}
        <span style={mutedStyle}>,</span>
      </TacticRow>
      <ProofNodeView
        node={node.child}
        depth={depth}
        cursorId={cursorId}
        state={state}
        tacticMode={tacticMode}
        onTacticMode={onTacticMode}
        onPushChange={onPushChange}
        onClickNode={onClickNode}
        typedContext={typedContext}
        registry={registry}
        goalMap={goalMap}
      />
    </>
  );
}

// ============================================================================
// FoldView — renders "fold <name>,"
// ============================================================================

function FoldView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, registry, goalMap }: NodeViewProps) {
  if (node.tag !== 'fold') return null;
  const isFocused = cursorId === node.id;
  const hasError = !!goalMap?.get(node.id)?.tacticError;

  const handleDelete = useCallback(() => {
    const result = clearProofTreeNode(state, node.id);
    if (result) onPushChange(result);
  }, [state, node.id, onPushChange]);

  return (
    <>
      <TacticRow nodeId={node.id} depth={depth} isFocused={isFocused} onClickNode={onClickNode} onDelete={handleDelete} hasError={hasError}>
        <span style={keywordStyle}>fold </span>
        <span style={{ color: '#79c0ff' }}>{node.name}</span>
        {node.occurrence != null && <span style={mutedStyle}> #{node.occurrence}</span>}
        <span style={mutedStyle}>,</span>
      </TacticRow>
      <ProofNodeView
        node={node.child}
        depth={depth}
        cursorId={cursorId}
        state={state}
        tacticMode={tacticMode}
        onTacticMode={onTacticMode}
        onPushChange={onPushChange}
        onClickNode={onClickNode}
        typedContext={typedContext}
        registry={registry}
        goalMap={goalMap}
      />
    </>
  );
}

// ============================================================================
// RewriteView — renders "rewrite <name>,"
// ============================================================================

function RewriteView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, registry, goalMap }: NodeViewProps) {
  if (node.tag !== 'rewrite') return null;
  const isFocused = cursorId === node.id;
  const hasError = !!goalMap?.get(node.id)?.tacticError;

  const handleDelete = useCallback(() => {
    const result = clearProofTreeNode(state, node.id);
    if (result) onPushChange(result);
  }, [state, node.id, onPushChange]);

  return (
    <>
      <TacticRow nodeId={node.id} depth={depth} isFocused={isFocused} onClickNode={onClickNode} onDelete={handleDelete} hasError={hasError}>
        <span style={keywordStyle}>{node.reverse ? 'rewrite\u2190 ' : 'rewrite '}</span>
        <span style={{ color: '#79c0ff' }}>{node.name}</span>
        {node.occurrences && node.occurrences.length > 0 && <span style={mutedStyle}> #{node.occurrences.join(',')}</span>}
        <span style={mutedStyle}>,</span>
      </TacticRow>
      <ProofNodeView
        node={node.child}
        depth={depth}
        cursorId={cursorId}
        state={state}
        tacticMode={tacticMode}
        onTacticMode={onTacticMode}
        onPushChange={onPushChange}
        onClickNode={onClickNode}
        typedContext={typedContext}
        registry={registry}
        goalMap={goalMap}
      />
    </>
  );
}

// ============================================================================
// ApplyView — renders "apply <name>,"
// ============================================================================

function ApplyView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, registry, goalMap }: NodeViewProps) {
  if (node.tag !== 'apply') return null;
  const isFocused = cursorId === node.id;
  const hasError = !!goalMap?.get(node.id)?.tacticError;

  const handleDelete = useCallback(() => {
    const result = clearProofTreeNode(state, node.id);
    if (result) onPushChange(result);
  }, [state, node.id, onPushChange]);

  return (
    <>
      <TacticRow nodeId={node.id} depth={depth} isFocused={isFocused} onClickNode={onClickNode} onDelete={handleDelete} hasError={hasError}>
        <span style={keywordStyle}>apply </span>
        <span style={{ color: '#79c0ff' }}>{node.name}</span>
        <span style={mutedStyle}>,</span>
      </TacticRow>
      {node.children.map((child) => (
        <ProofNodeView
          key={child.id}
          node={child}
          depth={depth + 1}
          cursorId={cursorId}
          state={state}
          tacticMode={tacticMode}
          onTacticMode={onTacticMode}
          onPushChange={onPushChange}
          onClickNode={onClickNode}
          typedContext={typedContext}
          registry={registry}
          goalMap={goalMap}
        />
      ))}
    </>
  );
}

// ============================================================================
// SimpView
// ============================================================================

function SimpView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, registry, goalMap }: NodeViewProps) {
  if (node.tag !== 'simp') return null;
  const isFocused = cursorId === node.id;

  const handleDelete = useCallback(() => {
    const result = clearProofTreeNode(state, node.id);
    if (result) onPushChange(result);
  }, [state, node.id, onPushChange]);

  const handleToggle = useCallback(() => {
    const result = toggleSimpCollapseInProofTree(state, node.id);
    if (result) onPushChange(result);
  }, [state, node.id, onPushChange]);

  return (
    <>
      <TacticRow nodeId={node.id} depth={depth} isFocused={isFocused} onClickNode={onClickNode} onDelete={handleDelete}>
        <span style={keywordStyle}>simp </span>
        <span style={{ color: '#79c0ff' }}>{node.lemmas.join(', ')}</span>
        <span style={mutedStyle}> ({node.steps.length} step{node.steps.length !== 1 ? 's' : ''})</span>
        <button
          style={{ ...btnStyle, marginLeft: '4px', padding: '0 4px', fontSize: '10px' }}
          onClick={(e) => { e.stopPropagation(); handleToggle(); }}
        >
          {node.collapsed ? '\u25B6' : '\u25BC'}
        </button>
      </TacticRow>
      {!node.collapsed && node.steps.map((step) => (
        <ProofNodeView
          key={step.id}
          node={step}
          depth={depth + 1}
          cursorId={cursorId}
          state={state}
          tacticMode={tacticMode}
          onTacticMode={onTacticMode}
          onPushChange={onPushChange}
          onClickNode={onClickNode}
          typedContext={typedContext}
          registry={registry}
          goalMap={goalMap}
        />
      ))}
      <ProofNodeView
        node={node.child}
        depth={depth + 1}
        cursorId={cursorId}
        state={state}
        tacticMode={tacticMode}
        onTacticMode={onTacticMode}
        onPushChange={onPushChange}
        onClickNode={onClickNode}
        typedContext={typedContext}
        registry={registry}
        goalMap={goalMap}
      />
    </>
  );
}

// ============================================================================
// ExactView
// ============================================================================

function ExactView({ node, depth, cursorId, state, onPushChange, onClickNode }: NodeViewProps) {
  if (node.tag !== 'exact') return null;
  const isFocused = cursorId === node.id;

  const handleDelete = useCallback(() => {
    const result = clearProofTreeNode(state, node.id);
    if (result) onPushChange(result);
  }, [state, node.id, onPushChange]);

  return (
    <TacticRow nodeId={node.id} depth={depth} isFocused={isFocused} onClickNode={onClickNode} onDelete={handleDelete}>
      <span style={keywordStyle}>by </span>
      <InlineKaTeX
        latex={textToLatex(node.expr)}
        style={{ fontSize: '13px' }}
      />
    </TacticRow>
  );
}

// ============================================================================
// HaveView
// ============================================================================

function HaveView({ node, depth, cursorId, state, onPushChange, onClickNode, ...rest }: NodeViewProps) {
  if (node.tag !== 'have') return null;
  const isFocused = cursorId === node.id;
  const handleDelete = useCallback(() => {
    const result = clearProofTreeNode(state, node.id);
    if (result) onPushChange(result);
  }, [state, node.id, onPushChange]);

  return (
    <>
      <TacticRow nodeId={node.id} depth={depth} isFocused={isFocused} onClickNode={onClickNode} onDelete={handleDelete}>
        <span style={keywordStyle}>have </span>
        <InlineKaTeX latex={textToLatex(node.name)} style={{ fontSize: '13px' }} />
        <span style={{ color: '#8b949e' }}> := </span>
        <InlineKaTeX latex={textToLatex(node.expr)} style={{ fontSize: '13px' }} />
      </TacticRow>
      {/* Render the proof subtree (interactive proof of the have's type) */}
      {node.proofTree && (
        <ProofNodeView {...rest} node={node.proofTree} depth={depth + 1} cursorId={cursorId} state={state} onPushChange={onPushChange} onClickNode={onClickNode} />
      )}
      <ProofNodeView {...rest} node={node.child} depth={depth + 1} cursorId={cursorId} state={state} onPushChange={onPushChange} onClickNode={onClickNode} />
    </>
  );
}

// ============================================================================
// SufficesView
// ============================================================================

function SufficesView({ node, depth, cursorId, state, onPushChange, onClickNode, ...rest }: NodeViewProps) {
  if (node.tag !== 'suffices') return null;
  const isFocused = cursorId === node.id;
  const handleDelete = useCallback(() => {
    const result = clearProofTreeNode(state, node.id);
    if (result) onPushChange(result);
  }, [state, node.id, onPushChange]);

  return (
    <>
      <TacticRow nodeId={node.id} depth={depth} isFocused={isFocused} onClickNode={onClickNode} onDelete={handleDelete}>
        <span style={keywordStyle}>suffices </span>
        <InlineKaTeX latex={textToLatex(node.name)} style={{ fontSize: '13px' }} />
        <span style={{ color: '#8b949e' }}> : </span>
        <InlineKaTeX latex={textToLatex(node.typeExpr)} style={{ fontSize: '13px' }} />
      </TacticRow>
      {node.byProof && (
        <ProofNodeView {...rest} node={node.byProof} depth={depth + 1} cursorId={cursorId} state={state} onPushChange={onPushChange} onClickNode={onClickNode} />
      )}
      <ProofNodeView {...rest} node={node.child} depth={depth + 1} cursorId={cursorId} state={state} onPushChange={onPushChange} onClickNode={onClickNode} />
    </>
  );
}

// ============================================================================
// ProofProseView — natural language proof rendering
// ============================================================================

interface ProseViewProps {
  items: ProseItem[];
  cursorId: ProofNodeId;
  state: ProofTreeState;
  tacticMode: TacticMode;
  onTacticMode: (m: TacticMode) => void;
  onPushChange: (s: ProofTreeState) => void;
  onClickNode: (id: ProofNodeId) => void;
  typedContext: TypedProofContext | null;
  registry?: SyntaxRegistry;
  // Shared goal interaction state
  interactiveGoal: InteractiveGoal | null;
  suggestions: readonly TacticSuggestion[];
  selectedPath: GoalPath | null;
  onSelectPath: (p: GoalPath | null) => void;
  editingNames: string[] | null;
  onEditingNames: (n: string[] | null, suggestionId?: string) => void;
  editingSuggestionId: string | null;
  onEditingSuggestionId: (id: string | null) => void;
  onApplySuggestion: (suggestion: TacticSuggestion) => void;
  onStartEditingSuggestion: (suggestion: TacticSuggestion) => void;
  // Binder selection from clickable tokens in prose
  selectedBinder: SelectedBinder | null;
  onSelectBinder: (b: SelectedBinder | null) => void;
  // Inline term builder
  termBuilder?: TermBuilderDisplay | null;
  onSetTermBuilder?: (b: TermBuilderDisplay | null) => void;
  // Extra content rendered inline above the active hole's tactic buttons
  // (Lean-backed suggestion pills); mirrors where the TT path showed them.
  holeExtraSlot?: React.ReactNode;
  applySubgoalCount?: (name: string) => number;
  /** Branches a split on this scrutinee opens — one per constructor of its
   *  type. `null` when nothing in scope knows. */
  caseBranchCount?: (scrutinee: string) => number | null;
  /** Doc comment of a file lemma, for reason-style citations. */
  lemmaDoc?: (name: string) => string | undefined;
  /** The declaration's raw Lean signature — shown above the Tactics tree. */
  declSignature?: string;
  rewriteSideGoalCount?: (name: string) => number;
  termBuilderProvider?: TermBuilderProvider;
}

function ProofProseView({
  items, state, tacticMode, onTacticMode, onPushChange, onClickNode,
  typedContext, registry,
  interactiveGoal, suggestions, selectedPath, onSelectPath,
  editingNames, onEditingNames, editingSuggestionId, onEditingSuggestionId,
  onApplySuggestion, onStartEditingSuggestion,
  selectedBinder, onSelectBinder,
  termBuilder, onSetTermBuilder, holeExtraSlot, applySubgoalCount, caseBranchCount, rewriteSideGoalCount, termBuilderProvider,
}: ProseViewProps) {
  if (items.length === 0) {
    return <div style={{ padding: '8px 12px', color: '#484f58', fontStyle: 'italic' }}>No proof steps yet.</div>;
  }

  // Find the last goal-showing step before the active cursor hole.
  // This step will render its goal interactively instead of as plain LaTeX.
  const lastGoalStepIdx = findLastInteractiveGoalStepIndex(items);

  // Consecutive Obtain rows (≥2, same depth, cursor not inside any of them)
  // group under a single "Obtain:" header — four unpackings are one act.
  // Rows keep their full components (rename, hover types, delete); only the
  // repeated lead word goes.
  const isObtainRow = (i: number): boolean => {
    const k = items[i]?.kind as { anonymous?: boolean; lead?: unknown } | undefined;
    return !!k?.anonymous && k?.lead !== undefined;
  };
  const obtainRunStart = new Set<number>();
  const obtainRunMember = new Set<number>();
  for (let i = 0; i < items.length; i++) {
    if (!isObtainRow(i) || obtainRunMember.has(i)) continue;
    let j = i;
    while (isObtainRow(j) && items[j].depth === items[i].depth) j++;
    const run = items.slice(i, j);
    if (run.length >= 2 && !run.some((r) => r.isCursor)) {
      obtainRunStart.add(i);
      for (let k = i; k < j; k++) obtainRunMember.add(k);
    }
  }

  // Paper framing: open with "Proof." and close with ONE tombstone when
  // nothing is open and nothing is broken. (The per-step qed items barely
  // fire on the Lean path and a paper ends a proof exactly once.)
  const proofComplete =
    items.length > 0 &&
    !items.some((i) =>
      (i.kind.tag === 'hole' && !(i.kind as { solved?: boolean }).solved) ||
      (i.kind as { error?: string }).error !== undefined,
    ) &&
    items[items.length - 1].kind.tag !== 'qed';

  return (
    <div className="proof-prose">
      {/* KaTeX's default .katex-display margin is 1em top+bottom — page-height
          whitespace between every step. Paper density: a display equation sits
          close to the sentence that introduces it. */}
      <style>{`
        .proof-prose .katex-display { margin: 0.25em 0; }
        /* Editor affordances live in the margin voice: chain-step citation
           tags and delete buttons appear when the pointer reaches for them,
           so the DOCUMENT reads clean. */
        .proof-prose .chain-step-tools { opacity: 0; transition: opacity 120ms; }
        .proof-prose div:hover > .chain-step-tools { opacity: 1; }
      `}</style>
      <div style={{ padding: '2px 4px' }}>
        <span style={{ fontStyle: 'italic', fontFamily: 'KaTeX_Main, Georgia, serif', color: '#c9d1d9' }}>Proof.</span>
      </div>
      {items.map((item, idx) => {
        // Deletable items: anything except hole, qed, caseHeader
        // A sole case has no header row of its own, so it carries the header's
        // delete too — otherwise a one-case destructure cannot be removed at all.
        const soleCaseOf = item.kind.tag === 'caseHeader' ? item.kind.lead?.nodeId : undefined;
        const isDeletable = item.kind.tag === 'intro' || item.kind.tag === 'unfold'
          || item.kind.tag === 'rewrite' || item.kind.tag === 'apply'
          || item.kind.tag === 'exact' || item.kind.tag === 'inductionHeader'
          || item.kind.tag === 'have' || item.kind.tag === 'simp' || item.kind.tag === 'suffices'
          || soleCaseOf !== undefined;
        const handleDelete = isDeletable ? () => {
          // Deleting the merged row removes the SPLIT, not the case: the case is
          // the whole of it, and `clearNode` on a case is not a thing.
          const result = clearProofTreeNode(state, soleCaseOf ?? item.nodeId);
          if (result) onPushChange(result);
        } : undefined;

        // Find the next hole's nodeId so clicking the goal can focus it
        const nextHoleNodeId = findNextHoleNodeId(items, idx);

        return (
          <React.Fragment key={`${item.nodeId}-${idx}`}>
          {obtainRunStart.has(idx) && (
            <div style={{ paddingLeft: `${item.depth * 20 + 4}px`, paddingTop: '2px' }}>
              <span style={{ fontFamily: 'KaTeX_Main, Georgia, serif', color: '#c9d1d9' }}>Obtain:</span>
            </div>
          )}
          {obtainRunMember.has(idx) ? (
            <div style={{ paddingLeft: '20px' }}>
              <ProseItemView
                item={item}
                prevItem={idx > 0 ? items[idx - 1] : undefined}
                nextItem={idx < items.length - 1 ? items[idx + 1] : undefined}
                isLastGoalStep={idx === lastGoalStepIdx}
                nextHoleNodeId={nextHoleNodeId}
                onClick={() => onClickNode(item.nodeId)}
                onDelete={handleDelete}
                state={state}
                tacticMode={tacticMode}
                onTacticMode={onTacticMode}
                onPushChange={onPushChange}
                onClickNode={onClickNode}
                typedContext={typedContext}
                registry={registry}
                interactiveGoal={interactiveGoal}
                suggestions={suggestions}
                selectedPath={selectedPath}
                onSelectPath={onSelectPath}
                editingNames={editingNames}
                onEditingNames={onEditingNames}
                editingSuggestionId={editingSuggestionId}
                onEditingSuggestionId={onEditingSuggestionId}
                onApplySuggestion={onApplySuggestion}
                onStartEditingSuggestion={onStartEditingSuggestion}
                selectedBinder={selectedBinder}
                onSelectBinder={onSelectBinder}
                termBuilder={termBuilder}
                onSetTermBuilder={onSetTermBuilder}
                holeExtraSlot={holeExtraSlot}
                applySubgoalCount={applySubgoalCount}
                caseBranchCount={caseBranchCount}
                rewriteSideGoalCount={rewriteSideGoalCount}
                termBuilderProvider={termBuilderProvider}
                compactLead
              />
            </div>
          ) : (
          <ProseItemView
            item={item}
            prevItem={idx > 0 ? items[idx - 1] : undefined}
            nextItem={idx < items.length - 1 ? items[idx + 1] : undefined}
            isLastGoalStep={idx === lastGoalStepIdx}
            nextHoleNodeId={nextHoleNodeId}

            onClick={() => onClickNode(item.nodeId)}
            onDelete={handleDelete}
            state={state}
            tacticMode={tacticMode}
            onTacticMode={onTacticMode}
            onPushChange={onPushChange}
            onClickNode={onClickNode}
            typedContext={typedContext}
              registry={registry}
                interactiveGoal={interactiveGoal}
            suggestions={suggestions}
            selectedPath={selectedPath}
            onSelectPath={onSelectPath}
            editingNames={editingNames}
            onEditingNames={onEditingNames}
            editingSuggestionId={editingSuggestionId}
            onEditingSuggestionId={onEditingSuggestionId}
            onApplySuggestion={onApplySuggestion}
            onStartEditingSuggestion={onStartEditingSuggestion}
              selectedBinder={selectedBinder}
            onSelectBinder={onSelectBinder}
            termBuilder={termBuilder}
            onSetTermBuilder={onSetTermBuilder}
            holeExtraSlot={holeExtraSlot}
            applySubgoalCount={applySubgoalCount}
            caseBranchCount={caseBranchCount}
            rewriteSideGoalCount={rewriteSideGoalCount}
            termBuilderProvider={termBuilderProvider}
          />
          )}
          </React.Fragment>
        );
      })}
      {proofComplete && (
        <div style={{ padding: '2px 4px', textAlign: 'right' }}>
          <span style={{ color: '#3fb950', fontSize: '14px' }}>&#8718;</span>
        </div>
      )}
    </div>
  );
}

// ============================================================================
// ProseItemView — renders a single prose item
// ============================================================================

interface ProseItemViewProps {
  /** Row sits inside a grouped "Obtain:" block — skip its lead word. */
  compactLead?: boolean;
  item: ProseItem;
  prevItem?: ProseItem;
  nextItem?: ProseItem;
  /** True if this is the last goal-showing step before the active hole. */
  isLastGoalStep?: boolean;
  /** NodeId of the next hole after this step (for click-to-focus on goal). */
  nextHoleNodeId?: ProofNodeId;

  onClick: () => void;
  onDelete?: () => void;
  state: ProofTreeState;
  tacticMode: TacticMode;
  onTacticMode: (m: TacticMode) => void;
  onPushChange: (s: ProofTreeState) => void;
  onClickNode: (id: ProofNodeId) => void;
  typedContext: TypedProofContext | null;
  registry?: SyntaxRegistry;
  // Shared goal interaction state
  interactiveGoal: InteractiveGoal | null;
  suggestions: readonly TacticSuggestion[];
  selectedPath: GoalPath | null;
  onSelectPath: (p: GoalPath | null) => void;
  editingNames: string[] | null;
  onEditingNames: (n: string[] | null, suggestionId?: string) => void;
  editingSuggestionId: string | null;
  onEditingSuggestionId: (id: string | null) => void;
  onApplySuggestion: (suggestion: TacticSuggestion) => void;
  onStartEditingSuggestion: (suggestion: TacticSuggestion) => void;
  // Binder selection from clickable tokens in prose
  selectedBinder: SelectedBinder | null;
  onSelectBinder: (b: SelectedBinder | null) => void;
  // Inline term builder
  termBuilder?: TermBuilderDisplay | null;
  onSetTermBuilder?: (b: TermBuilderDisplay | null) => void;
  // Extra content rendered inline above the active hole's tactic buttons.
  holeExtraSlot?: React.ReactNode;
  applySubgoalCount?: (name: string) => number;
  /** Branches a split on this scrutinee opens — one per constructor of its
   *  type. `null` when nothing in scope knows. */
  caseBranchCount?: (scrutinee: string) => number | null;
  /** Doc comment of a file lemma, for reason-style citations. */
  lemmaDoc?: (name: string) => string | undefined;
  /** The declaration's raw Lean signature — shown above the Tactics tree. */
  declSignature?: string;
  rewriteSideGoalCount?: (name: string) => number;
  termBuilderProvider?: TermBuilderProvider;
}

const proseStyle: React.CSSProperties = {
  fontSize: '13px',
  lineHeight: '1.7',
  cursor: 'pointer',
  fontFamily: '"STIX Two Text", "Times New Roman", Georgia, serif',
  textAlign: 'left',
};

// ============================================================================
// BinderNameRenameInput — text input + live KaTeX preview for binder rename
// ============================================================================
//
// The input accepts LaTeX-style commands (\delta_f, \alpha, etc.) thanks to
// `normalizeBinderNameInput`. As the user types, a small preview to the
// right shows how the name will render once committed — so they can tell
// at a glance whether their `\delta_f` is going to become δ_f (subscript)
// or stay as the literal "\delta_f" string.
function BinderNameRenameInput({
  defaultValue, onConfirm, onCancel, autoFocus,
}: {
  defaultValue: string;
  onConfirm: (value: string) => void;
  onCancel: () => void;
  autoFocus?: boolean;
}) {
  const [value, setValue] = useState(defaultValue);
  // Show preview only when the input has a value that DIFFERS visually from
  // the raw text — i.e. when there's something the renderer will transform.
  const previewName = normalizeBinderNameInput(value.trim());
  const previewLatex = previewName ? renderNameLatex(previewName, 'text') : '';
  // Skip the preview when nothing interesting is happening (plain ASCII
  // identifier that renders identically to its raw form).
  const showPreview = previewName.length > 0
    && (previewName !== value.trim() || /[α-ωΑ-Ω_]/.test(previewName));
  return (
    <>
      <input
        defaultValue={defaultValue}
        onChange={e => setValue(e.target.value)}
        onBlur={e => onConfirm(e.target.value)}
        onKeyDown={e => {
          if (e.key === 'Enter') { e.preventDefault(); onConfirm((e.target as HTMLInputElement).value); }
          if (e.key === 'Escape') { e.preventDefault(); onCancel(); }
        }}
        onClick={e => e.stopPropagation()}
        placeholder="rename"
        style={nameInputStyle}
        autoFocus={autoFocus}
      />
      {showPreview && (
        <>
          <span style={{ fontSize: '10px', color: '#484f58', fontFamily: FONT_UI }}>→</span>
          <span style={{ minWidth: '20px' }}>
            <InlineKaTeX latex={previewLatex} style={{ fontSize: '13px' }} />
          </span>
        </>
      )}
    </>
  );
}

function InlineTextEditInput({
  defaultValue,
  onCommit,
  onCancel,
  autoFocus,
  commitOnTab = false,
  width,
  minWidth,
}: {
  defaultValue: string;
  onCommit: (value: string) => void;
  onCancel: () => void;
  autoFocus?: boolean;
  commitOnTab?: boolean;
  width?: string;
  minWidth?: string;
}) {
  return (
    <input
      autoFocus={autoFocus}
      defaultValue={defaultValue}
      style={{
        background: 'rgba(88, 166, 255, 0.1)',
        border: '1px solid rgba(88, 166, 255, 0.3)',
        borderRadius: '3px',
        color: '#c9d1d9',
        fontSize: '13px',
        padding: '1px 6px',
        fontFamily: '"JetBrains Mono", monospace',
        width,
        minWidth,
      }}
      onKeyDown={(e) => {
        if (e.key === 'Enter' || (commitOnTab && e.key === 'Tab')) {
          e.preventDefault();
          onCommit((e.target as HTMLInputElement).value);
        } else if (e.key === 'Escape') {
          e.preventDefault();
          onCancel();
        }
      }}
      onBlur={(e) => onCommit(e.target.value)}
      onClick={(e) => e.stopPropagation()}
    />
  );
}

function ProofTreeTermBuilderPanel({
  builderState,
  registry,
  onFillSlot,
  onClearSlot,
  onConfirm,
  onCancel,
  onHoistToHave,
  marginBottom = '8px',
}: {
  builderState: TermBuilderDisplay;
  registry?: SyntaxRegistry;
  onFillSlot: (slotIndex: number, sourceExpr: string) => void;
  onClearSlot: (slotIndex: number) => void;
  onConfirm: () => void;
  onCancel: () => void;
  onHoistToHave?: (slotIndex: number) => void;
  marginBottom?: string;
}) {
  return (
    <div style={{ marginBottom }}>
      <TermBuilderView
        builderState={builderState}
        onFillSlot={onFillSlot}
        onClearSlot={onClearSlot}
        onConfirm={onConfirm}
        onCancel={onCancel}
        registry={registry}
        onHoistToHave={onHoistToHave}
      />
    </div>
  );
}

function InlineBinderRenameRow({
  depth,
  label,
  renameKey,
  defaultValue,
  onConfirm,
  onCancel,
  autoFocus,
}: {
  depth: number;
  label: string;
  renameKey: string | number;
  defaultValue: string;
  onConfirm: (value: string) => void;
  onCancel: () => void;
  autoFocus?: boolean;
}) {
  return (
    <div style={{
      paddingLeft: `${depth * 20 + 24}px`,
      paddingTop: '2px',
      paddingBottom: '4px',
      display: 'flex',
      alignItems: 'center',
      gap: '6px',
      flexWrap: 'wrap',
    }}>
      <span style={{ fontSize: '10px', color: '#484f58', fontFamily: FONT_UI }}>
        {label}:
      </span>
      <BinderNameRenameInput
        key={renameKey}
        defaultValue={defaultValue}
        onConfirm={onConfirm}
        onCancel={onCancel}
        autoFocus={autoFocus}
      />
    </div>
  );
}

function HaveExprBlock({
  editingExpr,
  exprEditor,
  isHole,
  proofLatex,
  expr,
  prose,
  onStartEditing,
  onOpenBuilder,
}: {

  editingExpr: boolean;
  exprEditor: React.ReactNode;
  isHole: boolean;
  proofLatex?: string;
  expr: string;
  prose: React.CSSProperties;
  onStartEditing: (e: React.MouseEvent) => void;
  onOpenBuilder: (e: React.MouseEvent) => void;
}) {
  const docText = lemmaDocOf(exprHeadName(expr));
  if (isHole) {
    return editingExpr ? (
      <div style={{ paddingLeft: '20px' }}>{exprEditor}</div>
    ) : (
      <span
        onClick={onStartEditing}
        style={{
          cursor: 'pointer',
          color: '#8b949e',
          fontStyle: 'italic',
          marginLeft: '6px',
          borderBottom: '1px dashed rgba(248, 81, 73, 0.4)',
        }}
        title="Click to provide proof"
      >
        proof needed
      </span>
    );
  }

  if (proofLatex) {
    return (
      <span style={{ opacity: 0.75 }}>
        <span style={prose}>{' '}since{' '}</span>
        {docText ? (
          /* The reason reads as prose; the term is one hover away and the
             click still opens the builder — display changed, model untouched. */
          <HoverType typeLatex={proofLatex}>
            <span
              onClick={onOpenBuilder}
              style={{ cursor: 'pointer', borderBottom: '1px dashed rgba(88, 166, 255, 0.4)' }}
              title="Click to edit expression"
            >
              <span style={prose}>{docText}</span>
            </span>
          </HoverType>
        ) : (
          <span
            onClick={onOpenBuilder}
            style={{ cursor: 'pointer', borderBottom: '1px dashed rgba(88, 166, 255, 0.4)' }}
            title="Click to edit expression"
          >
            <InlineKaTeX latex={proofLatex} style={{ fontSize: '13px' }} />
          </span>
        )}
        <span style={prose}>.</span>
      </span>
    );
  }

  return editingExpr ? (
    <div style={{ paddingLeft: '20px' }}>{exprEditor}</div>
  ) : (
    <span
      onClick={onStartEditing}
      style={{
        cursor: 'pointer',
        color: '#8b949e',
        borderBottom: '1px dashed rgba(88, 166, 255, 0.4)',
        marginLeft: '4px',
      }}
      title="Click to edit expression"
    >
      {expr}
    </span>
  );
}

/**
 * Show a name's TYPE on hover.
 *
 * The types are all already here — every binder the proof introduces is a
 * hypothesis in Lean's goal state — but the only place you could read one was
 * the context panel, which means scrolling away from the sentence you are
 * reading to look up a name in a list. A paper writes "where δ_F is the delta
 * from limF"; the closest interactive equivalent is: point at it.
 *
 * Rendered as math, not a native `title`, because a type IS math — `0 < δ_F`
 * as text is a step backwards from what the rest of the view does. Positioned
 * above the name and non-interactive, so it never eats a click meant for the
 * name underneath (those clicks rename the binder).
 */
function HoverType({ typeLatex, children }: { typeLatex?: string; children: React.ReactNode }) {
  const [shown, setShown] = useState(false);
  if (!typeLatex) return <>{children}</>;
  return (
    <span
      style={{ position: 'relative' }}
      onMouseEnter={() => setShown(true)}
      onMouseLeave={() => setShown(false)}
    >
      {children}
      {shown && (
        <span
          style={{
            position: 'absolute',
            bottom: '100%',
            left: '50%',
            transform: 'translateX(-50%)',
            marginBottom: '4px',
            padding: '3px 7px',
            background: '#161b22',
            border: '1px solid #30363d',
            borderRadius: '4px',
            boxShadow: '0 2px 8px rgba(0, 0, 0, 0.5)',
            whiteSpace: 'nowrap',
            zIndex: 20,
            pointerEvents: 'none',
          }}
        >
          <InlineKaTeX latex={typeLatex} style={{ fontSize: '12px' }} />
        </span>
      )}
    </span>
  );
}

function InlineProseName({ name, fontSize = '13px', fontWeight }: {
  name: string;
  fontSize?: string;
  fontWeight?: React.CSSProperties['fontWeight'];
}) {
  return (
    <InlineKaTeX
      latex={texNameForProse(name)}
      style={{ fontSize, ...(fontWeight ? { fontWeight } : {}) }}
    />
  );
}

function InlineLatexSequence({
  values,
  prose,
  fontSize = '13px',
}: {
  values: readonly string[];
  prose: React.CSSProperties;
  fontSize?: string;
}) {
  return (
    <>
      {values.map((value, index) => (
        <React.Fragment key={`${value}-${index}`}>
          {index > 0 && <span style={prose}>,{' '}</span>}
          <InlineKaTeX latex={value} style={{ fontSize }} />
        </React.Fragment>
      ))}
    </>
  );
}

type ProseRowHandlers = {
  onClick: () => void;
  onMouseEnter: () => void;
  onMouseLeave: () => void;
};

type GoalPrefixRenderer = (preGoalLatex?: string, isValueType?: boolean) => React.ReactNode;
type GoalSectionRenderer = (goalLatex: string | undefined, prefix: string) => React.ReactNode;

function ProseRow({
  rowStyle,
  rowHandlers,
  deleteBtn,
  children,
}: {
  rowStyle: React.CSSProperties;
  rowHandlers: ProseRowHandlers;
  deleteBtn?: React.ReactNode;
  children: React.ReactNode;
}) {
  return (
    <div style={rowStyle} {...rowHandlers}>
      {children}
      {deleteBtn}
    </div>
  );
}

function ApplyLeadFragment({
  phrase,
  theoremName,
  constructorPhrase,
  prose,
}: {
  phrase: 'constructor' | 'theorem';
  theoremName?: string;
  constructorPhrase?: string;
  prose: React.CSSProperties;
}) {
  if (phrase === 'constructor') {
    return <span style={prose}>This holds {constructorPhrase}</span>;
  }

  // The lemma's /-- doc --/ is the REASON; the identifier demotes to a small
  // citation tag. Undocumented lemmas keep the name — an honest fallback.
  const doc = lemmaDocOf(theoremName);
  if (doc) {
    return (
      <>
        <span style={prose}>This holds by {doc}</span>
        <span style={{ color: '#484f58', fontSize: '10px', marginLeft: '5px' }}>[{theoremName}]</span>
      </>
    );
  }
  return (
    <>
      <span style={prose}>This holds by{' '}</span>
      <InlineProseName name={theoremName ?? ''} />
    </>
  );
}

/** Doc for a lemma name via the counters context (hook-shaped helper). */
function lemmaDocOf(name: string | undefined): string | undefined {
  // eslint-disable-next-line react-hooks/rules-of-hooks
  const counters = useContext(LeanCounters);
  return name ? counters.lemmaDoc?.(name) : undefined;
}

function UnfoldProseItem({
  kind,
  rowStyle,
  rowHandlers,
  prose,
  deleteBtn,
  mustShowPrefix,
  errorSuffix,
  renderGoalSection,
}: {
  kind: Extract<ProseItemKind, { tag: 'unfold' }>;
  rowStyle: React.CSSProperties;
  rowHandlers: ProseRowHandlers;
  prose: React.CSSProperties;
  deleteBtn: React.ReactNode;
  mustShowPrefix: GoalPrefixRenderer;
  errorSuffix: React.ReactNode;
  renderGoalSection: GoalSectionRenderer;
}) {
  return (
    <ProseRow rowStyle={rowStyle} rowHandlers={rowHandlers} deleteBtn={deleteBtn}>
      {mustShowPrefix(kind.preGoalLatex)}
      <span style={prose}>This holds by definition of{' '}</span>
      <InlineProseName name={kind.name} />
      {errorSuffix}
      {renderGoalSection(kind.goalLatex, ', provided that')}
    </ProseRow>
  );
}

function FoldProseItem({
  kind,
  rowStyle,
  rowHandlers,
  prose,
  deleteBtn,
  mustShowPrefix,
  errorSuffix,
  renderGoalSection,
}: {
  kind: Extract<ProseItemKind, { tag: 'fold' }>;
  rowStyle: React.CSSProperties;
  rowHandlers: ProseRowHandlers;
  prose: React.CSSProperties;
  deleteBtn: React.ReactNode;
  mustShowPrefix: GoalPrefixRenderer;
  errorSuffix: React.ReactNode;
  renderGoalSection: GoalSectionRenderer;
}) {
  return (
    <ProseRow rowStyle={rowStyle} rowHandlers={rowHandlers} deleteBtn={deleteBtn}>
      {mustShowPrefix(kind.preGoalLatex)}
      <span style={prose}>which matches the definition of{' '}</span>
      <InlineProseName name={kind.name} />
      {errorSuffix}
      {renderGoalSection(kind.goalLatex, ', provided that')}
    </ProseRow>
  );
}

function RewriteProseItem({
  kind,
  rowStyle,
  rowHandlers,
  prose,
  deleteBtn,
  mustShowPrefix,
  errorSuffix,
  renderGoalSection,
}: {
  kind: Extract<ProseItemKind, { tag: 'rewrite' }>;
  rowStyle: React.CSSProperties;
  rowHandlers: ProseRowHandlers;
  prose: React.CSSProperties;
  deleteBtn: React.ReactNode;
  mustShowPrefix: GoalPrefixRenderer;
  errorSuffix: React.ReactNode;
  renderGoalSection: GoalSectionRenderer;
}) {
  const rewriteReference = describeRewriteReference(kind);
  return (
    <ProseRow rowStyle={rowStyle} rowHandlers={rowHandlers} deleteBtn={deleteBtn}>
      {mustShowPrefix(kind.preGoalLatex)}
      <span style={prose}>This holds because{' '}</span>
      {rewriteReference.mode === 'equation' ? (
        <>
          <InlineKaTeX latex={rewriteReference.equationLatex ?? ''} style={{ fontSize: '12px' }} />
          <span style={prose}>{rewriteReference.arrowSuffix} (</span>
          <InlineProseName name={rewriteReference.theoremName} />
          <span style={prose}>)</span>
        </>
      ) : (
        <>
          <span style={prose}>of{' '}</span>
          <InlineProseName name={rewriteReference.theoremName} />
          {rewriteReference.arrowSuffix && <span style={prose}>{rewriteReference.arrowSuffix}</span>}
        </>
      )}
      {errorSuffix}
      {renderGoalSection(kind.goalLatex, ', provided that')}
    </ProseRow>
  );
}

function ApplyProseItem({
  item,
  kind,
  rowStyle,
  rowHandlers,
  prose,
  deleteBtn,
  mustShowPrefix,
  errorSuffix,
  renderGoalSection,
}: {
  item: ProseItem;
  kind: Extract<ProseItemKind, { tag: 'apply' }>;
  rowStyle: React.CSSProperties;
  rowHandlers: ProseRowHandlers;
  prose: React.CSSProperties;
  deleteBtn: React.ReactNode;
  mustShowPrefix: GoalPrefixRenderer;
  errorSuffix: React.ReactNode;
  renderGoalSection: GoalSectionRenderer;
}) {
  const applyDescription = describeApplyProse(kind);

  if (applyDescription.mode === 'proofExprs') {
    const ROMAN = ['(i)', '(ii)', '(iii)', '(iv)', '(v)', '(vi)'];
    return (
      <ProseRow rowStyle={rowStyle} rowHandlers={rowHandlers} deleteBtn={deleteBtn}>
        {mustShowPrefix(kind.preGoalLatex)}
        <span style={prose}>The result follows from</span>
        {applyDescription.proofExprs.map((expr, i) => (
          <div key={i} style={{ paddingLeft: `${item.depth * 20 + 24}px`, paddingTop: '1px' }}>
            <span style={{ color: '#8b949e', fontSize: '12px', marginRight: '4px' }}>{ROMAN[i] ?? `(${i + 1})`}</span>
            <InlineKaTeX latex={expr} style={{ fontSize: '13px' }} />
          </div>
        ))}
        {errorSuffix}
      </ProseRow>
    );
  }

  if (applyDescription.mode === 'singleSubgoal') {
    return (
      <ProseRow rowStyle={rowStyle} rowHandlers={rowHandlers} deleteBtn={deleteBtn}>
        {mustShowPrefix(kind.preGoalLatex)}
        <ApplyLeadFragment
          phrase={applyDescription.phrase}
          theoremName={applyDescription.theoremName}
          constructorPhrase={applyDescription.constructorPhrase}
          prose={prose}
        />
        {applyDescription.appliedArgs.length > 0 && (
          <>
            <span style={prose}>{' '}applied to{' '}</span>
            <InlineLatexSequence values={applyDescription.appliedArgs} prose={prose} />
          </>
        )}
        {errorSuffix}
        {renderGoalSection(applyDescription.subgoals[0], ', provided that')}
      </ProseRow>
    );
  }

  return (
    <ProseRow rowStyle={rowStyle} rowHandlers={rowHandlers} deleteBtn={deleteBtn}>
      {mustShowPrefix(kind.preGoalLatex)}
      <ApplyLeadFragment
        phrase={applyDescription.phrase}
        theoremName={applyDescription.theoremName}
        constructorPhrase={applyDescription.constructorPhrase}
        prose={prose}
      />
      {applyDescription.appliedArgs.length > 0 && (
        <>
          <span style={prose}>{' '}applied to{' '}</span>
          <InlineLatexSequence values={applyDescription.appliedArgs} prose={prose} />
        </>
      )}
      {errorSuffix}
      <span style={prose}>{applyDescription.subgoals.length > 2 ? `, after showing ${applyDescription.subgoals.length} subgoals:` : ':'}</span>
    </ProseRow>
  );
}

function SimpProseItem({
  kind,
  rowStyle,
  rowHandlers,
  prose,
  deleteBtn,
  mustShowPrefix,
  renderGoalSection,
}: {
  kind: Extract<ProseItemKind, { tag: 'simp' }>;
  rowStyle: React.CSSProperties;
  rowHandlers: ProseRowHandlers;
  prose: React.CSSProperties;
  deleteBtn: React.ReactNode;
  mustShowPrefix: GoalPrefixRenderer;
  renderGoalSection: GoalSectionRenderer;
}) {
  return (
    <ProseRow rowStyle={rowStyle} rowHandlers={rowHandlers} deleteBtn={deleteBtn}>
      {mustShowPrefix(kind.preGoalLatex)}
      {/* `simp` (no lemmas) vs `simp [a, b]`; step count only when the engine
          actually tracked steps (the Lean backend doesn't, so it's omitted). */}
      <span style={prose}>{kind.lemmas.length > 0 ? 'Simplifying using ' : 'Simplifying'}</span>
      {kind.lemmas.length > 0 && (
        <InlineLatexSequence values={kind.lemmas.map((lemma) => texNameForProse(lemma))} prose={prose} />
      )}
      {kind.stepCount > 0 && (
        <span style={prose}>{' '}({kind.stepCount} step{kind.stepCount !== 1 ? 's' : ''})</span>
      )}
      {kind.error
        ? <span style={{ color: '#f85149', fontSize: '11px', marginLeft: '6px' }}>({kind.error.split('\n')[0]})</span>
        : renderGoalSection(kind.goalLatex, ', we get')}
    </ProseRow>
  );
}

function InductionHeaderProseItem({
  kind,
  rowStyle,
  rowHandlers,
  prose,
  deleteBtn,
}: {
  kind: Extract<ProseItemKind, { tag: 'inductionHeader' }>;
  rowStyle: React.CSSProperties;
  rowHandlers: ProseRowHandlers;
  prose: React.CSSProperties;
  deleteBtn: React.ReactNode;
}) {
  const header = describeInductionHeader(kind);
  const scrutineeDisplay = kind.scrutineeLatex
    ? <InlineKaTeX latex={kind.scrutineeLatex} style={{ fontSize: '13px' }} />
    : <InlineProseName name={kind.scrutinee} />;

  // When every branch has a meaning, the header reads like a paper: "Either
  // δF ≤ δG or δG ≤ δF." — the scrutinee term is plumbing (still visible in
  // the Tactics tab).
  if (kind.caseMeanings && kind.caseMeanings.length === 2) {
    return (
      <ProseRow rowStyle={rowStyle} rowHandlers={rowHandlers} deleteBtn={deleteBtn}>
        <span style={prose}>Either{' '}</span>
        <InlineKaTeX latex={kind.caseMeanings[0]} style={{ fontSize: '13px' }} />
        <span style={prose}>{' '}or{' '}</span>
        <InlineKaTeX latex={kind.caseMeanings[1]} style={{ fontSize: '13px' }} />
        <span style={prose}>.</span>
      </ProseRow>
    );
  }
  if (kind.caseMeanings && kind.caseMeanings.length > 2) {
    return (
      <ProseRow rowStyle={rowStyle} rowHandlers={rowHandlers} deleteBtn={deleteBtn}>
        <span style={prose}>One of the following holds:</span>
      </ProseRow>
    );
  }

  return (
    <ProseRow rowStyle={rowStyle} rowHandlers={rowHandlers} deleteBtn={deleteBtn}>
      <span style={prose}>{header.lead}{' '}</span>
      {scrutineeDisplay}
      <span style={prose}>{header.punctuation}</span>
    </ProseRow>
  );
}

function ExactProseItem({
  kind,
  rowStyle,
  rowHandlers,
  prose,
  deleteBtn,
  mustShowPrefix,
}: {
  kind: Extract<ProseItemKind, { tag: 'exact' }>;
  rowStyle: React.CSSProperties;
  rowHandlers: ProseRowHandlers;
  prose: React.CSSProperties;
  deleteBtn: React.ReactNode;
  mustShowPrefix: GoalPrefixRenderer;
}) {
  const description = describeExactProse(kind);
  // For a VALUE exact the term IS the content (never swap it for a doc);
  // for a proof, the head lemma's doc is the reason a paper would give.
  const exactDoc = kind.isValueType ? undefined : lemmaDocOf(exprHeadName(kind.exprLatex));
  // A one-liner closing a goal ALREADY on screen reads as a typed witness —
  // "⟨[], h, nilIndependent⟩ : ∃bs, Basis(W, bs)." — not as the stilted
  // "We must show the claim above. By ⟨…⟩." Only when short enough to stay
  // one line, and only when no doc gives a better reason.
  const typedWitness =
    kind.repeatedGoal === true &&
    description.mode !== 'error' &&
    !exactDoc &&
    !!kind.goalLatex &&
    visibleLatexLength(kind.goalLatex) + visibleLatexLength(description.displayLatex) <= 60;

  // A tuple against an ∃ reads best UNFLATTENED: the first component is the
  // witness, the rest discharge the predicate — "Take bs := [] with h and
  // nilIndependent." (⟨a, b, c⟩ means ⟨a, ⟨b, c⟩⟩; making the reader do that
  // unflattening was a legitimate complaint.)
  const tupleParts = splitAnonTuple(kind.exprLatex);
  const existsBinder = kind.goalLatex ? existsBinderFromLatex(kind.goalLatex) : null;
  if (typedWitness && tupleParts && existsBinder) {
    const proofs = tupleParts.slice(1);
    return (
      <ProseRow rowStyle={rowStyle} rowHandlers={rowHandlers} deleteBtn={deleteBtn}>
        <span style={prose}>Take{' '}</span>
        <InlineKaTeX latex={`${texNameForProse(existsBinder)} := ${textToLatex(tupleParts[0])}`} style={{ fontSize: '13px' }} />
        <span style={prose}>{' '}with{' '}</span>
        {proofs.map((c, i) => (
          <React.Fragment key={i}>
            {i > 0 && <span style={prose}>{i === proofs.length - 1 ? ' and ' : ', '}</span>}
            <InlineKaTeX latex={textToLatex(c)} style={{ fontSize: '13px' }} />
          </React.Fragment>
        ))}
        <span style={prose}>.</span>
      </ProseRow>
    );
  }
  if (typedWitness) {
    return (
      <ProseRow rowStyle={rowStyle} rowHandlers={rowHandlers} deleteBtn={deleteBtn}>
        <InlineKaTeX latex={description.displayLatex} style={{ fontSize: '13px' }} />
        <span style={prose}>{' : '}</span>
        <InlineKaTeX latex={kind.goalLatex!} style={{ fontSize: '13px' }} />
        <span style={prose}>.</span>
      </ProseRow>
    );
  }

  return (
    <ProseRow rowStyle={rowStyle} rowHandlers={rowHandlers} deleteBtn={deleteBtn}>
      {mustShowPrefix(kind.goalLatex, kind.isValueType)}
      {description.mode !== 'error' ? (
        exactDoc ? (
          <>
            <span style={prose}>{kind.isValueType ? 'Take' : 'This follows:'}{' '}</span>
            <HoverType typeLatex={description.displayLatex}>
              <span style={{ ...prose, borderBottom: '1px dashed rgba(139, 148, 158, 0.4)' }}>{exactDoc}</span>
            </HoverType>
            <span style={prose}>.</span>
          </>
        ) : (
        <>
          <span style={prose}>{description.lead}{' '}</span>
          <InlineKaTeX latex={description.displayLatex} style={{ fontSize: '13px' }} />
          <span style={prose}>.</span>
        </>
        )
      ) : description.mode === 'error' ? (
        <>
          <span style={{ color: '#f85149' }}>By{' '}</span>
          <InlineKaTeX latex={description.displayLatex} style={{ fontSize: '13px' }} />
          <span style={{ color: '#f85149', fontSize: '11px', marginLeft: '6px' }}>({description.error})</span>
        </>
      ) : (
        <>
          <span style={prose}>{description.lead}{' '}</span>
          <InlineKaTeX latex={description.displayLatex} style={{ fontSize: '13px' }} />
          <span style={prose}>.</span>
        </>
      )}
    </ProseRow>
  );
}

/** What a chain step cites, in the reason voice: the lemma's doc when it has
 *  one; "the induction hypothesis" when the name is an IH (our own enrichment
 *  names them `ih` / `*_ih`, so the pattern is a display convention, not a
 *  guess about user intent); else the bare name. */
function chainReason(lemmaName: string, doc: string | undefined): string {
  if (/(^|_)ih\d*$/.test(lemmaName)) return 'by the induction hypothesis';
  if (doc) return `by ${doc}`;
  return `(${lemmaName})`;
}

function CalcChainStepRow({
  step,
  isStepCursor,
  onClickNode,
  onDelete,
}: {
  step: CalcChainStep;
  isStepCursor: boolean;
  onClickNode: (id: ProofNodeId) => void;
  onDelete: () => void;
}) {
  const stepStyle: React.CSSProperties = {
    display: 'flex',
    alignItems: 'baseline',
    gap: '8px',
    paddingTop: '2px',
    paddingBottom: '2px',
    paddingLeft: '4px',
    borderLeft: isStepCursor ? '2px solid #58a6ff' : '2px solid transparent',
    cursor: 'pointer',
  };

  return (
    <div key={step.nodeId} style={stepStyle} onClick={(e) => { e.stopPropagation(); onClickNode(step.nodeId); }}>
      <span style={{ flex: 1 }}>
        {step.goalLatex ? (
          <InlineKaTeX latex={step.goalLatex} style={{ fontSize: '13px' }} />
        ) : (
          <span style={{ color: '#8b949e', fontStyle: 'italic' }}>?</span>
        )}
      </span>
      {/* The citation is VISIBLE — hover-hiding it buried "by the induction
          hypothesis", the pivotal citation of any induction proof. Only the
          delete button waits for hover. */}
      <span style={{ color: '#6e7681', fontSize: '11px', whiteSpace: 'nowrap', marginLeft: '12px', fontStyle: 'italic' }}>
        {chainReason(step.lemmaName, lemmaDocOf(step.lemmaName))}
      </span>
      <span className="chain-step-tools" style={{ whiteSpace: 'nowrap' }}>
        <button
          onClick={(e) => { e.stopPropagation(); onDelete(); }}
          style={{
            background: 'none', border: 'none', color: '#f85149',
            cursor: 'pointer', fontSize: '13px', padding: '0 2px',
            opacity: 0.5, lineHeight: 1,
          }}
          title="Delete this step"
        >&times;</button>
      </span>
    </div>
  );
}

function CalcChainProseItem({
  item,
  kind,
  rowStyle,
  rowHandlers,
  prose,
  state,
  onPushChange,
  onClickNode,
  mustShowPrefix,
}: {
  item: ProseItem;
  kind: Extract<ProseItemKind, { tag: 'calcChain' }>;
  rowStyle: React.CSSProperties;
  rowHandlers: { onClick: () => void; onMouseEnter: () => void; onMouseLeave: () => void };
  prose: React.CSSProperties;
  state: ProofTreeState;
  onPushChange: (s: ProofTreeState) => void;
  onClickNode: (id: ProofNodeId) => void;
  mustShowPrefix: (preGoalLatex?: string, isValueType?: boolean) => React.ReactNode;
}) {
  return (
    <div style={rowStyle} {...rowHandlers}>
      {mustShowPrefix(kind.preGoalLatex)}
      <span style={prose}>By rewriting:</span>
      <div style={{ paddingLeft: '12px', paddingTop: '4px', paddingBottom: '4px' }}>
        {kind.steps.map((step) => (
          <CalcChainStepRow
            key={step.nodeId}
            step={step}
            isStepCursor={step.nodeId === item.nodeId}
            onClickNode={onClickNode}
            onDelete={() => {
              const result = clearProofTreeNode(state, step.nodeId);
              if (result) onPushChange(result);
            }}
          />
        ))}
      </div>
    </div>
  );
}

function SufficesProseItem({
  kind,
  rowStyle,
  rowHandlers,
  prose,
  deleteBtn,
}: {
  kind: Extract<ProseItemKind, { tag: 'suffices' }>;
  rowStyle: React.CSSProperties;
  rowHandlers: ProseRowHandlers;
  prose: React.CSSProperties;
  deleteBtn: React.ReactNode;
}) {
  return (
    <ProseRow rowStyle={rowStyle} rowHandlers={rowHandlers} deleteBtn={deleteBtn}>
      <span style={prose}>It suffices to show</span>
      {kind.goalLatex && (visibleLatexLength(kind.goalLatex) <= 30 ? (
        <>
          <span style={prose}>{' '}</span>
          <InlineKaTeX latex={kind.goalLatex} style={{ fontSize: '13px' }} />
          <span style={prose}>,</span>
        </>
      ) : (
        <span style={eqBlockStyle}>
          <InlineKaTeX latex={kind.goalLatex} displayMode />
        </span>
      ))}
      {kind.byExprLatex ? (
        <div style={{ paddingLeft: '20px' }}>
          <span style={prose}>since the result then follows from{' '}</span>
          <InlineKaTeX latex={kind.byExprLatex} style={{ fontSize: '13px' }} />
          <span style={prose}>.</span>
        </div>
      ) : null}
    </ProseRow>
  );
}

function SubgoalHeaderProseItem({
  kind,
  rowStyle,
  rowHandlers,
  prose,
  expand,
}: {
  kind: Extract<ProseItemKind, { tag: 'subgoalHeader' }>;
  rowStyle: React.CSSProperties;
  rowHandlers: ProseRowHandlers;
  prose: React.CSSProperties;
  expand?: boolean;
}) {
  const goalLead = buildProseGoalLead(kind.goalLatex, kind.isValueType, undefined, expand);
  if (kind.remaining) {
    return (
      <div style={{ ...rowStyle, paddingTop: '4px' }} {...rowHandlers}>
        {goalLead ? (
          <>
            <span style={prose}>It remains to show{goalLead.inline ? ' ' : ''}</span>
            {goalLead.inline ? (
              <>
                <InlineKaTeX latex={goalLead.goalLatex} style={{ fontSize: '13px' }} />
                <span style={prose}>.</span>
              </>
            ) : (
              <span style={eqBlockStyle}>
                <InlineKaTeX latex={goalLead.goalLatex} displayMode />
              </span>
            )}
          </>
        ) : (
          <span style={prose}>It remains to verify the choice.</span>
        )}
      </div>
    );
  }
  return (
    <div style={{ ...rowStyle, fontWeight: 600, paddingTop: '6px' }} {...rowHandlers}>
      <span style={{ color: '#79c0ff' }}>{kind.label}</span>
      <span style={prose}>:</span>
      {goalLead?.inline && (
        <>
          <span style={{ ...prose, fontWeight: 400 }}>{' '}{goalLead.lead}{' '}</span>
          <InlineKaTeX latex={goalLead.goalLatex} style={{ fontSize: '13px' }} />
          <span style={{ ...prose, fontWeight: 400 }}>.</span>
        </>
      )}
      {goalLead && !goalLead.inline && (
        <>
          <span style={{ ...prose, fontWeight: 400 }}>{' '}{goalLead.lead}</span>
          <span style={eqBlockStyle}>
            <InlineKaTeX latex={goalLead.goalLatex} displayMode />
          </span>
        </>
      )}
    </div>
  );
}

function QedProseItem({
  rowStyle,
  rowHandlers,
}: {
  rowStyle: React.CSSProperties;
  rowHandlers: ProseRowHandlers;
}) {
  return (
    <ProseRow rowStyle={{ ...rowStyle, paddingTop: '2px' }} rowHandlers={rowHandlers}>
      <span style={{ color: '#3fb950', fontSize: '14px' }}>&#8718;</span>
    </ProseRow>
  );
}

// ============================================================================
// IntroProseItem — intro line with clickable variable tokens
// ============================================================================

function IntroProseItem({
  item, kind, rowStyle, rowHandlers, prose, deleteBtn, renderGoalSection,
  state, onPushChange, selectedBinder, onSelectBinder,
}: {
  item: ProseItem;
  kind: Extract<ProseItemKind, { tag: 'intro' }>;
  rowStyle: React.CSSProperties;
  rowHandlers: ProseRowHandlers;
  prose: React.CSSProperties;
  deleteBtn: React.ReactNode;
  renderGoalSection: GoalSectionRenderer;
  state: ProofTreeState;
  onPushChange: (s: ProofTreeState) => void;
  selectedBinder: SelectedBinder | null;
  onSelectBinder: (b: SelectedBinder | null) => void;
}) {
  const isTokenSelected = (token: IntroToken) =>
    selectedBinder?.introNodeId === item.nodeId && selectedBinder?.token.nameIndex === token.nameIndex;

  const selectedToken = selectedBinder?.introNodeId === item.nodeId ? selectedBinder.token : null;

  const handleTokenClick = (token: IntroToken, e: React.MouseEvent) => {
    e.stopPropagation();
    if (isTokenSelected(token)) {
      onSelectBinder(null);
    } else {
      onSelectBinder({ token, introNodeId: item.nodeId });
    }
  };

  const handleRename = useCallback((newName: string) => {
    if (!selectedToken) return;
    const result = commitProofTreeBinderRename(state, {
      tag: 'introToken',
      nodeId: item.nodeId,
      nameIndex: selectedToken.nameIndex,
    }, newName);
    if (result) onPushChange(result);
  }, [selectedToken, state, item.nodeId, onPushChange]);

  const groups = kind.groups;

  return (
    <>
      <div style={rowStyle} {...rowHandlers}>
        <span style={prose}>Let{' '}</span>
        {groups ? (
          groups.map((group, gi) => {
            // Conditions fold into the binder — "Let x ∈ ℝ with 0 < x and
            // |x − x₀| < δ (h, h₁)" — instead of reading as more bindings.
            const prevProp = gi > 0 && !!groups[gi - 1].isProp;
            const joiner =
              gi === 0 ? null
              : group.isProp ? (prevProp ? ' and ' : ' with ')
              : gi === groups.length - 1 ? ' and '
              : ', ';
            const nameTokens = (muted: boolean) => group.tokens.map((token, ti) => (
              <React.Fragment key={ti}>
                {ti > 0 && <span style={prose}>,{' '}</span>}
                <span
                  onClick={e => handleTokenClick(token, e)}
                  style={{
                    cursor: 'pointer',
                    ...(muted ? { color: '#8b949e', fontSize: '11px' } : {}),
                    borderBottom: isTokenSelected(token)
                      ? '2px solid #58a6ff'
                      : `1px dotted rgba(${muted ? '139, 148, 158' : '201, 209, 217'}, 0.4)`,
                    paddingBottom: '1px',
                  }}
                >
                  <InlineKaTeX latex={token.nameLatex} style={{ fontSize: muted ? '11px' : '13px' }} />
                </span>
              </React.Fragment>
            ));
            return (
              <React.Fragment key={gi}>
                {joiner && <span style={prose}>{joiner}</span>}
                {group.isProp ? (
                  <>
                    <InlineKaTeX latex={group.typeLatex} style={{ fontSize: '13px' }} />
                    <span style={{ ...prose, color: '#484f58', fontSize: '11px' }}>{' ('}</span>
                    {nameTokens(true)}
                    <span style={{ ...prose, color: '#484f58', fontSize: '11px' }}>)</span>
                  </>
                ) : (
                  <>
                    {nameTokens(false)}
                    <span style={prose}>{' '}: </span>
                    <InlineKaTeX latex={group.typeLatex} style={{ fontSize: '13px' }} />
                  </>
                )}
              </React.Fragment>
            );
          })
        ) : (
          <InlineKaTeX latex={kind.latex} style={{ fontSize: '13px' }} />
        )}
        {kind.goalLatex ? renderGoalSection(kind.goalLatex, '. We must show') : <span style={prose}>.</span>}
        {deleteBtn}
      </div>
      {/* Inline rename for selected token */}
      {selectedToken && (
        <div data-token-rename>
          <InlineBinderRenameRow
            depth={item.depth}
            label={selectedToken.name}
            renameKey={selectedToken.nameIndex}
            defaultValue={selectedToken.name}
            onConfirm={handleRename}
            onCancel={() => onSelectBinder(null)}
          />
        </div>
      )}
    </>
  );
}

// ============================================================================
// CaseHeaderProseItem — case header with clickable pattern variable names
// ============================================================================

function CaseHeaderProseItem({
  item, kind, rowStyle, rowHandlers, prose, deleteBtn,
  state, onPushChange, compactLead,
}: {
  item: ProseItem;
  kind: Extract<ProseItemKind, { tag: 'caseHeader' }>;
  rowStyle: React.CSSProperties;
  rowHandlers: ProseRowHandlers;
  prose: React.CSSProperties;
  deleteBtn?: React.ReactNode;
  state: ProofTreeState;
  onPushChange: (s: ProofTreeState) => void;
  /** Inside a grouped "Obtain:" block: skip the per-row lead word. */
  compactLead?: boolean;
}) {
  const [selectedParamIndex, setSelectedParamIndex] = useState<number | null>(null);
  const caseContainerRef = useRef<HTMLDivElement>(null);
  const tray = useContext(HypothesisTray);

  const paramNames = kind.constructorParamNames;
  const hasParams = paramNames && paramNames.length > 0;

  // Clicking a bound name both selects it for renaming AND asks the session for
  // that hypothesis's moves, so `Destructure gProof` is one click from the name
  // itself. Out-of-scope names simply produce an empty tray (the session checks
  // scope at the cursor), so this needs no guard of its own.
  const selectParam = useCallback((idx: number | null) => {
    setSelectedParamIndex(idx);
    tray.onSelect?.(idx === null ? null : (paramNames?.[idx] ?? null));
  }, [tray, paramNames]);

  const handleParamClick = (idx: number, e: React.MouseEvent) => {
    e.stopPropagation();
    selectParam(selectedParamIndex === idx ? null : idx);
  };

  const handleRename = useCallback((newName: string) => {
    if (selectedParamIndex === null) return;
    const result = commitProofTreeBinderRename(state, kind.anonymous
      ? { tag: 'destructureName', nodeId: item.nodeId, nameIndex: selectedParamIndex }
      : { tag: 'caseParam', nodeId: item.nodeId, paramIndex: selectedParamIndex },
      newName);
    if (result) onPushChange(result);
  }, [selectedParamIndex, state, item.nodeId, kind.anonymous, onPushChange]);

  // Dismiss selection when focus leaves the container
  const handleCaseContainerBlur = useCallback((e: React.FocusEvent) => {
    if (caseContainerRef.current?.contains(e.relatedTarget as Node)) return;
    const active = document.activeElement;
    if (active instanceof HTMLInputElement) {
      handleRename(active.value);
    }
    selectParam(null);
  }, [handleRename, selectParam]);

  // Render the label with clickable param names.
  // For induction: "scrutinee = Constructor(param1, param2)"
  // For cases: "Constructor(param1, param2)" (no scrutinee prefix)
  // A case label is an EQUATION when the scrutinee is a simple name:
  // "Base case (n = zero):", "Case (vs = cons(a, rest)):" — what the branch
  // actually asserts, not a bare constructor tag.
  const simpleScrutinee =
    kind.scrutinee && /^[A-Za-z_][A-Za-z0-9_']*$/.test(kind.scrutinee) ? kind.scrutinee : undefined;

  const renderLabelWithClickableParams = () => {
    // Paramless constructor (zero, nil): the equation form, or the bare
    // constructor when the scrutinee is complex. Falls back to labelLatex
    // only when we know nothing better — labelLatex may be a dotted composed
    // tag (`zero.nil`), which is plumbing.
    if (!hasParams && kind.constructorName) {
      const ctorTex = texNameForProse(kind.constructorName);
      return (
        <InlineKaTeX
          latex={simpleScrutinee ? `${texNameForProse(simpleScrutinee)} = ${ctorTex}` : ctorTex}
          style={{ fontSize: '12px' }}
        />
      );
    }
    if (!hasParams || (!kind.constructorName && !kind.anonymous)) {
      // No params or missing data — render as before
      return <InlineKaTeX latex={kind.labelLatex} style={{ fontSize: '12px' }} />;
    }

    const ctorTex = texNameForProse(kind.constructorName ?? '');
    // For cases, omit the "scrutinee = " prefix since it's often a complex expression
    // An `obtain` writes the anonymous constructor, so the prose does too —
    // \u27e8a, b\u27e9, the notation the proof itself contains.
    const prefix = kind.anonymous
      ? '\\langle '
      : simpleScrutinee
        ? `${texNameForProse(simpleScrutinee)} = ${ctorTex}\\,(`
        : `${ctorTex}\\,(`;

    return (
      <>
        <InlineKaTeX latex={prefix} style={{ fontSize: '12px' }} />
        {paramNames!.map((name, i) => {
          // A CONDITION's type is stated inline — "dfPos : 0 < δ_F" — because
          // the fact is the point of binding it. Data names (δ_F : ℝ) and
          // types too wide to inline keep name-only, with the type on hover.
          const t = kind.paramTypeLatex?.[i];
          const inlineType = t || undefined;
          const typeSep = kind.paramIsCondition?.[i] === false ? ' \u2208 ' : ' : ';
          return (
          <React.Fragment key={i}>
            {i > 0 && <InlineKaTeX latex=",\," style={{ fontSize: '12px' }} />}
            <HoverType typeLatex={inlineType ? undefined : t}>
              <span
                onClick={e => handleParamClick(i, e)}
                style={{
                  cursor: 'pointer',
                  borderBottom: selectedParamIndex === i
                    ? '2px solid #58a6ff'
                    : '1px dotted rgba(201, 209, 217, 0.4)',
                  paddingBottom: '1px',
                }}
              >
                <InlineKaTeX latex={texNameForProse(name)} style={{ fontSize: '12px' }} />
              </span>
            </HoverType>
            {inlineType && (
              <>
                <span style={prose}>{typeSep}</span>
                <InlineKaTeX latex={inlineType} style={{ fontSize: '12px' }} />
              </>
            )}
          </React.Fragment>
          );
        })}
        <InlineKaTeX latex={kind.anonymous ? '\\rangle' : ')'} style={{ fontSize: '12px' }} />
      </>
    );
  };

  return (
    <div ref={caseContainerRef} onBlur={handleCaseContainerBlur} tabIndex={-1} style={{ outline: 'none' }}>
      <div style={{ ...rowStyle, fontWeight: 600 }} {...rowHandlers}>
        {/* A sole case carries its own "By cases on x:" — the split has no
            header row of its own, so the destructuring reads as one line. */}
        {kind.lead && kind.anonymous ? (
          /* Both destructure forms read the same way: "Obtain ⟨…⟩ from src."
             — src is the unpacked hypothesis, or (fused have+obtain) the
             justification term itself. Inside a grouped block the word is
             said once, by the block header. */
          compactLead ? null : <span style={{ ...prose, fontWeight: 400 }}>Obtain{' '}</span>
        ) : kind.lead && (
          <>
            <span style={{ ...prose, fontWeight: 400 }}>
              {describeInductionHeader({ tag: 'inductionHeader', scrutinee: kind.lead.scrutinee, isCases: kind.lead.isCases }).lead}{' '}
            </span>
            {kind.lead.scrutineeLatex
              ? <InlineKaTeX latex={kind.lead.scrutineeLatex} style={{ fontSize: '13px' }} />
              : <InlineProseName name={kind.lead.scrutinee} />}
            <span style={{ ...prose, fontWeight: 400 }}>{': '}</span>
          </>
        )}
        {!kind.anonymous && (
          <>
            <span style={{ color: kind.isCases ? '#79c0ff' : (kind.isBaseCase ? '#d2a8ff' : '#79c0ff') }}>
              {kind.isCases ? 'Case' : (kind.isBaseCase ? 'Base case' : 'Inductive step')}
            </span>
            <span style={prose}>{kind.meaningLatex ? ' ' : ' ('}</span>
          </>
        )}
        {kind.meaningLatex ? (
          /* The case's MEANING — the type of the hypothesis it introduces —
             with the name as a small clickable handle: "Case δF ≤ δG (a):". */
          <>
            <InlineKaTeX latex={kind.meaningLatex} style={{ fontSize: '13px' }} />
            {kind.meaningName && paramNames && paramNames.length > 0 && (
              <>
                <span style={{ ...prose, color: '#484f58', fontSize: '11px' }}>{' ('}</span>
                <span
                  onClick={(e) => handleParamClick(0, e)}
                  style={{
                    cursor: 'pointer',
                    fontSize: '11px',
                    color: '#8b949e',
                    borderBottom: selectedParamIndex === 0 ? '2px solid #58a6ff' : '1px dotted rgba(139, 148, 158, 0.4)',
                  }}
                >
                  <InlineKaTeX latex={texNameForProse(kind.meaningName)} style={{ fontSize: '11px' }} />
                </span>
                <span style={{ ...prose, color: '#484f58', fontSize: '11px' }}>)</span>
              </>
            )}
          </>
        ) : (
          renderLabelWithClickableParams()
        )}
        {kind.anonymous ? (
          <span style={{ opacity: kind.chooseSinceLatex !== undefined ? 0.75 : 1 }}>
            <span style={prose}>{' '}from{' '}</span>
            {kind.chooseSinceLatex !== undefined ? (
              <InlineKaTeX latex={kind.chooseSinceLatex} style={{ fontSize: '13px' }} />
            ) : kind.lead?.scrutineeLatex ? (
              <InlineKaTeX latex={kind.lead.scrutineeLatex} style={{ fontSize: '13px' }} />
            ) : (
              <InlineProseName name={kind.lead?.scrutinee ?? ''} />
            )}
            <span style={prose}>.</span>
          </span>
        ) : (
          <span style={prose}>{kind.meaningLatex ? ':' : '):'}</span>
        )}
        {deleteBtn}
      </div>
      {/* What you can DO with the clicked name — the same validated tray the
          context panel shows, brought to where the name is written. */}
      {selectedParamIndex !== null && (tray.suggestions?.length ?? 0) > 0 && (
        <div style={{
          display: 'flex', gap: '4px', flexWrap: 'wrap',
          marginTop: '3px', marginBottom: '2px',
          paddingLeft: `${(item.depth + 1) * 20}px`,
        }}>
          {tray.suggestions!.map((sg) => (
            <button
              key={sg.id}
              style={{ ...suggestionBtnStyle, fontSize: '11px', padding: '2px 8px' }}
              onClick={(e) => { e.stopPropagation(); tray.onApply?.(sg); selectParam(null); }}
              title={sg.description}
            >
              <InlineKaTeX latex={sg.labelLatex ?? sg.label} style={{ fontSize: '11px' }} />
            </button>
          ))}
        </div>
      )}
      {/* Inline rename for selected param — same style as tactic suggestions */}
      {selectedParamIndex !== null && paramNames && (
        <InlineBinderRenameRow
          depth={item.depth}
          label={paramNames[selectedParamIndex]}
          renameKey={`${item.nodeId}-${selectedParamIndex}`}
          defaultValue={paramNames[selectedParamIndex]}
          onConfirm={handleRename}
          onCancel={() => selectParam(null)}
          autoFocus
        />
      )}
    </div>
  );
}

/** Style for a centered display-mode equation block */
const eqBlockStyle: React.CSSProperties = {
  display: 'block',
  padding: '2px 0',
  overflowX: 'auto',
};

function ProseItemView({
  item, prevItem, nextItem, isLastGoalStep, nextHoleNodeId, onClick, onDelete, state, tacticMode, onTacticMode, onPushChange, onClickNode,
  typedContext, registry,
  interactiveGoal, suggestions, selectedPath, onSelectPath,
  editingNames, onEditingNames, editingSuggestionId, onEditingSuggestionId,
  onApplySuggestion, onStartEditingSuggestion,
  selectedBinder, onSelectBinder,
  termBuilder, onSetTermBuilder, holeExtraSlot, applySubgoalCount, caseBranchCount, rewriteSideGoalCount, termBuilderProvider, compactLead,
}: ProseItemViewProps) {
  const [hovered, setHovered] = useState(false);
  const { kind } = item;

  // Check for error on unfold/rewrite/apply/exact/have/simp items
  const hasError = (kind.tag === 'unfold' || kind.tag === 'rewrite' || kind.tag === 'apply'
    || kind.tag === 'exact' || kind.tag === 'have' || kind.tag === 'simp') && !!kind.error;

  const rowStyle: React.CSSProperties = {
    ...proseStyle,
    position: 'relative' as const,
    paddingLeft: `${item.depth * 20 + 12}px`,
    paddingRight: '28px',
    paddingTop: '1px',
    paddingBottom: '1px',
    backgroundColor: hasError
      ? (item.isCursor ? 'rgba(248, 81, 73, 0.12)' : 'rgba(248, 81, 73, 0.06)')
      : (item.isCursor ? 'rgba(88, 166, 255, 0.08)' : 'transparent'),
    borderLeft: hasError
      ? '2px solid #f85149'
      : (item.isCursor ? '2px solid #58a6ff' : '2px solid transparent'),
  };

  const prose: React.CSSProperties = { color: hasError ? '#f85149' : '#c9d1d9' };

  // Does the previous item already show a goal equation (making the pre-goal redundant)?
  const prevShowedGoal = prevItem ? proseItemShowsVisibleGoal(prevItem.kind) : false;

  // "We must show [goal]" / "We need a value of type [goal]" prefix for steps
  // where no prior goal is visible. The isValueType flag switches to
  // "need a value of type" phrasing when the goal is data (like ℝ or Nat)
  // rather than a proposition.
  //
  // Short goals render inline (`We need a value of type ℝ.`); longer ones
  // break to a centered display block for readability.
  function mustShowPrefix(preGoalLatex?: string, isValueType?: boolean): React.ReactNode {
    if (prevShowedGoal) return null;
    // The goal is EXACTLY the last one already on screen (a case split that
    // didn't change it): a paper states a claim once and then refers to it.
    if ((kind.tag === 'hole' || kind.tag === 'exact') && kind.repeatedGoal) {
      return <span style={prose}>We must show the claim above.{' '}</span>;
    }
    // The row being edited expands its goal to a display block (room to read
    // and to click subterms); everything else stays inline when short.
    const goalLead = buildProseGoalLead(preGoalLatex, isValueType, undefined, item.isCursor);
    if (!goalLead) return null;
    if (goalLead.inline) {
      return (
        <>
          <span style={prose}>{goalLead.lead}{' '}</span>
          <InlineKaTeX latex={goalLead.goalLatex} style={{ fontSize: '13px' }} />
          <span style={prose}>.{' '}</span>
        </>
      );
    }
    return (
      <>
        <span style={prose}>{goalLead.lead}</span>
        <span style={eqBlockStyle}>
          <InlineKaTeX latex={goalLead.goalLatex} displayMode />
        </span>
      </>
    );
  }

  // Error message suffix for failed tactics
  const errorSuffix = hasError ? (
    <span style={{ color: '#f85149', fontSize: '11px', marginLeft: '6px' }}>
      ({(kind as any).error})
    </span>
  ) : null;

  // Deletable items get an (x) button on hover
  const isDeletable = kind.tag === 'intro' || kind.tag === 'unfold' || kind.tag === 'rewrite'
    || kind.tag === 'apply' || kind.tag === 'exact' || kind.tag === 'inductionHeader'
    || kind.tag === 'simp' || kind.tag === 'have' || kind.tag === 'suffices'
    || (kind.tag === 'caseHeader' && kind.lead !== undefined);

  const deleteBtn = isDeletable && onDelete && hovered ? (
    <button
      onClick={(e) => { e.stopPropagation(); onDelete(); }}
      style={{
        position: 'absolute',
        right: '4px',
        top: '50%',
        transform: 'translateY(-50%)',
        background: 'none',
        border: 'none',
        color: '#f85149',
        cursor: 'pointer',
        fontSize: '14px',
        padding: '0 4px',
        lineHeight: 1,
        fontFamily: 'inherit',
      }}
      title="Delete this step"
    >
      &times;
    </button>
  ) : null;

  const rowHandlers = {
    onClick,
    onMouseEnter: () => setHovered(true),
    onMouseLeave: () => setHovered(false),
  };

  /** Render a goal section — plain LaTeX, or suppressed on the last step (hole shows it interactively). */
  function renderGoalSection(goalLatex: string | undefined, prefix: string): React.ReactNode {
    if (!goalLatex) return <span style={prose}>.</span>;
    // Last step before hole: suppress plain goal here — the hole renders it interactively
    if (isLastGoalStep) return <span style={prose}>{prefix}</span>;
    // When there's a next hole, clicking the goal focuses it (feels like editing the goal)
    const goalClick = nextHoleNodeId ? (e: React.MouseEvent) => {
      e.stopPropagation();
      onClickNode(nextHoleNodeId);
    } : undefined;
    // Paper-style density: a short resulting goal reads inline in the
    // sentence; only long formulas (or the row being edited) earn a display
    // block. Length is measured in VISIBLE glyphs — see visibleLatexLength.
    if (!item.isCursor && visibleLatexLength(goalLatex) <= 30) {
      return (
        <>
          <span style={prose}>{prefix}{' '}</span>
          <span style={{ cursor: goalClick ? 'pointer' : undefined }} onClick={goalClick}>
            <InlineKaTeX latex={goalLatex} style={{ fontSize: '13px' }} />
          </span>
          <span style={prose}>.</span>
        </>
      );
    }
    return (
      <>
        <span style={prose}>{prefix}</span>
        <span style={{ ...eqBlockStyle, cursor: goalClick ? 'pointer' : undefined }} onClick={goalClick}>
          <InlineKaTeX latex={goalLatex} displayMode />
        </span>
      </>
    );
  }

  switch (kind.tag) {
    case 'intro':
      return (
        <IntroProseItem
          item={item}
          kind={kind}
          rowStyle={rowStyle}
          rowHandlers={rowHandlers}
          prose={prose}
          deleteBtn={deleteBtn}
          renderGoalSection={renderGoalSection}
          state={state}
          onPushChange={onPushChange}
          selectedBinder={selectedBinder}
          onSelectBinder={onSelectBinder}
        />
      );

    case 'unfold':
      return (
        <UnfoldProseItem
          kind={kind}
          rowStyle={rowStyle}
          rowHandlers={rowHandlers}
          prose={prose}
          deleteBtn={deleteBtn}
          mustShowPrefix={mustShowPrefix}
          errorSuffix={errorSuffix}
          renderGoalSection={renderGoalSection}
        />
      );

    case 'fold':
      return (
        <FoldProseItem
          kind={kind}
          rowStyle={rowStyle}
          rowHandlers={rowHandlers}
          prose={prose}
          deleteBtn={deleteBtn}
          mustShowPrefix={mustShowPrefix}
          errorSuffix={errorSuffix}
          renderGoalSection={renderGoalSection}
        />
      );

    case 'rewrite':
      return (
        <RewriteProseItem
          kind={kind}
          rowStyle={rowStyle}
          rowHandlers={rowHandlers}
          prose={prose}
          deleteBtn={deleteBtn}
          mustShowPrefix={mustShowPrefix}
          errorSuffix={errorSuffix}
          renderGoalSection={renderGoalSection}
        />
      );

    case 'apply':
      return (
        <ApplyProseItem
          item={item}
          kind={kind}
          rowStyle={rowStyle}
          rowHandlers={rowHandlers}
          prose={prose}
          deleteBtn={deleteBtn}
          mustShowPrefix={mustShowPrefix}
          errorSuffix={errorSuffix}
          renderGoalSection={renderGoalSection}
        />
      );

    case 'inductionHeader':
      return (
        <InductionHeaderProseItem
          kind={kind}
          rowStyle={rowStyle}
          rowHandlers={rowHandlers}
          prose={prose}
          deleteBtn={deleteBtn}
        />
      );

    case 'caseHeader':
      return (
        <CaseHeaderProseItem
          item={item}
          kind={kind}
          rowStyle={rowStyle}
          rowHandlers={rowHandlers}
          prose={prose}
          deleteBtn={deleteBtn}
          state={state}
          onPushChange={onPushChange}
          compactLead={compactLead}
        />
      );

    case 'exact':
      return (
        <ExactProseItem
          kind={kind}
          rowStyle={rowStyle}
          rowHandlers={rowHandlers}
          prose={prose}
          deleteBtn={deleteBtn}
          mustShowPrefix={mustShowPrefix}
        />
      );

    case 'simp':
      return (
        <SimpProseItem
          kind={kind}
          rowStyle={rowStyle}
          rowHandlers={rowHandlers}
          prose={prose}
          deleteBtn={deleteBtn}
          mustShowPrefix={mustShowPrefix}
          renderGoalSection={renderGoalSection}
        />
      );

    case 'calcChain':
      return (
        <CalcChainProseItem
          item={item}
          kind={kind}
          rowStyle={rowStyle}
          rowHandlers={rowHandlers}
          prose={prose}
          state={state}
          onPushChange={onPushChange}
          onClickNode={onClickNode}
          mustShowPrefix={mustShowPrefix}
        />
      );

    case 'have':
      return (
        <HaveProseItem
          item={item}
          kind={kind}
          rowStyle={rowStyle}
          rowHandlers={rowHandlers}
          prose={prose}
          deleteBtn={deleteBtn}
          renderGoalSection={renderGoalSection}
          nextItem={nextItem}
          state={state}
          onPushChange={onPushChange}
          registry={registry}
          typedContext={typedContext}
          termBuilderProvider={termBuilderProvider}
        />
      );

    case 'suffices':
      return (
        <SufficesProseItem
          kind={kind}
          rowStyle={rowStyle}
          rowHandlers={rowHandlers}
          prose={prose}
          deleteBtn={deleteBtn}
        />
      );

    case 'subgoalHeader':
      return (
        <SubgoalHeaderProseItem
          kind={kind}
          rowStyle={rowStyle}
          rowHandlers={rowHandlers}
          prose={prose}
          expand={item.isCursor}
        />
      );

    case 'qed':
      return <QedProseItem rowStyle={rowStyle} rowHandlers={rowHandlers} />;

    case 'hole': {
      // A hole Lean already considers closed (e.g. the continuation after a
      // goal-closing `simp`) is DONE — show a ✓, never a stray `?`, whether or
      // not the cursor is on it.
      if ((item.kind as { solved?: boolean }).solved) {
        return (
          <div style={rowStyle} {...rowHandlers}>
            <span style={{ color: '#3fb950', fontSize: '13px' }}>✓ solved</span>
          </div>
        );
      }
      if (!item.isCursor) {
        return (
          <div style={rowStyle} {...rowHandlers}>
            <span style={{ color: '#d29922', fontStyle: 'italic' }}>?</span>
          </div>
        );
      }
      // Active hole at cursor — show goal + tactic buttons
      // Reuse the HoleView's tactic input logic
      return (
        <HoleProseView
          nodeId={item.nodeId}
          depth={item.depth}
          goalLatex={kind.goalLatex}

          state={state}
          tacticMode={tacticMode}
          onTacticMode={onTacticMode}
          onPushChange={onPushChange}
          onClickNode={onClickNode}
          typedContext={typedContext}
          registry={registry}
          interactiveGoal={interactiveGoal}
          suggestions={suggestions}
          selectedPath={selectedPath}
          onSelectPath={onSelectPath}
          editingNames={editingNames}
          onEditingNames={onEditingNames}
          editingSuggestionId={editingSuggestionId}
          onEditingSuggestionId={onEditingSuggestionId}
          onApplySuggestion={onApplySuggestion}
          onStartEditingSuggestion={onStartEditingSuggestion}
          termBuilder={termBuilder}
          onSetTermBuilder={onSetTermBuilder}
          holeExtraSlot={holeExtraSlot}
          applySubgoalCount={applySubgoalCount}
            caseBranchCount={caseBranchCount}
          rewriteSideGoalCount={rewriteSideGoalCount}
          termBuilderProvider={termBuilderProvider}
        />
      );
    }

    default:
      return null;
  }
}

/** Render a variable name for prose inline KaTeX.
 *  Single chars stay as math italic (e.g., n, f).
 *  Single letter + digits: subscript (x0 → x_{0}).
 *  Multi-char names use \textsf for clean sans-serif rendering (e.g., sum, minusSucc). */
function texNameForProse(name: string): string {
  return renderNameLatex(name, 'textsf');
}

// ============================================================================
// HoleProseView — active hole in prose view with tactic buttons
// ============================================================================

interface HoleProseViewProps {
  nodeId: ProofNodeId;
  depth: number;
  goalLatex?: string;

  state: ProofTreeState;
  tacticMode: TacticMode;
  onTacticMode: (m: TacticMode) => void;
  onPushChange: (s: ProofTreeState) => void;
  onClickNode: (id: ProofNodeId) => void;
  typedContext: TypedProofContext | null;
  registry?: SyntaxRegistry;
  // Shared goal interaction state
  interactiveGoal: InteractiveGoal | null;
  suggestions: readonly TacticSuggestion[];
  selectedPath: GoalPath | null;
  onSelectPath: (p: GoalPath | null) => void;
  editingNames: string[] | null;
  onEditingNames: (n: string[] | null, suggestionId?: string) => void;
  editingSuggestionId: string | null;
  onEditingSuggestionId: (id: string | null) => void;
  onApplySuggestion: (suggestion: TacticSuggestion) => void;
  onStartEditingSuggestion: (suggestion: TacticSuggestion) => void;
  /** Active term builder (shown inline before the hole). */
  termBuilder?: TermBuilderDisplay | null;
  onSetTermBuilder?: (b: TermBuilderDisplay | null) => void;
  /** Extra content rendered above the tactic buttons (Lean suggestion pills). */
  holeExtraSlot?: React.ReactNode;
  applySubgoalCount?: (name: string) => number;
  /** Branches a split on this scrutinee opens — one per constructor of its
   *  type. `null` when nothing in scope knows. */
  caseBranchCount?: (scrutinee: string) => number | null;
  /** Doc comment of a file lemma, for reason-style citations. */
  lemmaDoc?: (name: string) => string | undefined;
  /** The declaration's raw Lean signature — shown above the Tactics tree. */
  declSignature?: string;
  rewriteSideGoalCount?: (name: string) => number;
  termBuilderProvider?: TermBuilderProvider;
}

function HoleProseView({
  nodeId, depth, goalLatex, state, tacticMode, onTacticMode, onPushChange,
  onClickNode, typedContext, registry,
  interactiveGoal, suggestions, selectedPath, onSelectPath,
  editingNames, onEditingNames, editingSuggestionId, onEditingSuggestionId,
  onApplySuggestion, onStartEditingSuggestion,
  holeExtraSlot, applySubgoalCount, caseBranchCount, rewriteSideGoalCount,
}: HoleProseViewProps) {
  const inputRef = useRef<HTMLInputElement>(null);
  const activeTactic = tacticMode?.tactic ?? null;

  useEffect(() => {
    if (activeTactic && inputRef.current) {
      inputRef.current.focus();
    }
  }, [activeTactic]);

  // (Constructor suggestions are computed in computeTacticSuggestions)

  const handleSubmit = useCallback((value: string) => {
    const result = applyManualProofTreeTactic(state, tacticMode, value, {
      typedContext,
      // Estimate apply's subgoals from the lemma's type in Lean's declaration
      // list, rather than defaulting to a single branch.
      computeApplySubgoalCount: (_root, _cursorNodeId, name) =>
        applySubgoalCount ? applySubgoalCount(name) : 1,
      computeRewriteSideGoalCount: rewriteSideGoalCount,
      computeCaseBranchCount: (scrutinee) => (caseBranchCount ? caseBranchCount(scrutinee) : null),
    });
    if (result) onPushChange(result);
    onTacticMode(null);
  }, [tacticMode, state, onPushChange, onTacticMode, typedContext, registry, applySubgoalCount, caseBranchCount, rewriteSideGoalCount]);

  const handleKeyDown = useCallback((e: React.KeyboardEvent<HTMLInputElement>) => {
    if (e.key === 'Enter') {
      e.preventDefault();
      e.stopPropagation();
      handleSubmit(e.currentTarget.value);
    }
    if (e.key === 'Escape') {
      e.preventDefault();
      e.stopPropagation();
      onTacticMode(null);
    }
  }, [handleSubmit, onTacticMode]);

  const rowStyle: React.CSSProperties = {
    ...proseStyle,
    paddingLeft: `${depth * 20 + 12}px`,
    paddingRight: '12px',
    paddingTop: '2px',
    paddingBottom: '2px',
    backgroundColor: 'rgba(88, 166, 255, 0.08)',
    borderLeft: '2px solid #58a6ff',
  };

  return (
    <div style={rowStyle} onClick={() => onClickNode(nodeId)}>
      {/* Interactive goal display — centered and large */}
      <div style={{ marginBottom: '6px', textAlign: 'center' }}>
        <GoalInteraction
          interactiveGoal={interactiveGoal}
          suggestions={suggestions}
          selectedPath={selectedPath}
          onSelectPath={onSelectPath}
          editingNames={editingNames}
          onEditingNames={onEditingNames}
          editingSuggestionId={editingSuggestionId}
          onEditingSuggestionId={onEditingSuggestionId}
          onApplySuggestion={onApplySuggestion}
          onStartEditingSuggestion={onStartEditingSuggestion}
          fallbackGoalLatex={goalLatex}
          goalFontSize="16px"
        />
      </div>

      {/* Lean-backed suggestion pills (rendered inline, above the tactic
          buttons — where the TT path surfaced focus recommendations). */}
      {holeExtraSlot}

      {/* Tactic buttons or input */}
      {!activeTactic ? (
        <span style={{ display: 'inline-flex', gap: '4px', flexWrap: 'wrap' }}>
          <span style={{ color: '#d29922', fontStyle: 'italic', marginRight: '6px' }}>?</span>
          {[
            { tactic: 'intros' as const, label: 'Intros' },
            { tactic: 'induction' as const, label: 'Induction' },
            { tactic: 'cases' as const, label: 'Cases' },
            { tactic: 'exact' as const, label: 'Exact' },
            { tactic: 'unfold' as const, label: 'Unfold' },
            { tactic: 'fold' as const, label: 'Fold' },
            { tactic: 'rewrite' as const, label: 'Rewrite' },
            { tactic: 'rewrite_rev' as const, label: 'Rewrite\u2190' },
            { tactic: 'apply' as const, label: 'Apply' },
            { tactic: 'simp' as const, label: 'Simp' },
            { tactic: 'have' as const, label: 'Have' },
          ].filter(({ tactic }) =>
            // `fold` isn't a core Lean tactic (it'd emit a lost `-- fold`
            // comment); hide it on the Lean backend (applySubgoalCount present).
            !(tactic === 'fold' && applySubgoalCount)
          ).map(({ tactic, label }) => (
            <button
              key={tactic}
              style={proseBtnStyle}
              onClick={(e) => { e.stopPropagation(); onTacticMode({ tactic }); }}
            >
              {label}
            </button>
          ))}
        </span>
      ) : (
        <span style={{ display: 'inline-flex', gap: '4px', alignItems: 'center' }}>
          <span style={keywordStyle}>
            {activeTactic === 'intros' ? 'Given' :
             activeTactic === 'induction' ? 'Induct on' :
             activeTactic === 'cases' ? 'By cases on' :
             activeTactic === 'unfold' ? 'Unfold' :
             activeTactic === 'fold' ? 'Fold' :
             activeTactic === 'rewrite' ? 'Rewrite' :
             activeTactic === 'rewrite_rev' ? 'Rewrite\u2190' :
             activeTactic === 'apply' ? 'Apply' :
             activeTactic === 'simp' ? 'Simp' :
             activeTactic === 'have' ? 'Have' :
             'by'}
          </span>
          <input
            ref={inputRef}
            autoFocus
            style={inputStyle}
            placeholder={
              activeTactic === 'intros' ? 'n, m, f' :
              activeTactic === 'induction' ? 'variable name' :
              activeTactic === 'cases' ? 'hF   or   leTotal a b' :
              activeTactic === 'unfold' ? 'definition name' :
              activeTactic === 'rewrite' || activeTactic === 'rewrite_rev' ? 'lemma name' :
              activeTactic === 'apply' ? 'lemma name' :
              activeTactic === 'simp' ? '(empty = all @simp lemmas)' :
              activeTactic === 'have' ? 'name := expression' :
              'proof expression'
            }
            onKeyDown={handleKeyDown}
            onClick={(e) => e.stopPropagation()}
          />
          <button style={proseBtnStyle} onClick={(e) => {
            e.stopPropagation();
            if (inputRef.current) handleSubmit(inputRef.current.value);
          }}>
            {'↵'}
          </button>
          <button style={proseBtnStyle} onClick={(e) => { e.stopPropagation(); onTacticMode(null); }}>
            Cancel
          </button>
        </span>
      )}
    </div>
  );
}

const proseBtnStyle: React.CSSProperties = {
  padding: '1px 6px',
  fontSize: '10px',
  fontFamily: FONT_UI,
  color: '#8b949e',
  background: '#21262d',
  border: '1px solid #30363d',
  borderRadius: '3px',
  cursor: 'pointer',
};
