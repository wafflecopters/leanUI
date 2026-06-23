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

import React, { useCallback, useEffect, useMemo, useRef, useState } from 'react';
import katex from 'katex';
import { TTerm } from '../compiler/surface';
import { TTKTerm } from '../compiler/kernel';
import { DefinitionsMap } from '../compiler/term';
import { SyntaxRegistry } from '../math-editor/syntax-registry';
import {
  ProofTreeHistory, ProofTreeState, ProofNode, CaseNode, SimpNode, ProofNodeId,
  computeContext,
  applySimp,
  moveCursorUp, moveCursorDown,
  pushState, updateCurrent, undo, redo,
} from '../proof-tree/proof-tree';
import { runSimp } from '../tactics/simp-tactic';
import {
  TypedProofContext, ValidationResult, computeTypedContext, computeApplySubgoalCount,
  NodeGoalInfo, replayEntireTree, replayToEngine,
  InductiveMap, generateCaseInfos,
} from '../proof-tree/goal-computation';
import { buildReverseRegistry, ReverseRegistry } from '../math-editor/tt-to-math';
import { ProseItem, ProseItemKind, IntroToken, CalcChainStep, generateProofProse } from '../proof-tree/proof-prose';
import {
  buildProseGoalLead,
  findLastInteractiveGoalStepIndex,
  findNextHoleNodeId,
  proseItemShowsVisibleGoal,
} from '../proof-tree/prose-view-helpers';
import {
  describeApplyProse,
  describeExactProse,
  describeInductionHeader,
  describeRewriteReference,
} from '../proof-tree/prose-row-helpers';
import { renderInteractiveGoal, InteractiveGoal, GoalPath } from '../proof-tree/interactive-goal';
import {
  computeRewriteSuggestionsIncremental,
  TacticSuggestion,
  RewriteProgress,
} from '../proof-tree/tactic-suggestions';
import {
  EMPTY_GOAL_INTERACTION_STATE,
  clearGoalInteractionAfterApply,
  clearGoalInteractionForCursorChange,
  computeGoalInteractionHypothesisSuggestions,
  computeGoalInteractionSuggestions,
  selectGoalInteractionBinder,
  selectGoalInteractionPath,
  startGoalInteractionEditing,
  toggleGoalInteractionHypothesis,
  updateGoalInteractionEditingNames,
  type GoalInteractionState,
  type SelectedBinder,
} from '../proof-tree/goal-interaction-state';
import { renderNameLatex, normalizeBinderNameInput } from '../proof-tree/name-latex';
import {
  clearTermBuilderSlotFromGoal,
  fillTermBuilderSlotFromGoal,
  TermBuilderState,
  TermSlot,
} from '../proof-tree/term-builder';
import {
  addInductionCaseInProofTree,
  applyManualProofTreeTactic,
  applySuggestionToProofTreeState,
  clearHaveTermBuilderSlotInProofTree,
  clearProofTreeNode,
  commitHaveExprSourceInProofTree,
  commitProofTreeBinderRename,
  convertMathEditorSourceToUnicode,
  fillHaveTermBuilderSlotInProofTree,
  hoistTermBuilderSlotToHave,
  insertHaveFromTermBuilder,
  openHaveExprTermBuilder,
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
  /** Surface type of the declaration — enables real type info in goal panel */
  surfaceType?: TTerm;
  /** Kernel type of the declaration — enables unfold normalization */
  kernelType?: TTKTerm;
  /** Definitions map — needed for unfold to normalize terms */
  definitions?: DefinitionsMap;
  /** Syntax registry for structured math rendering of types/goals */
  registry?: SyntaxRegistry;
  /** Map of inductive type names to their constructors — enables case-specific goals */
  inductiveMap?: InductiveMap;
  /** Name of the declaration being proved — used to filter self-referential suggestions */
  currentDeclName?: string;
  /** Pre-computed tactic trace from compilation — avoids re-running tactics */
  tacticTrace?: import('../tactics/tactic-session').TacticStepTrace[];
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
  }, [latex]);

  return <span ref={ref} style={style} />;
}

/** Convert a plain-text math expression to LaTeX. Simple heuristic. */
function textToLatex(text: string): string {
  return text
    .replace(/'/g, "'")     // prime
    .replace(/\bNat\b/g, '\\mathbb{N}')
    .replace(/\bType\b/g, '\\text{Type}')
    .replace(/->/g, '\\to ')
    .replace(/=>/g, '\\Rightarrow ')
    .replace(/\brefl\b/g, '\\text{refl}');
}

// ============================================================================
// Tactic input state (ephemeral, per-hole)
// ============================================================================

type TacticMode = null | ProofTreeManualTacticMode;

// ============================================================================
// Main Component
// ============================================================================

export function ProofTreeEditor({ history, onHistoryChange, surfaceType, kernelType, definitions, registry, inductiveMap, currentDeclName, tacticTrace, goalMapOverride, typedContextOverride, interactiveGoalOverride, onGoalPathSelect, goalExtraSlot }: ProofTreeEditorProps) {
  const containerRef = useRef<HTMLDivElement>(null);
  const state = history.current;

  // Once the user interactively edits the proof tree, the compiled
  // tacticTrace is stale — it was produced for the ORIGINAL proof tree
  // and doesn't match the edited one. Using it for replay produces wrong
  // goals (e.g., ∀ n ∈ ℕ still showing after intros). Invalidate the
  // trace when the undo stack has entries (= user has made edits).
  const effectiveTrace = history.undoStack.length > 0 ? undefined : tacticTrace;

  // Ephemeral tactic input mode (not part of immutable state)
  const [tacticMode, setTacticMode] = useState<TacticMode>(null);
  const [activeTab, setActiveTab] = useState<'tactics' | 'proof'>('proof');

  // Goal interaction state (shared between GoalPanel and prose view)
  const [goalInteractionState, setGoalInteractionState] = useState<GoalInteractionState>(
    EMPTY_GOAL_INTERACTION_STATE,
  );
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
    setGoalInteractionState(prev => toggleGoalInteractionHypothesis(prev, hypIndex));
  }, []);

  const emptyRegistry = useMemo<SyntaxRegistry>(() => ({ symbolMap: new Map(), entries: [] }), []);

  // Compute typed context at cursor position (uses surface type when available).
  // Lean backend: when a typedContextOverride is supplied, use it directly.
  const typedContext = useMemo<TypedProofContext | null>(() => {
    if (typedContextOverride !== undefined) return typedContextOverride;
    if (surfaceType) {
      return computeTypedContext(
        state.root, state.cursor.nodeId, surfaceType, registry ?? emptyRegistry,
        inductiveMap, kernelType, definitions, effectiveTrace,
      );
    }
    // Fallback: use untyped context, convert to TypedProofContext shape
    const ctx = computeContext(state.root, state.cursor.nodeId);
    if (!ctx) return null;
    return {
      hypotheses: ctx.hypotheses.map(h => ({ name: h.name, type: '' })),
      caseLabel: ctx.caseLabel,
      inductionVar: ctx.inductionVar,
      goal: ctx.goalDescription,
    };
  }, [typedContextOverride, state.root, state.cursor.nodeId, surfaceType, kernelType, definitions, registry, emptyRegistry, inductiveMap]);

  // Compute interactive goal from kernel info (shared between GoalPanel and prose
  // view). Lean backend: a supplied interactiveGoalOverride takes over.
  const interactiveGoal = useMemo<InteractiveGoal | null>(() => {
    if (interactiveGoalOverride !== undefined) return interactiveGoalOverride;
    if (!typedContext?.kernelGoal) return null;
    if (typedContext.validation?.status === 'solved') return null;
    const { engine, goal, definitions: defs, rev: r } = typedContext.kernelGoal;
    try {
      return renderInteractiveGoal(engine, goal, defs, r);
    } catch {
      return null;
    }
  }, [interactiveGoalOverride, typedContext?.kernelGoal, typedContext?.validation]);

  // Augment kernelGoal with currentDeclName for self-reference filtering
  const kernelGoalWithDeclName = useMemo(() => {
    if (!typedContext?.kernelGoal) return undefined;
    if (!currentDeclName) return typedContext.kernelGoal;
    return { ...typedContext.kernelGoal, currentDeclName };
  }, [typedContext?.kernelGoal, currentDeclName]);

  // Compute tactic suggestions from selection (synchronous: intro, unfold, induction)
  // Incremental rewrite suggestions (scan hypotheses, try targeted rewrites)
  const [rewriteProgress, setRewriteProgress] = useState<RewriteProgress | null>(null);
  useEffect(() => {
    setRewriteProgress(null);
    if (!goalSelectedPath || !interactiveGoal || !kernelGoalWithDeclName) return;
    const cancel = computeRewriteSuggestionsIncremental(
      goalSelectedPath, interactiveGoal, kernelGoalWithDeclName,
      (progress) => setRewriteProgress(progress),
    );
    return cancel;
  }, [goalSelectedPath, interactiveGoal, kernelGoalWithDeclName]);

  // Compute binder-specific suggestions when a binder is selected in the prose view
  const goalSuggestions = useMemo<readonly TacticSuggestion[]>(() => {
    return computeGoalInteractionSuggestions(
      goalInteractionState,
      interactiveGoal,
      definitions,
      kernelGoalWithDeclName,
      inductiveMap,
      rewriteProgress,
    );
  }, [
    goalInteractionState,
    interactiveGoal,
    definitions,
    kernelGoalWithDeclName,
    inductiveMap,
    rewriteProgress,
  ]);

  const hypSuggestions = useMemo<readonly TacticSuggestion[]>(() => {
    return computeGoalInteractionHypothesisSuggestions(
      goalInteractionState,
      typedContext,
      definitions,
    );
  }, [goalInteractionState, typedContext, definitions]);

  // Reset goal selection and binder selection when cursor changes
  useEffect(() => {
    setGoalInteractionState(clearGoalInteractionForCursorChange());
  }, [state.cursor.nodeId]);

  // Compute goal map for prose view (replays entire tree, not just to cursor)
  const rev = useMemo<ReverseRegistry | null>(() => {
    if (!registry) return null;
    return buildReverseRegistry(registry, definitions ?? undefined);
  }, [registry, definitions]);

  const goalMap = useMemo<Map<ProofNodeId, NodeGoalInfo>>(() => {
    // Lean backend: a supplied goal map (from the Lean round-trip) takes over.
    if (goalMapOverride) return goalMapOverride;
    if (!kernelType || !definitions || !rev) return new Map();
    try {
      return replayEntireTree(state.root, kernelType, definitions, rev, effectiveTrace);
    } catch {
      return new Map();
    }
  }, [goalMapOverride, state.root, kernelType, definitions, rev, effectiveTrace]);

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
    const result = applySuggestionToProofTreeState(state, suggestion, {
      inductiveMap,
      registry,
      typedContext,
      definitions,
      editingNames: goalInteractionState.editingNames,
      editingSuggestionId: goalInteractionState.editingSuggestionId,
    });

    if (result) {
      pushChange(result);
      setGoalInteractionState(clearGoalInteractionAfterApply());
    }
  }, [
    state,
    inductiveMap,
    registry,
    typedContext,
    definitions,
    goalInteractionState.editingNames,
    goalInteractionState.editingSuggestionId,
    pushChange,
  ]);

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

  return (
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
                inductiveMap={inductiveMap}
                registry={registry}
                kernelType={kernelType}
                definitions={definitions}
                goalMap={goalMap}
              />
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
                inductiveMap={inductiveMap}
                registry={registry}
                kernelType={kernelType}
                definitions={definitions}
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
                rewriteProgress={rewriteProgress}
                selectedBinder={selectedBinder}
                onSelectBinder={handleSelectBinder}
                termBuilder={null}
                onSetTermBuilder={() => {}}
                holeExtraSlot={goalExtraSlot}
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
          rewriteProgress={rewriteProgress}
          onOpenTermBuilder={() => {}}
          extraSlot={goalExtraSlot}
        />
      </SplitPane>
    </div>
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
  validation?: ValidationResult;
  /** Progress of incremental rewrite suggestion scanning. */
  rewriteProgress?: RewriteProgress | null;
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
  rewriteProgress, goalFontSize,
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
      {(suggestions.length > 0 || (rewriteProgress && !rewriteProgress.done)) && (
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
          {/* Rewrite scanning progress */}
          {rewriteProgress && !rewriteProgress.done && (
            <div style={{
              padding: '3px 0',
              fontSize: '10px',
              color: '#484f58',
              display: 'flex',
              alignItems: 'center',
              gap: '4px',
            }}>
              <span style={{
                display: 'inline-block',
                width: '10px',
                height: '10px',
                border: '1.5px solid #484f58',
                borderTopColor: '#58a6ff',
                borderRadius: '50%',
                animation: 'spin 0.8s linear infinite',
              }} />
              checking rewrites ({rewriteProgress.checked}/{rewriteProgress.total})
            </div>
          )}
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
  rewriteProgress,
  onOpenTermBuilder: _onOpenTermBuilder,
  extraSlot,
}: {
  context: TypedProofContext | null;
  extraSlot?: React.ReactNode;
  state?: ProofTreeState;
  onPushChange?: (s: ProofTreeState) => void;
  /** Open the term builder inline in the prose view. */
  onOpenTermBuilder?: (builder: TermBuilderState) => void;
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
  rewriteProgress?: RewriteProgress | null;
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
            rewriteProgress={rewriteProgress}
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
  state, onPushChange, registry: _registry,
  definitions, typedContext,
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
  definitions?: DefinitionsMap;
  typedContext: TypedProofContext | null;
}) {
  const [builderState, setBuilderState] = useState<TermBuilderState | null>(null);
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

  // Open the term builder by parsing the have expression into slots
  const openBuilder = useCallback(() => {
    const opened = openHaveExprTermBuilder(kind.expr, typedContext?.kernelGoal, definitions);
    if (opened) {
      setBuilderState(opened.builderState);
    }
  }, [kind.expr, definitions, typedContext]);

  if (builderState) {
    return (
      <div style={rowStyle}>
        <ProofTreeTermBuilderPanel
          builderState={builderState}
          registry={_registry}
          onFillSlot={(slotIndex, sourceExpr) => {
            const rebuilt = fillHaveTermBuilderSlotInProofTree(
              state,
              item.nodeId,
              builderState,
              slotIndex,
              sourceExpr,
              typedContext?.kernelGoal,
              definitions,
            );
            if (!rebuilt) return;
            setBuilderState(rebuilt.builderState);
            onPushChange(rebuilt.state);
          }}
          onClearSlot={(slotIndex) => {
            const rebuilt = clearHaveTermBuilderSlotInProofTree(
              state,
              item.nodeId,
              builderState,
              slotIndex,
              typedContext?.kernelGoal,
              definitions,
            );
            if (!rebuilt) return;
            setBuilderState(rebuilt.builderState);
            onPushChange(rebuilt.state);
          }}
          onConfirm={() => setBuilderState(null)}
          onCancel={() => setBuilderState(null)}
          onHoistToHave={(slotIndex) => {
            if (!builderState) return;
            const updated = hoistTermBuilderSlotToHave(state, item.nodeId, builderState, slotIndex, definitions);
            if (!updated) return;
            onPushChange(updated);
            setBuilderState(null);
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
      <span style={{ ...prose, ...errorStyle }}>Observe that{' '}</span>
      {displayType ? (
        <InlineKaTeX latex={displayType} style={{ fontSize: '13px' }} />
      ) : (
        <InlineKaTeX latex={texNameForProse(kind.name)} style={{ fontSize: '13px' }} />
      )}
      <span style={prose}>{' '}(</span>
      {nameEditor}
      <span style={prose}>)</span>
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

function TermBuilderView({
  builderState,
  onFillSlot,
  onClearSlot,
  onConfirm: _onConfirm,
  onCancel,
  registry,
  onHoistToHave,
}: {
  builderState: TermBuilderState;
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
      {/* Header */}
      <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center', marginBottom: '6px' }}>
        <span style={{ fontSize: '11px', color: '#8b949e', letterSpacing: '0.03em' }}>
          BUILDING TERM
        </span>
        <button
          onClick={onCancel}
          style={{ background: 'none', border: 'none', color: '#f85149', cursor: 'pointer', fontSize: '11px' }}
        >
          ✕
        </button>
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
                  if (editorState && registry) {
                    const result = convertToSource(registry, editorState.root.children);
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
                if (editorState && registry) {
                  const result = convertToSource(registry, editorState.root.children);
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
  inductiveMap?: InductiveMap;
  registry?: SyntaxRegistry;
  kernelType?: TTKTerm;
  definitions?: DefinitionsMap;
  goalMap?: Map<ProofNodeId, NodeGoalInfo>;
}

function ProofNodeView(props: NodeViewProps) {
  switch (props.node.tag) {
    case 'hole': return <HoleView {...props} />;
    case 'intros': return <IntrosView {...props} />;
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

function HoleView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, inductiveMap, registry, kernelType, definitions }: NodeViewProps) {
  const isFocused = cursorId === node.id;
  const inputRef = useRef<HTMLInputElement>(null);

  const handleSubmit = useCallback((value: string) => {
    const result = applyManualProofTreeTactic(state, tacticMode, value, {
      typedContext,
      inductiveMap,
      registry,
      kernelType,
      definitions,
      computeApplySubgoalCount: (root, cursorNodeId, rootKernelType, defs, name) =>
        computeApplySubgoalCount(root, cursorNodeId, rootKernelType, defs, name),
    });
    if (result) onPushChange(result);
    onTacticMode(null);
  }, [tacticMode, state, onPushChange, onTacticMode, typedContext, inductiveMap, registry, kernelType, definitions]);

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
              activeTactic === 'unfold' ? 'definition name' :
              activeTactic === 'fold' ? 'definition name' :
              activeTactic === 'rewrite' ? 'lemma name' :
              activeTactic === 'rewrite_rev' ? 'lemma name' :
              activeTactic === 'apply' ? 'lemma name' :
              activeTactic === 'simp' ? '(empty = all @simp lemmas)' :
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

function IntrosView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, inductiveMap, registry, kernelType, definitions, goalMap }: NodeViewProps) {
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
        inductiveMap={inductiveMap}
        registry={registry}
        kernelType={kernelType}
        definitions={definitions}
        goalMap={goalMap}
      />
    </>
  );
}

// ============================================================================
// InductionView
// ============================================================================

function InductionView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, inductiveMap, registry, kernelType, definitions, goalMap }: NodeViewProps) {
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
          inductiveMap={inductiveMap}
          registry={registry}
          kernelType={kernelType}
          definitions={definitions}
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
  inductiveMap?: InductiveMap;
  registry?: SyntaxRegistry;
  kernelType?: TTKTerm;
  definitions?: DefinitionsMap;
  goalMap?: Map<ProofNodeId, NodeGoalInfo>;
}

function CaseView({
  caseNode, caseIndex, inductionId, depth,
  cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode,
  typedContext, inductiveMap, registry, kernelType, definitions, goalMap,
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
          inductiveMap={inductiveMap}
          registry={registry}
          kernelType={kernelType}
          definitions={definitions}
          goalMap={goalMap}
        />
      )}
    </>
  );
}

// ============================================================================
// UnfoldView — renders "unfold <name>,"
// ============================================================================

function UnfoldView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, inductiveMap, registry, kernelType, definitions, goalMap }: NodeViewProps) {
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
        inductiveMap={inductiveMap}
        registry={registry}
        kernelType={kernelType}
        definitions={definitions}
        goalMap={goalMap}
      />
    </>
  );
}

// ============================================================================
// FoldView — renders "fold <name>,"
// ============================================================================

function FoldView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, inductiveMap, registry, kernelType, definitions, goalMap }: NodeViewProps) {
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
        inductiveMap={inductiveMap}
        registry={registry}
        kernelType={kernelType}
        definitions={definitions}
        goalMap={goalMap}
      />
    </>
  );
}

// ============================================================================
// RewriteView — renders "rewrite <name>,"
// ============================================================================

function RewriteView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, inductiveMap, registry, kernelType, definitions, goalMap }: NodeViewProps) {
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
        inductiveMap={inductiveMap}
        registry={registry}
        kernelType={kernelType}
        definitions={definitions}
        goalMap={goalMap}
      />
    </>
  );
}

// ============================================================================
// ApplyView — renders "apply <name>,"
// ============================================================================

function ApplyView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, inductiveMap, registry, kernelType, definitions, goalMap }: NodeViewProps) {
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
          inductiveMap={inductiveMap}
          registry={registry}
          kernelType={kernelType}
          definitions={definitions}
          goalMap={goalMap}
        />
      ))}
    </>
  );
}

// ============================================================================
// SimpView
// ============================================================================

function SimpView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, inductiveMap, registry, kernelType, definitions, goalMap }: NodeViewProps) {
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
          inductiveMap={inductiveMap}
          registry={registry}
          kernelType={kernelType}
          definitions={definitions}
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
        inductiveMap={inductiveMap}
        registry={registry}
        kernelType={kernelType}
        definitions={definitions}
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
  inductiveMap?: InductiveMap;
  registry?: SyntaxRegistry;
  kernelType?: TTKTerm;
  definitions?: DefinitionsMap;
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
  rewriteProgress?: RewriteProgress | null;
  // Binder selection from clickable tokens in prose
  selectedBinder: SelectedBinder | null;
  onSelectBinder: (b: SelectedBinder | null) => void;
  // Inline term builder
  termBuilder?: TermBuilderState | null;
  onSetTermBuilder?: (b: TermBuilderState | null) => void;
  // Extra content rendered inline above the active hole's tactic buttons
  // (Lean-backed suggestion pills); mirrors where the TT path showed them.
  holeExtraSlot?: React.ReactNode;
}

function ProofProseView({
  items, state, tacticMode, onTacticMode, onPushChange, onClickNode,
  typedContext, inductiveMap, registry, kernelType, definitions,
  interactiveGoal, suggestions, selectedPath, onSelectPath,
  editingNames, onEditingNames, editingSuggestionId, onEditingSuggestionId,
  onApplySuggestion, onStartEditingSuggestion,
  rewriteProgress, selectedBinder, onSelectBinder,
  termBuilder, onSetTermBuilder, holeExtraSlot,
}: ProseViewProps) {
  if (items.length === 0) {
    return <div style={{ padding: '8px 12px', color: '#484f58', fontStyle: 'italic' }}>No proof steps yet.</div>;
  }

  // Find the last goal-showing step before the active cursor hole.
  // This step will render its goal interactively instead of as plain LaTeX.
  const lastGoalStepIdx = findLastInteractiveGoalStepIndex(items);

  return (
    <div>
      {items.map((item, idx) => {
        // Deletable items: anything except hole, qed, caseHeader
        const isDeletable = item.kind.tag === 'intro' || item.kind.tag === 'unfold'
          || item.kind.tag === 'rewrite' || item.kind.tag === 'apply'
          || item.kind.tag === 'exact' || item.kind.tag === 'inductionHeader'
          || item.kind.tag === 'have' || item.kind.tag === 'simp' || item.kind.tag === 'suffices';
        const handleDelete = isDeletable ? () => {
          const result = clearProofTreeNode(state, item.nodeId);
          if (result) onPushChange(result);
        } : undefined;

        // Find the next hole's nodeId so clicking the goal can focus it
        const nextHoleNodeId = findNextHoleNodeId(items, idx);

        return (
          <ProseItemView
            key={`${item.nodeId}-${idx}`}
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
            inductiveMap={inductiveMap}
            registry={registry}
            kernelType={kernelType}
            definitions={definitions}
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
            rewriteProgress={rewriteProgress}
            selectedBinder={selectedBinder}
            onSelectBinder={onSelectBinder}
            termBuilder={termBuilder}
            onSetTermBuilder={onSetTermBuilder}
            holeExtraSlot={holeExtraSlot}
          />
        );
      })}
    </div>
  );
}

// ============================================================================
// ProseItemView — renders a single prose item
// ============================================================================

interface ProseItemViewProps {
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
  inductiveMap?: InductiveMap;
  registry?: SyntaxRegistry;
  kernelType?: TTKTerm;
  definitions?: DefinitionsMap;
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
  rewriteProgress?: RewriteProgress | null;
  // Binder selection from clickable tokens in prose
  selectedBinder: SelectedBinder | null;
  onSelectBinder: (b: SelectedBinder | null) => void;
  // Inline term builder
  termBuilder?: TermBuilderState | null;
  onSetTermBuilder?: (b: TermBuilderState | null) => void;
  // Extra content rendered inline above the active hole's tactic buttons.
  holeExtraSlot?: React.ReactNode;
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
  builderState: TermBuilderState;
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
      <div style={{ paddingLeft: '20px' }}>
        <span style={prose}>since{' '}</span>
        <span
          onClick={onOpenBuilder}
          style={{ cursor: 'pointer', borderBottom: '1px dashed rgba(88, 166, 255, 0.4)' }}
          title="Click to edit expression"
        >
          <InlineKaTeX latex={proofLatex} style={{ fontSize: '13px' }} />
        </span>
        <span style={prose}>.</span>
      </div>
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
    return <span style={prose}>which is true, {constructorPhrase}</span>;
  }

  return (
    <>
      <span style={prose}>which is true, by{' '}</span>
      <InlineProseName name={theoremName ?? ''} />
    </>
  );
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
      <span style={prose}>which is true, by definition of{' '}</span>
      <InlineProseName name={kind.name} />
      {errorSuffix}
      {renderGoalSection(kind.goalLatex, ', if')}
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
      {renderGoalSection(kind.goalLatex, ', if')}
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
      <span style={prose}>which is true, because{' '}</span>
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
      {renderGoalSection(kind.goalLatex, ', if')}
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
        {renderGoalSection(applyDescription.subgoals[0], ', if')}
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
      <span style={prose}>, after showing {applyDescription.subgoals.length} subgoals:</span>
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
      {renderGoalSection(kind.goalLatex, ', we get')}
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

  return (
    <ProseRow rowStyle={rowStyle} rowHandlers={rowHandlers} deleteBtn={deleteBtn}>
      {mustShowPrefix(kind.goalLatex, kind.isValueType)}
      {description.mode === 'solved' ? (
        <>
          <span style={prose}>{description.lead}{' '}</span>
          <InlineKaTeX latex={description.displayLatex} style={{ fontSize: '13px' }} />
          <span style={prose}>.</span>
        </>
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
      <span style={{ color: '#484f58', fontSize: '11px', whiteSpace: 'nowrap', marginLeft: '12px' }}>
        (<InlineKaTeX latex={texNameForProse(step.lemmaName)} style={{ fontSize: '11px' }} />)
      </span>
      <button
        onClick={(e) => { e.stopPropagation(); onDelete(); }}
        style={{
          background: 'none', border: 'none', color: '#f85149',
          cursor: 'pointer', fontSize: '13px', padding: '0 2px',
          opacity: 0.5, lineHeight: 1,
        }}
        title="Delete this step"
      >&times;</button>
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
      {kind.goalLatex && (
        <span style={eqBlockStyle}>
          <InlineKaTeX latex={kind.goalLatex} displayMode />
        </span>
      )}
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
}: {
  kind: Extract<ProseItemKind, { tag: 'subgoalHeader' }>;
  rowStyle: React.CSSProperties;
  rowHandlers: ProseRowHandlers;
  prose: React.CSSProperties;
}) {
  const goalLead = buildProseGoalLead(kind.goalLatex, kind.isValueType);
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
          groups.map((group, gi) => (
            <React.Fragment key={gi}>
              {gi > 0 && (
                gi === groups.length - 1
                  ? <span style={prose}>{' '}and{' '}</span>
                  : <span style={prose}>,{' '}</span>
              )}
              {group.tokens.map((token, ti) => (
                <React.Fragment key={ti}>
                  {ti > 0 && <span style={prose}>,{' '}</span>}
                  <span
                    onClick={e => handleTokenClick(token, e)}
                    style={{
                      cursor: 'pointer',
                      borderBottom: isTokenSelected(token)
                        ? '2px solid #58a6ff'
                        : '1px dotted rgba(201, 209, 217, 0.4)',
                      paddingBottom: '1px',
                    }}
                  >
                    <InlineKaTeX latex={token.nameLatex} style={{ fontSize: '13px' }} />
                  </span>
                </React.Fragment>
              ))}
              <span style={prose}>{' '}: </span>
              <InlineKaTeX latex={group.typeLatex} style={{ fontSize: '13px' }} />
            </React.Fragment>
          ))
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
  item, kind, rowStyle, rowHandlers, prose,
  state, onPushChange,
}: {
  item: ProseItem;
  kind: Extract<ProseItemKind, { tag: 'caseHeader' }>;
  rowStyle: React.CSSProperties;
  rowHandlers: ProseRowHandlers;
  prose: React.CSSProperties;
  state: ProofTreeState;
  onPushChange: (s: ProofTreeState) => void;
}) {
  const [selectedParamIndex, setSelectedParamIndex] = useState<number | null>(null);
  const caseContainerRef = useRef<HTMLDivElement>(null);

  const paramNames = kind.constructorParamNames;
  const hasParams = paramNames && paramNames.length > 0;

  const handleParamClick = (idx: number, e: React.MouseEvent) => {
    e.stopPropagation();
    setSelectedParamIndex(prev => prev === idx ? null : idx);
  };

  const handleRename = useCallback((newName: string) => {
    if (selectedParamIndex === null) return;
    const result = commitProofTreeBinderRename(state, {
      tag: 'caseParam',
      nodeId: item.nodeId,
      paramIndex: selectedParamIndex,
    }, newName);
    if (result) onPushChange(result);
  }, [selectedParamIndex, state, item.nodeId, onPushChange]);

  // Dismiss selection when focus leaves the container
  const handleCaseContainerBlur = useCallback((e: React.FocusEvent) => {
    if (caseContainerRef.current?.contains(e.relatedTarget as Node)) return;
    const active = document.activeElement;
    if (active instanceof HTMLInputElement) {
      handleRename(active.value);
    }
    setSelectedParamIndex(null);
  }, [handleRename]);

  // Render the label with clickable param names.
  // For induction: "scrutinee = Constructor(param1, param2)"
  // For cases: "Constructor(param1, param2)" (no scrutinee prefix)
  const renderLabelWithClickableParams = () => {
    if (!hasParams || !kind.constructorName) {
      // No params or missing data — render as before
      return <InlineKaTeX latex={kind.labelLatex} style={{ fontSize: '12px' }} />;
    }

    const ctorTex = texNameForProse(kind.constructorName);
    // For cases, omit the "scrutinee = " prefix since it's often a complex expression
    const prefix = kind.isCases
      ? `${ctorTex}\\,(`
      : kind.scrutinee
        ? `${texNameForProse(kind.scrutinee)} = ${ctorTex}\\,(`
        : `${ctorTex}\\,(`;

    return (
      <>
        <InlineKaTeX latex={prefix} style={{ fontSize: '12px' }} />
        {paramNames!.map((name, i) => (
          <React.Fragment key={i}>
            {i > 0 && <InlineKaTeX latex=",\," style={{ fontSize: '12px' }} />}
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
          </React.Fragment>
        ))}
        <InlineKaTeX latex=")" style={{ fontSize: '12px' }} />
      </>
    );
  };

  return (
    <div ref={caseContainerRef} onBlur={handleCaseContainerBlur} tabIndex={-1} style={{ outline: 'none' }}>
      <div style={{ ...rowStyle, fontWeight: 600 }} {...rowHandlers}>
        <span style={{ color: kind.isCases ? '#79c0ff' : (kind.isBaseCase ? '#d2a8ff' : '#79c0ff') }}>
          {kind.isCases ? 'Case' : (kind.isBaseCase ? 'Base case' : 'Inductive step')}
        </span>
        <span style={prose}> (</span>
        {renderLabelWithClickableParams()}
        <span style={prose}>):</span>
      </div>
      {/* Inline rename for selected param — same style as tactic suggestions */}
      {selectedParamIndex !== null && paramNames && (
        <InlineBinderRenameRow
          depth={item.depth}
          label={paramNames[selectedParamIndex]}
          renameKey={`${item.nodeId}-${selectedParamIndex}`}
          defaultValue={paramNames[selectedParamIndex]}
          onConfirm={handleRename}
          onCancel={() => setSelectedParamIndex(null)}
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
  typedContext, inductiveMap, registry, kernelType, definitions,
  interactiveGoal, suggestions, selectedPath, onSelectPath,
  editingNames, onEditingNames, editingSuggestionId, onEditingSuggestionId,
  onApplySuggestion, onStartEditingSuggestion,
  rewriteProgress, selectedBinder, onSelectBinder,
  termBuilder, onSetTermBuilder, holeExtraSlot,
}: ProseItemViewProps) {
  const [hovered, setHovered] = useState(false);
  const { kind } = item;

  // Check for error on unfold/rewrite/apply/exact/have items
  const hasError = (kind.tag === 'unfold' || kind.tag === 'rewrite' || kind.tag === 'apply'
    || kind.tag === 'exact' || kind.tag === 'have') && !!kind.error;

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
    const goalLead = buildProseGoalLead(preGoalLatex, isValueType);
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
          || kind.tag === 'simp' || kind.tag === 'have' || kind.tag === 'suffices';

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
          state={state}
          onPushChange={onPushChange}
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
          definitions={definitions}
          typedContext={typedContext}
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
        />
      );

    case 'qed':
      return <QedProseItem rowStyle={rowStyle} rowHandlers={rowHandlers} />;

    case 'hole': {
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
          inductiveMap={inductiveMap}
          registry={registry}
          kernelType={kernelType}
          definitions={definitions}
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
          rewriteProgress={rewriteProgress}
          termBuilder={termBuilder}
          onSetTermBuilder={onSetTermBuilder}
          holeExtraSlot={holeExtraSlot}
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
  inductiveMap?: InductiveMap;
  registry?: SyntaxRegistry;
  kernelType?: TTKTerm;
  definitions?: DefinitionsMap;
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
  rewriteProgress?: RewriteProgress | null;
  /** Active term builder (shown inline before the hole). */
  termBuilder?: TermBuilderState | null;
  onSetTermBuilder?: (b: TermBuilderState | null) => void;
  /** Extra content rendered above the tactic buttons (Lean suggestion pills). */
  holeExtraSlot?: React.ReactNode;
}

function HoleProseView({
  nodeId, depth, goalLatex, state, tacticMode, onTacticMode, onPushChange,
  onClickNode, typedContext, inductiveMap, registry, kernelType, definitions,
  interactiveGoal, suggestions, selectedPath, onSelectPath,
  editingNames, onEditingNames, editingSuggestionId, onEditingSuggestionId,
  onApplySuggestion, onStartEditingSuggestion,
  rewriteProgress,
  termBuilder: inlineTermBuilder, onSetTermBuilder, holeExtraSlot,
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
      inductiveMap,
      registry,
      kernelType,
      definitions,
      computeApplySubgoalCount: (root, cursorNodeId, rootKernelType, defs, name) =>
        computeApplySubgoalCount(root, cursorNodeId, rootKernelType, defs, name),
    });
    if (result) onPushChange(result);
    onTacticMode(null);
  }, [tacticMode, state, onPushChange, onTacticMode, typedContext, inductiveMap, registry, kernelType, definitions]);

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
      {/* Inline term builder (appears above the goal when active) */}
      {inlineTermBuilder && onSetTermBuilder && (
        <ProofTreeTermBuilderPanel
          builderState={inlineTermBuilder}
          registry={registry}
          onFillSlot={(slotIndex, sourceExpr) => {
            const rebuilt = fillTermBuilderSlotFromGoal(
              inlineTermBuilder,
              slotIndex,
              convertMathEditorSourceToUnicode(sourceExpr),
              typedContext?.kernelGoal,
              definitions,
            );
            if (rebuilt) onSetTermBuilder(rebuilt.builderState);
          }}
          onClearSlot={(slotIndex) => {
            const rebuilt = clearTermBuilderSlotFromGoal(
              inlineTermBuilder,
              slotIndex,
              typedContext?.kernelGoal,
              definitions,
            );
            if (rebuilt) onSetTermBuilder(rebuilt.builderState);
          }}
          onConfirm={() => {
            const result = insertHaveFromTermBuilder(state, inlineTermBuilder);
            if (result) onPushChange(result);
            onSetTermBuilder(null);
          }}
          onCancel={() => onSetTermBuilder(null)}
        />
      )}

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
          rewriteProgress={rewriteProgress}
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
            { tactic: 'exact' as const, label: 'Exact' },
            { tactic: 'unfold' as const, label: 'Unfold' },
            { tactic: 'fold' as const, label: 'Fold' },
            { tactic: 'rewrite' as const, label: 'Rewrite' },
            { tactic: 'rewrite_rev' as const, label: 'Rewrite\u2190' },
            { tactic: 'apply' as const, label: 'Apply' },
            { tactic: 'simp' as const, label: 'Simp' },
            { tactic: 'have' as const, label: 'Have' },
          ].map(({ tactic, label }) => (
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
