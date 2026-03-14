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
  applyIntros, applyInduction, applyInductionWithCtors, applyExact, applyUnfold, applyFold, applyRewrite, applyApplyTactic, applySimp,
  addCase, removeCase, toggleCollapse, toggleInductionCollapse, toggleSimpCollapse,
  moveCursorUp, moveCursorDown,
  clearNode,
  pushState, updateCurrent, undo, redo,
} from '../proof-tree/proof-tree';
import { runSimp } from '../tactics/simp-tactic';
import {
  TypedProofContext, ValidationResult, computeTypedContext, computeApplySubgoalCount,
  NodeGoalInfo, replayEntireTree, replayToEngine,
  InductiveMap, extractTypeHead, generateCaseInfos,
} from '../proof-tree/goal-computation';
import { buildReverseRegistry, ReverseRegistry } from '../math-editor/tt-to-math';
import { ProseItem, generateProofProse } from '../proof-tree/proof-prose';
import { renderInteractiveGoal, InteractiveGoal, GoalPath } from '../proof-tree/interactive-goal';
import { computeTacticSuggestions, computeRewriteSuggestionsIncremental, TacticSuggestion, RewriteSuggestion, RewriteProgress } from '../proof-tree/tactic-suggestions';
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

type TacticMode =
  | null
  | { tactic: 'intros' }
  | { tactic: 'induction' }
  | { tactic: 'exact' }
  | { tactic: 'unfold' }
  | { tactic: 'fold' }
  | { tactic: 'rewrite' }
  | { tactic: 'rewrite_rev' }
  | { tactic: 'apply' }
  | { tactic: 'simp' };

// ============================================================================
// Main Component
// ============================================================================

export function ProofTreeEditor({ history, onHistoryChange, surfaceType, kernelType, definitions, registry, inductiveMap }: ProofTreeEditorProps) {
  const containerRef = useRef<HTMLDivElement>(null);
  const state = history.current;

  // Ephemeral tactic input mode (not part of immutable state)
  const [tacticMode, setTacticMode] = useState<TacticMode>(null);
  const [activeTab, setActiveTab] = useState<'tactics' | 'proof'>('proof');

  // Goal interaction state (shared between GoalPanel and prose view)
  const [goalSelectedPath, setGoalSelectedPath] = useState<GoalPath | null>(null);
  const [goalEditingNames, setGoalEditingNames] = useState<string[] | null>(null);
  const [goalEditingSuggestionId, setGoalEditingSuggestionId] = useState<string | null>(null);

  const emptyRegistry = useMemo<SyntaxRegistry>(() => ({ symbolMap: new Map(), entries: [] }), []);

  // Compute typed context at cursor position (uses surface type when available)
  const typedContext = useMemo<TypedProofContext | null>(() => {
    if (surfaceType) {
      return computeTypedContext(
        state.root, state.cursor.nodeId, surfaceType, registry ?? emptyRegistry,
        inductiveMap, kernelType, definitions,
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
  }, [state.root, state.cursor.nodeId, surfaceType, kernelType, definitions, registry, emptyRegistry, inductiveMap]);

  // Compute interactive goal from kernel info (shared between GoalPanel and prose view)
  const interactiveGoal = useMemo<InteractiveGoal | null>(() => {
    if (!typedContext?.kernelGoal) return null;
    if (typedContext.validation?.status === 'solved') return null;
    const { engine, goal, definitions: defs, rev: r } = typedContext.kernelGoal;
    try {
      return renderInteractiveGoal(engine, goal, defs, r);
    } catch {
      return null;
    }
  }, [typedContext?.kernelGoal, typedContext?.validation]);

  // Compute tactic suggestions from selection (synchronous: intro, unfold, induction)
  const syncSuggestions = useMemo<readonly TacticSuggestion[]>(() => {
    if (!interactiveGoal || !goalSelectedPath) return [];
    return computeTacticSuggestions(goalSelectedPath, interactiveGoal, definitions, typedContext?.kernelGoal ?? undefined);
  }, [goalSelectedPath, interactiveGoal, definitions, typedContext?.kernelGoal]);

  // Incremental rewrite suggestions (scan hypotheses, try targeted rewrites)
  const [rewriteProgress, setRewriteProgress] = useState<RewriteProgress | null>(null);
  const rewriteSuggestions = rewriteProgress?.suggestions ?? [];
  useEffect(() => {
    setRewriteProgress(null);
    if (!goalSelectedPath || !interactiveGoal || !typedContext?.kernelGoal) return;
    const cancel = computeRewriteSuggestionsIncremental(
      goalSelectedPath, interactiveGoal, typedContext.kernelGoal,
      (progress) => setRewriteProgress(progress),
    );
    return cancel;
  }, [goalSelectedPath, interactiveGoal, typedContext?.kernelGoal]);

  // Merge all suggestions
  const goalSuggestions = useMemo<readonly TacticSuggestion[]>(() => {
    if (syncSuggestions.length === 0 && rewriteSuggestions.length === 0) return [];
    return [...syncSuggestions, ...rewriteSuggestions];
  }, [syncSuggestions, rewriteSuggestions]);

  // Reset goal selection when cursor changes
  useEffect(() => {
    setGoalSelectedPath(null);
    setGoalEditingNames(null);
    setGoalEditingSuggestionId(null);
  }, [state.cursor.nodeId]);

  // Compute goal map for prose view (replays entire tree, not just to cursor)
  const rev = useMemo<ReverseRegistry | null>(() => {
    if (!registry) return null;
    return buildReverseRegistry(registry);
  }, [registry]);

  const goalMap = useMemo<Map<ProofNodeId, NodeGoalInfo>>(() => {
    if (!kernelType || !definitions || !rev) return new Map();
    try {
      return replayEntireTree(state.root, kernelType, definitions, rev);
    } catch {
      return new Map();
    }
  }, [state.root, kernelType, definitions, rev]);

  // Generate prose items from proof tree + goal map
  const proseItems = useMemo<ProseItem[]>(() => {
    return generateProofProse(state.root, state.cursor.nodeId, goalMap);
  }, [state.root, state.cursor.nodeId, goalMap]);

  // Dispatch a structural change (goes on undo stack)
  const pushChange = useCallback((newState: ProofTreeState) => {
    onHistoryChange(pushState(history, newState));
    setTacticMode(null);
  }, [history, onHistoryChange]);

  // Dispatch a cursor-only move (does NOT go on undo stack)
  const moveCursor = useCallback((newState: ProofTreeState) => {
    onHistoryChange(updateCurrent(history, newState));
  }, [history, onHistoryChange]);

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
        const cleared = clearNode(state, state.cursor.nodeId);
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
                onSelectPath={setGoalSelectedPath}
                editingNames={goalEditingNames}
                onEditingNames={setGoalEditingNames}
                editingSuggestionId={goalEditingSuggestionId}
                onEditingSuggestionId={setGoalEditingSuggestionId}
                rewriteProgress={rewriteProgress}
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
          onSelectPath={setGoalSelectedPath}
          editingNames={goalEditingNames}
          onEditingNames={setGoalEditingNames}
          editingSuggestionId={goalEditingSuggestionId}
          onEditingSuggestionId={setGoalEditingSuggestionId}
          inductiveMap={inductiveMap}
          registry={registry}
          rewriteProgress={rewriteProgress}
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
  onEditingNames: (n: string[] | null) => void;
  editingSuggestionId: string | null;
  onEditingSuggestionId: (id: string | null) => void;
  state: ProofTreeState;
  onPushChange: (s: ProofTreeState) => void;
  /** Fallback LaTeX when interactive goal is unavailable. */
  fallbackGoalLatex?: string;
  validation?: ValidationResult;
  inductiveMap?: InductiveMap;
  registry?: SyntaxRegistry;
  typedContext?: TypedProofContext | null;
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
  state, onPushChange,
  fallbackGoalLatex, validation,
  inductiveMap, registry, typedContext,
  rewriteProgress, goalFontSize,
}: GoalInteractionProps) {
  const handleApplySuggestion = (suggestion: TacticSuggestion) => {
    let result: ProofTreeState | null = null;

    if (suggestion.id === 'exact-refl') {
      result = applyExact(state, 'refl');
    } else if (suggestion.id.startsWith('unfold-')) {
      const name = suggestion.id.slice('unfold-'.length);
      result = applyUnfold(state, name, suggestion.unfoldOccurrence);
    } else if (suggestion.id.startsWith('induction-')) {
      const scrutinee = suggestion.id.slice('induction-'.length);
      // Look up the inductive type info for the variable's type
      const typeHead = interactiveGoal?.contextVarTypes.get(scrutinee);
      const indInfo = typeHead && inductiveMap ? inductiveMap.get(typeHead) : undefined;
      if (indInfo) {
        const rev = registry ? buildReverseRegistry(registry) : undefined;
        const ctxNames = typedContext?.hypotheses.map(h => h.name);
        const ctorInfos = generateCaseInfos(scrutinee, indInfo, rev, ctxNames);
        result = applyInductionWithCtors(state, scrutinee, ctorInfos);
      }
    } else if (suggestion.id.startsWith('fold-')) {
      const name = suggestion.foldName ?? suggestion.id.slice('fold-'.length);
      result = applyFold(state, name, suggestion.foldOccurrence);
    } else if (suggestion.id.startsWith('rewrite-')) {
      const rw = suggestion as RewriteSuggestion;
      result = applyRewrite(state, rw.rewriteName, rw.reverse, rw.occurrences, rw.targetHead);
    } else {
      const names = editingSuggestionId === suggestion.id && editingNames
        ? editingNames
        : [...(suggestion.proposedNames ?? [])];
      result = applyIntros(state, names);
    }

    if (result) {
      onPushChange(result);
      onSelectPath(null);
      onEditingNames(null);
      onEditingSuggestionId(null);
    }
  };

  const handleStartEditing = (suggestion: TacticSuggestion) => {
    if (editingSuggestionId === suggestion.id) {
      onEditingSuggestionId(null);
      onEditingNames(null);
    } else {
      onEditingSuggestionId(suggestion.id);
      onEditingNames([...(suggestion.proposedNames ?? [])]);
    }
  };

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
                return (
                  <button
                    key={s.id}
                    style={suggestionBtnStyle}
                    onClick={() => handleApplySuggestion(s)}
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
                  onClick={() => handleStartEditing(s)}
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
                      onEditingNames(updated);
                      if (!isEditing) onEditingSuggestionId(s.id);
                    }}
                    onKeyDown={e => {
                      if (e.key === 'Enter') {
                        e.preventDefault();
                        handleApplySuggestion(s);
                      }
                    }}
                    style={nameInputStyle}
                  />
                ))}
                <button
                  style={applyBtnStyle}
                  onClick={() => handleApplySuggestion(s)}
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
  inductiveMap, registry, rewriteProgress,
}: {
  context: TypedProofContext | null;
  state?: ProofTreeState;
  onPushChange?: (s: ProofTreeState) => void;
  interactiveGoal: InteractiveGoal | null;
  suggestions: readonly TacticSuggestion[];
  selectedPath: GoalPath | null;
  onSelectPath: (p: GoalPath | null) => void;
  editingNames: string[] | null;
  onEditingNames: (n: string[] | null) => void;
  editingSuggestionId: string | null;
  onEditingSuggestionId: (id: string | null) => void;
  inductiveMap?: InductiveMap;
  registry?: SyntaxRegistry;
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
            <div key={i} style={{
              padding: '1px 0',
              display: 'flex',
              alignItems: 'baseline',
              gap: '4px',
              flexWrap: 'wrap',
            }}>
              <InlineKaTeX latex={textToLatex(h.name)} style={{ fontSize: '12px' }} />
              {h.type && (
                <>
                  <span style={{ color: '#484f58', fontSize: '11px' }}>:</span>
                  <InlineKaTeX latex={h.type} style={{ fontSize: '11px' }} />
                </>
              )}
            </div>
          ))}
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
            state={state}
            onPushChange={onPushChange}
            fallbackGoalLatex={goal}
            validation={validation}
            inductiveMap={inductiveMap}
            registry={registry}
            typedContext={context}
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
    if (!tacticMode) return;
    let result: ProofTreeState | null = null;
    switch (tacticMode.tactic) {
      case 'intros': {
        const names = value.split(/[\s,]+/).filter(Boolean);
        if (names.length > 0) result = applyIntros(state, names);
        break;
      }
      case 'induction': {
        const scrutinee = value.trim();
        if (scrutinee) {
          // Try to auto-generate cases from inductive type info
          const hyp = typedContext?.hypotheses.find(h => h.name === scrutinee);
          const rawType = hyp?.rawType;
          const headName = rawType ? extractTypeHead(rawType) : null;
          const indInfo = headName && inductiveMap ? inductiveMap.get(headName) : undefined;

          if (indInfo) {
            const rev = registry ? buildReverseRegistry(registry) : undefined;
            const ctxNames = typedContext?.hypotheses.map(h => h.name);
            const ctorInfos = generateCaseInfos(scrutinee, indInfo, rev, ctxNames);
            result = applyInductionWithCtors(state, scrutinee, ctorInfos);
          } else {
            // Fallback: hardcoded case labels
            result = applyInduction(state, scrutinee, [`${scrutinee} = 0`, `${scrutinee} = k'`]);
          }
        }
        break;
      }
      case 'exact': {
        const expr = value.trim();
        if (expr) result = applyExact(state, expr);
        break;
      }
      case 'unfold': {
        const name = value.trim();
        if (name) result = applyUnfold(state, name);
        break;
      }
      case 'fold': {
        const name = value.trim();
        if (name) result = applyFold(state, name);
        break;
      }
      case 'rewrite': {
        const name = value.trim();
        if (name) result = applyRewrite(state, name);
        break;
      }
      case 'rewrite_rev': {
        const name = value.trim();
        if (name) result = applyRewrite(state, name, true);
        break;
      }
      case 'apply': {
        const name = value.trim();
        if (name) {
          let numChildren = 1;
          if (kernelType && definitions) {
            numChildren = computeApplySubgoalCount(
              state.root, state.cursor.nodeId, kernelType, definitions, name,
            );
          }
          result = applyApplyTactic(state, name, numChildren);
        }
        break;
      }
      case 'simp': {
        const lemmaStr = value.trim();
        if (lemmaStr && kernelType && definitions) {
          const lemmas = lemmaStr.split(/[\s,]+/).filter(Boolean);
          const engine = replayToEngine(state.root, state.cursor.nodeId, kernelType, definitions);
          if (engine) {
            const simpResult = runSimp(engine, lemmas);
            if (simpResult.success) {
              result = applySimp(state, lemmas, simpResult.proofNodes);
            }
          }
        }
        break;
      }
    }
    if (result) onPushChange(result);
    onTacticMode(null);
  }, [tacticMode, state, onPushChange, onTacticMode, kernelType, definitions]);

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
              activeTactic === 'simp' ? 'lemma1, lemma2, ...' :
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
    const parts = names.map(n => textToLatex(n));
    if (parts.length === 0) return '';
    if (parts.length === 1) return parts[0];
    if (parts.length === 2) return `${parts[0]} \\text{ and } ${parts[1]}`;
    return parts.slice(0, -1).join(',\\, ') + ',\\, \\text{and } ' + parts[parts.length - 1];
  };

  const handleDelete = useCallback(() => {
    const result = clearNode(state, node.id);
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
    const result = toggleInductionCollapse(state, node.id);
    if (result) onPushChange(result);
  }, [state, node.id, onPushChange]);

  const handleAddCase = useCallback((e: React.MouseEvent) => {
    e.stopPropagation();
    const result = addCase(state, node.id, 'new case');
    if (result) onPushChange(result);
  }, [state, node.id, onPushChange]);

  const handleDelete = useCallback(() => {
    const result = clearNode(state, node.id);
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
        <span style={keywordStyle}>induct on </span>
        <InlineKaTeX
          latex={textToLatex(node.scrutinee)}
          style={{ fontSize: '13px' }}
        />
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
    onPushChange(toggleCollapse(state, caseNode.id));
  }, [state, caseNode.id, onPushChange]);

  const handleDelete = useCallback((e: React.MouseEvent) => {
    e.stopPropagation();
    const result = removeCase(state, inductionId, caseIndex);
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
    const result = clearNode(state, node.id);
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
    const result = clearNode(state, node.id);
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
    const result = clearNode(state, node.id);
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
    const result = clearNode(state, node.id);
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
    const result = clearNode(state, node.id);
    if (result) onPushChange(result);
  }, [state, node.id, onPushChange]);

  const handleToggle = useCallback(() => {
    const result = toggleSimpCollapse(state, node.id);
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
    const result = clearNode(state, node.id);
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
  onEditingNames: (n: string[] | null) => void;
  editingSuggestionId: string | null;
  onEditingSuggestionId: (id: string | null) => void;
  rewriteProgress?: RewriteProgress | null;
}

function ProofProseView({
  items, state, tacticMode, onTacticMode, onPushChange, onClickNode,
  typedContext, inductiveMap, registry, kernelType, definitions,
  interactiveGoal, suggestions, selectedPath, onSelectPath,
  editingNames, onEditingNames, editingSuggestionId, onEditingSuggestionId,
  rewriteProgress,
}: ProseViewProps) {
  if (items.length === 0) {
    return <div style={{ padding: '8px 12px', color: '#484f58', fontStyle: 'italic' }}>No proof steps yet.</div>;
  }

  // Find the last goal-showing step before the active cursor hole.
  // This step will render its goal interactively instead of as plain LaTeX.
  const lastGoalStepIdx = (() => {
    // Find cursor hole
    const holeIdx = items.findIndex(it => it.isCursor && it.kind.tag === 'hole');
    if (holeIdx < 0) return -1;
    // Walk backwards to find the last goal-showing step
    for (let i = holeIdx - 1; i >= 0; i--) {
      const k = items[i].kind;
      if (k.tag === 'unfold' || k.tag === 'rewrite' || k.tag === 'simp') return i;
      if (k.tag === 'intro' && k.goalLatex) return i;
      if (k.tag === 'apply') return i;
      // Stop at structural boundaries
      if (k.tag === 'caseHeader' || k.tag === 'inductionHeader') break;
      if (k.tag === 'hole' || k.tag === 'qed' || k.tag === 'exact') break;
    }
    return -1;
  })();

  return (
    <div>
      {items.map((item, idx) => {
        // Deletable items: anything except hole, qed, caseHeader
        const isDeletable = item.kind.tag === 'intro' || item.kind.tag === 'unfold'
          || item.kind.tag === 'rewrite' || item.kind.tag === 'apply'
          || item.kind.tag === 'exact' || item.kind.tag === 'inductionHeader';
        const handleDelete = isDeletable ? () => {
          const result = clearNode(state, item.nodeId);
          if (result) onPushChange(result);
        } : undefined;

        return (
          <ProseItemView
            key={`${item.nodeId}-${idx}`}
            item={item}
            prevItem={idx > 0 ? items[idx - 1] : undefined}
            isLastGoalStep={idx === lastGoalStepIdx}

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
            rewriteProgress={rewriteProgress}
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
  /** True if this is the last goal-showing step before the active hole. */
  isLastGoalStep?: boolean;

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
  onEditingNames: (n: string[] | null) => void;
  editingSuggestionId: string | null;
  onEditingSuggestionId: (id: string | null) => void;
  rewriteProgress?: RewriteProgress | null;
}

const proseStyle: React.CSSProperties = {
  fontSize: '13px',
  lineHeight: '1.7',
  cursor: 'pointer',
  fontFamily: '"STIX Two Text", "Times New Roman", Georgia, serif',
  textAlign: 'left',
};

/** Style for a centered display-mode equation block */
const eqBlockStyle: React.CSSProperties = {
  display: 'block',
  padding: '2px 0',
  overflowX: 'auto',
};

function ProseItemView({
  item, prevItem, isLastGoalStep, onClick, onDelete, state, tacticMode, onTacticMode, onPushChange, onClickNode,
  typedContext, inductiveMap, registry, kernelType, definitions,
  interactiveGoal, suggestions, selectedPath, onSelectPath,
  editingNames, onEditingNames, editingSuggestionId, onEditingSuggestionId,
  rewriteProgress,
}: ProseItemViewProps) {
  const [hovered, setHovered] = useState(false);
  const { kind } = item;

  // Check for error on unfold/rewrite/apply items
  const hasError = (kind.tag === 'unfold' || kind.tag === 'rewrite' || kind.tag === 'apply') && !!kind.error;

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
  const prevShowedGoal = prevItem && (
    (prevItem.kind.tag === 'unfold' && prevItem.kind.goalLatex) ||
    (prevItem.kind.tag === 'rewrite' && prevItem.kind.goalLatex) ||
    (prevItem.kind.tag === 'apply' && (prevItem.kind.subgoalLatex?.length ?? 0) <= 1 && prevItem.kind.subgoalLatex?.[0]) ||
    (prevItem.kind.tag === 'simp' && prevItem.kind.goalLatex) ||
    (prevItem.kind.tag === 'intro' && prevItem.kind.goalLatex)
  );

  // "We must show [goal]" prefix for steps where no prior goal is visible
  function mustShowPrefix(preGoalLatex?: string): React.ReactNode {
    if (prevShowedGoal || !preGoalLatex) return null;
    return (
      <>
        <span style={prose}>We must show</span>
        <span style={eqBlockStyle}>
          <InlineKaTeX latex={preGoalLatex} displayMode />
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
          || kind.tag === 'simp';

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
    return (
      <>
        <span style={prose}>{prefix}</span>
        <span style={eqBlockStyle}>
          <InlineKaTeX latex={goalLatex} displayMode />
        </span>
      </>
    );
  }

  switch (kind.tag) {
    case 'intro':
      return (
        <div style={rowStyle} {...rowHandlers}>
          <span style={prose}>Let{' '}</span>
          <InlineKaTeX latex={kind.latex} style={{ fontSize: '13px' }} />
          {kind.goalLatex ? renderGoalSection(kind.goalLatex, '. We must show') : <span style={prose}>.</span>}
          {deleteBtn}
        </div>
      );

    case 'unfold':
      return (
        <div style={rowStyle} {...rowHandlers}>
          {mustShowPrefix(kind.preGoalLatex)}
          <span style={prose}>which is true, by definition of{' '}</span>
          <InlineKaTeX latex={texNameForProse(kind.name)} style={{ fontSize: '13px' }} />
          {errorSuffix}
          {renderGoalSection(kind.goalLatex, ', if')}
          {deleteBtn}
        </div>
      );

    case 'fold':
      return (
        <div style={rowStyle} {...rowHandlers}>
          {mustShowPrefix(kind.preGoalLatex)}
          <span style={prose}>which matches the definition of{' '}</span>
          <InlineKaTeX latex={texNameForProse(kind.name)} style={{ fontSize: '13px' }} />
          {errorSuffix}
          {renderGoalSection(kind.goalLatex, ', if')}
          {deleteBtn}
        </div>
      );

    case 'rewrite': {
      const arrow = kind.reverse ? ' (\u2190)' : '';
      return (
        <div style={rowStyle} {...rowHandlers}>
          {mustShowPrefix(kind.preGoalLatex)}
          <span style={prose}>which is true, because{' '}</span>
          {kind.equationLatex ? (
            <>
              <InlineKaTeX latex={kind.equationLatex} style={{ fontSize: '12px' }} />
              <span style={prose}>{arrow} (</span>
              <InlineKaTeX latex={texNameForProse(kind.name)} style={{ fontSize: '13px' }} />
              <span style={prose}>)</span>
            </>
          ) : (
            <>
              <span style={prose}>of{' '}</span>
              <InlineKaTeX latex={texNameForProse(kind.name)} style={{ fontSize: '13px' }} />
              {arrow && <span style={prose}>{arrow}</span>}
            </>
          )}
          {errorSuffix}
          {renderGoalSection(kind.goalLatex, ', if')}
          {deleteBtn}
        </div>
      );
    }

    case 'apply': {
      const subgoals = kind.subgoalLatex ?? [];
      const appliedArgs = kind.appliedArgsLatex ?? [];
      if (subgoals.length <= 1) {
        return (
          <div style={rowStyle} {...rowHandlers}>
            {mustShowPrefix(kind.preGoalLatex)}
            <span style={prose}>which is true, by{' '}</span>
            <InlineKaTeX latex={texNameForProse(kind.name)} style={{ fontSize: '13px' }} />
            {appliedArgs.length > 0 && (
              <>
                <span style={prose}>{' '}applied to{' '}</span>
                {appliedArgs.map((arg, i) => (
                  <React.Fragment key={i}>
                    {i > 0 && <span style={prose}>,{' '}</span>}
                    <InlineKaTeX latex={arg} style={{ fontSize: '13px' }} />
                  </React.Fragment>
                ))}
              </>
            )}
            {errorSuffix}
            {renderGoalSection(subgoals[0], ', if')}
            {deleteBtn}
          </div>
        );
      }
      // Multiple subgoals
      return (
        <div style={rowStyle} {...rowHandlers}>
          {mustShowPrefix(kind.preGoalLatex)}
          <span style={prose}>which is true, by{' '}</span>
          <InlineKaTeX latex={texNameForProse(kind.name)} style={{ fontSize: '13px' }} />
          {appliedArgs.length > 0 && (
            <>
              <span style={prose}>{' '}applied to{' '}</span>
              {appliedArgs.map((arg, i) => (
                <React.Fragment key={i}>
                  {i > 0 && <span style={prose}>,{' '}</span>}
                  <InlineKaTeX latex={arg} style={{ fontSize: '13px' }} />
                </React.Fragment>
              ))}
            </>
          )}
          {errorSuffix}
          <span style={prose}>, if:</span>
          {subgoals.map((sg, i) => (
            <div key={i} style={{ paddingTop: '2px', textAlign: 'center' }}>
              <span style={prose}>({i + 1}){' '}</span>
              <InlineKaTeX latex={sg} displayMode />
            </div>
          ))}
          {deleteBtn}
        </div>
      );
    }

    case 'inductionHeader':
      return (
        <div style={rowStyle} {...rowHandlers}>
          <span style={prose}>We proceed by induction on{' '}</span>
          <InlineKaTeX latex={texNameForProse(kind.scrutinee)} style={{ fontSize: '13px' }} />
          <span style={prose}>.</span>
          {deleteBtn}
        </div>
      );

    case 'caseHeader':
      return (
        <div style={{ ...rowStyle, fontWeight: 600 }} {...rowHandlers}>
          <span style={{ color: kind.isBaseCase ? '#d2a8ff' : '#79c0ff' }}>
            {kind.isBaseCase ? 'Base case' : 'Inductive step'}
          </span>
          <span style={prose}> (</span>
          <InlineKaTeX latex={kind.labelLatex} style={{ fontSize: '12px' }} />
          <span style={prose}>):</span>
        </div>
      );

    case 'exact':
      return (
        <div style={rowStyle} {...rowHandlers}>
          {mustShowPrefix(kind.goalLatex)}
          {kind.solved ? (
            <>
              <span style={prose}>The result follows from{' '}</span>
              <InlineKaTeX latex={texNameForProse(kind.exprLatex)} style={{ fontSize: '13px' }} />
              <span style={prose}>.</span>
            </>
          ) : kind.error ? (
            <>
              <span style={{ color: '#f85149' }}>By{' '}</span>
              <InlineKaTeX latex={texNameForProse(kind.exprLatex)} style={{ fontSize: '13px' }} />
              <span style={{ color: '#f85149', fontSize: '11px', marginLeft: '6px' }}>({kind.error})</span>
            </>
          ) : (
            <>
              <span style={prose}>By{' '}</span>
              <InlineKaTeX latex={texNameForProse(kind.exprLatex)} style={{ fontSize: '13px' }} />
              <span style={prose}>.</span>
            </>
          )}
          {deleteBtn}
        </div>
      );

    case 'simp':
      return (
        <div style={rowStyle} {...rowHandlers}>
          {mustShowPrefix(kind.preGoalLatex)}
          <span style={prose}>Simplifying using{' '}</span>
          {kind.lemmas.map((lemma, i) => (
            <React.Fragment key={i}>
              {i > 0 && <span style={prose}>,{' '}</span>}
              <InlineKaTeX latex={texNameForProse(lemma)} style={{ fontSize: '13px' }} />
            </React.Fragment>
          ))}
          <span style={prose}>{' '}({kind.stepCount} step{kind.stepCount !== 1 ? 's' : ''})</span>
          {renderGoalSection(kind.goalLatex, ', we get')}
          {deleteBtn}
        </div>
      );

    case 'qed':
      return (
        <div style={{ ...rowStyle, paddingTop: '2px' }} {...rowHandlers}>
          <span style={{ color: '#3fb950', fontSize: '14px' }}>&#8718;</span>
        </div>
      );

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
          rewriteProgress={rewriteProgress}
        />
      );
    }

    default:
      return null;
  }
}

/** Render a variable name for prose inline KaTeX.
 *  Single chars stay as math italic (e.g., n, f).
 *  Multi-char names use \textsf for clean sans-serif rendering (e.g., sum, minusSucc). */
function texNameForProse(name: string): string {
  if (name.length === 1) return name;
  if (name.length === 2 && name[1] === "'") return `${name[0]}'`;
  return `\\textsf{${name}}`;
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
  onEditingNames: (n: string[] | null) => void;
  editingSuggestionId: string | null;
  onEditingSuggestionId: (id: string | null) => void;
  rewriteProgress?: RewriteProgress | null;
}

function HoleProseView({
  nodeId, depth, goalLatex, state, tacticMode, onTacticMode, onPushChange,
  onClickNode, typedContext, inductiveMap, registry, kernelType, definitions,
  interactiveGoal, suggestions, selectedPath, onSelectPath,
  editingNames, onEditingNames, editingSuggestionId, onEditingSuggestionId,
  rewriteProgress,
}: HoleProseViewProps) {
  const inputRef = useRef<HTMLInputElement>(null);
  const activeTactic = tacticMode?.tactic ?? null;

  useEffect(() => {
    if (activeTactic && inputRef.current) {
      inputRef.current.focus();
    }
  }, [activeTactic]);

  const handleSubmit = useCallback((value: string) => {
    if (!tacticMode) return;
    let result: ProofTreeState | null = null;
    switch (tacticMode.tactic) {
      case 'intros': {
        const names = value.split(/[\s,]+/).filter(Boolean);
        if (names.length > 0) result = applyIntros(state, names);
        break;
      }
      case 'induction': {
        const scrutinee = value.trim();
        if (scrutinee) {
          const hyp = typedContext?.hypotheses.find(h => h.name === scrutinee);
          const rawType = hyp?.rawType;
          const headName = rawType ? extractTypeHead(rawType) : null;
          const indInfo = headName && inductiveMap ? inductiveMap.get(headName) : undefined;
          if (indInfo) {
            const rev = registry ? buildReverseRegistry(registry) : undefined;
            const ctxNames = typedContext?.hypotheses.map(h => h.name);
            const ctorInfos = generateCaseInfos(scrutinee, indInfo, rev, ctxNames);
            result = applyInductionWithCtors(state, scrutinee, ctorInfos);
          } else {
            result = applyInduction(state, scrutinee, [`${scrutinee} = 0`, `${scrutinee} = k'`]);
          }
        }
        break;
      }
      case 'exact': {
        const expr = value.trim();
        if (expr) result = applyExact(state, expr);
        break;
      }
      case 'unfold': {
        const name = value.trim();
        if (name) result = applyUnfold(state, name);
        break;
      }
      case 'fold': {
        const name = value.trim();
        if (name) result = applyFold(state, name);
        break;
      }
      case 'rewrite': {
        const name = value.trim();
        if (name) result = applyRewrite(state, name);
        break;
      }
      case 'rewrite_rev': {
        const name = value.trim();
        if (name) result = applyRewrite(state, name, true);
        break;
      }
      case 'apply': {
        const name = value.trim();
        if (name) {
          let numChildren = 1;
          if (kernelType && definitions) {
            numChildren = computeApplySubgoalCount(
              state.root, state.cursor.nodeId, kernelType, definitions, name,
            );
          }
          result = applyApplyTactic(state, name, numChildren);
        }
        break;
      }
      case 'simp': {
        const lemmaStr = value.trim();
        if (lemmaStr && kernelType && definitions) {
          const lemmas = lemmaStr.split(/[\s,]+/).filter(Boolean);
          const engine = replayToEngine(state.root, state.cursor.nodeId, kernelType, definitions);
          if (engine) {
            const simpResult = runSimp(engine, lemmas);
            if (simpResult.success) {
              result = applySimp(state, lemmas, simpResult.proofNodes);
            }
          }
        }
        break;
      }
    }
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
          state={state}
          onPushChange={onPushChange}
          fallbackGoalLatex={goalLatex}
          inductiveMap={inductiveMap}
          registry={registry}
          typedContext={typedContext}
          rewriteProgress={rewriteProgress}
          goalFontSize="16px"
        />
      </div>

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
              activeTactic === 'simp' ? 'lemma1, lemma2, ...' :
              'proof expression'
            }
            onKeyDown={handleKeyDown}
            onClick={(e) => e.stopPropagation()}
          />
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
