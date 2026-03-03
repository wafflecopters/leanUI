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
  ProofTreeHistory, ProofTreeState, ProofNode, CaseNode, ProofNodeId,
  computeContext,
  applyIntros, applyInduction, applyInductionWithCtors, applyExact, applyUnfold, applyRewrite, applyApplyTactic,
  addCase, removeCase, toggleCollapse, toggleInductionCollapse,
  moveCursorUp, moveCursorDown,
  clearNode,
  pushState, updateCurrent, undo, redo,
} from '../proof-tree/proof-tree';
import {
  TypedProofContext, computeTypedContext,
  InductiveMap, extractTypeHead, generateCaseInfos,
} from '../proof-tree/goal-computation';
import { buildReverseRegistry } from '../math-editor/tt-to-math';
import SplitPane from './SplitPane';

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
  minHeight: '40px',
};

const INITIAL_PANE_SIZES = [
  { size: 65, mode: 'percent' as const },
  { size: 35, mode: 'percent' as const },
];

// ============================================================================
// InlineKaTeX — renders a LaTeX string inline
// ============================================================================

function InlineKaTeX({ latex, style }: { latex: string; style?: React.CSSProperties }) {
  const ref = useRef<HTMLSpanElement>(null);

  useEffect(() => {
    if (!ref.current) return;
    try {
      katex.render(latex, ref.current, {
        displayMode: false,
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
  | { tactic: 'rewrite' }
  | { tactic: 'apply' };

// ============================================================================
// Main Component
// ============================================================================

export function ProofTreeEditor({ history, onHistoryChange, surfaceType, kernelType, definitions, registry, inductiveMap }: ProofTreeEditorProps) {
  const containerRef = useRef<HTMLDivElement>(null);
  const state = history.current;

  // Ephemeral tactic input mode (not part of immutable state)
  const [tacticMode, setTacticMode] = useState<TacticMode>(null);

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
        {/* Left: proof tree */}
        <div style={{ padding: '8px 0', minWidth: 0, overflowY: 'auto', height: '100%' }}>
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
          />
        </div>

        {/* Right: goal panel */}
        <GoalPanel context={typedContext} />
      </SplitPane>
    </div>
  );
}

// ============================================================================
// GoalPanel — shows context + goal at cursor position
// ============================================================================

function GoalPanel({ context }: { context: TypedProofContext | null }) {
  if (!context) return null;

  const { hypotheses, caseLabel, caseLabelLatex, inductionVar, goal } = context;

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
          <div style={{
            fontSize: '10px',
            color: '#484f58',
            letterSpacing: '0.04em',
            marginBottom: '4px',
            fontWeight: 600,
          }}>
            CONTEXT
          </div>
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
          <div style={{
            fontSize: '10px',
            color: '#484f58',
            letterSpacing: '0.04em',
            marginBottom: '4px',
            fontWeight: 600,
          }}>
            CASE
          </div>
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
        <div style={{
          fontSize: '10px',
          color: '#484f58',
          letterSpacing: '0.04em',
          marginBottom: '4px',
          fontWeight: 600,
        }}>
          GOAL
        </div>
        <div style={{
          padding: '4px 8px',
          backgroundColor: '#0d1117',
          borderRadius: '4px',
          border: '1px solid #21262d',
          wordBreak: 'break-word' as const,
        }}>
          {goal === '?' ? (
            <span style={{ color: '#d29922', fontStyle: 'italic' }}>unsolved</span>
          ) : goal ? (
            <InlineKaTeX latex={goal} style={{ fontSize: '11px' }} />
          ) : (
            <span style={{ color: '#484f58' }}>&mdash;</span>
          )}
        </div>
      </div>
    </div>
  );
}

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
}

function ProofNodeView(props: NodeViewProps) {
  switch (props.node.tag) {
    case 'hole': return <HoleView {...props} />;
    case 'intros': return <IntrosView {...props} />;
    case 'induction': return <InductionView {...props} />;
    case 'exact': return <ExactView {...props} />;
    case 'unfold': return <UnfoldView {...props} />;
    case 'rewrite': return <RewriteView {...props} />;
    case 'apply': return <ApplyView {...props} />;
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

// ============================================================================
// HoleView
// ============================================================================

function HoleView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, inductiveMap, registry }: NodeViewProps) {
  const isFocused = cursorId === node.id;
  const inputRef = useRef<HTMLInputElement>(null);

  const handleSubmit = useCallback((value: string) => {
    if (!tacticMode) return;
    let result: ProofTreeState | null = null;
    switch (tacticMode.tactic) {
      case 'intros': {
        const names = value.split(',').map(s => s.trim()).filter(Boolean);
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
            const ctorInfos = generateCaseInfos(scrutinee, indInfo, rev);
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
      case 'rewrite': {
        const name = value.trim();
        if (name) result = applyRewrite(state, name);
        break;
      }
      case 'apply': {
        const name = value.trim();
        if (name) result = applyApplyTactic(state, name);
        break;
      }
    }
    if (result) onPushChange(result);
    onTacticMode(null);
  }, [tacticMode, state, onPushChange, onTacticMode]);

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
        <span style={{ display: 'inline-flex', gap: '4px', alignItems: 'center' }}>
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
          <button style={btnStyle} onClick={(e) => { e.stopPropagation(); onTacticMode({ tactic: 'rewrite' }); }}>
            Rewrite...
          </button>
          <button style={btnStyle} onClick={(e) => { e.stopPropagation(); onTacticMode({ tactic: 'apply' }); }}>
            Apply...
          </button>
        </span>
      )}

      {isFocused && activeTactic && (
        <span style={{ display: 'inline-flex', gap: '4px', alignItems: 'center' }}>
          <span style={keywordStyle}>
            {activeTactic === 'intros' ? 'Given' :
             activeTactic === 'induction' ? 'Induct on' :
             activeTactic === 'unfold' ? 'Unfold' :
             activeTactic === 'rewrite' ? 'Rewrite' :
             activeTactic === 'apply' ? 'Apply' :
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
              activeTactic === 'rewrite' ? 'lemma name' :
              activeTactic === 'apply' ? 'lemma name' :
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

function IntrosView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, inductiveMap, registry }: NodeViewProps) {
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

  return (
    <>
      <div style={nodeRowStyle(depth, isFocused)} onClick={() => onClickNode(node.id)}>
        <span style={keywordStyle}>Given </span>
        <InlineKaTeX latex={namesLatex(node.names)} style={{ fontSize: '13px' }} />
        <span style={mutedStyle}>,</span>
      </div>
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
      />
    </>
  );
}

// ============================================================================
// InductionView
// ============================================================================

function InductionView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, inductiveMap, registry }: NodeViewProps) {
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

  return (
    <>
      <div style={nodeRowStyle(depth, isFocused)} onClick={() => onClickNode(node.id)}>
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
      </div>

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
}

function CaseView({
  caseNode, caseIndex, inductionId, depth,
  cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode,
  typedContext, inductiveMap, registry,
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
        />
      )}
    </>
  );
}

// ============================================================================
// UnfoldView — renders "unfold <name>,"
// ============================================================================

function UnfoldView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, inductiveMap, registry }: NodeViewProps) {
  if (node.tag !== 'unfold') return null;
  const isFocused = cursorId === node.id;

  return (
    <>
      <div style={nodeRowStyle(depth, isFocused)} onClick={() => onClickNode(node.id)}>
        <span style={keywordStyle}>unfold </span>
        <span style={{ color: '#79c0ff' }}>{node.name}</span>
        <span style={mutedStyle}>,</span>
      </div>
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
      />
    </>
  );
}

// ============================================================================
// RewriteView — renders "rewrite <name>,"
// ============================================================================

function RewriteView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, inductiveMap, registry }: NodeViewProps) {
  if (node.tag !== 'rewrite') return null;
  const isFocused = cursorId === node.id;

  return (
    <>
      <div style={nodeRowStyle(depth, isFocused)} onClick={() => onClickNode(node.id)}>
        <span style={keywordStyle}>rewrite </span>
        <span style={{ color: '#79c0ff' }}>{node.name}</span>
        <span style={mutedStyle}>,</span>
      </div>
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
      />
    </>
  );
}

// ============================================================================
// ApplyView — renders "apply <name>,"
// ============================================================================

function ApplyView({ node, depth, cursorId, state, tacticMode, onTacticMode, onPushChange, onClickNode, typedContext, inductiveMap, registry }: NodeViewProps) {
  if (node.tag !== 'apply') return null;
  const isFocused = cursorId === node.id;

  return (
    <>
      <div style={nodeRowStyle(depth, isFocused)} onClick={() => onClickNode(node.id)}>
        <span style={keywordStyle}>apply </span>
        <span style={{ color: '#79c0ff' }}>{node.name}</span>
        <span style={mutedStyle}>,</span>
      </div>
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
      />
    </>
  );
}

// ============================================================================
// ExactView
// ============================================================================

function ExactView({ node, depth, cursorId, onClickNode }: NodeViewProps) {
  if (node.tag !== 'exact') return null;
  const isFocused = cursorId === node.id;

  return (
    <div style={nodeRowStyle(depth, isFocused)} onClick={() => onClickNode(node.id)}>
      <span style={keywordStyle}>by </span>
      <InlineKaTeX
        latex={textToLatex(node.expr)}
        style={{ fontSize: '13px' }}
      />
    </div>
  );
}
