import { useCallback, useEffect, useMemo, useRef, useState } from 'react';
import { useSearchParams } from 'react-router-dom';
import Editor, { type OnMount } from '@monaco-editor/react';
import type { editor } from 'monaco-editor';
import type { AnalyzeResult, LeanDeclaration, LeanGoal, LeanGoalState, LeanMessage, LeanSeverity } from '../lean/types';
import { pickGoalAtCursor } from '../lean/goalAtCursor';
import { LEAN_PRESETS, DEFAULT_LEAN_SOURCE } from '../lean/presets';
import { findPresetBySlug, parseEditorUrlParams, presetSlug, resolveSymbolName } from '../lean/presetLookup';
import { analyzeRequest } from '../lean/analyzeClient';
import { LeanMathView } from './LeanMathView';
import { LeanMathEditor } from './LeanMathEditor';
import { LeanWysiwygPanel } from './LeanWysiwygPanel';

/**
 * The leanUI editor — running entirely on Lean 4.
 *
 * Monaco source box, a live goal-at-cursor panel (the InfoView equivalent, fed
 * by the InfoTree extractor), a declarations list, and diagnostics — all from
 * `POST /api/analyze`. This is the default editor; the legacy TT/TTK page lives
 * at /tt-legacy during the migration (removed in M5). The WYSIWYG panel returns
 * here in M3 once Lean expressions render to the math editor.
 */

// ── theme (matches the app's dark chrome) ──────────────────────────────────
const C = {
  bg: '#0d1117',
  panel: '#161b22',
  border: '#30363d',
  label: '#8b949e',
  text: '#c9d1d9',
  blue: '#79c0ff',
  purple: '#d2a8ff',
  teal: '#39c5bb',
  amber: '#d29922',
  red: '#f85149',
  green: '#3fb950',
  faint: '#484f58',
};

const SEVERITY_COLOR: Record<LeanSeverity, string> = {
  error: C.red,
  warning: C.amber,
  information: C.blue,
  hint: C.faint,
};

const KIND_COLOR: Record<LeanDeclaration['kind'], string> = {
  def: C.blue,
  theorem: C.purple,
  inductive: C.teal,
  axiom: C.amber,
  opaque: C.faint,
};

function severityToMarker(sev: LeanSeverity): number {
  // monaco MarkerSeverity: Hint=1, Info=2, Warning=4, Error=8
  switch (sev) {
    case 'error':
      return 8;
    case 'warning':
      return 4;
    case 'information':
      return 2;
    default:
      return 1;
  }
}

const mono = "'JetBrains Mono', 'Fira Code', 'Consolas', monospace";

const sectionHeader: React.CSSProperties = {
  padding: '6px 12px',
  fontSize: 11,
  fontWeight: 600,
  color: C.label,
  textTransform: 'uppercase',
  letterSpacing: '0.5px',
  backgroundColor: C.panel,
  borderBottom: `1px solid ${C.border}`,
  flexShrink: 0,
};

export function LeanEditorPage() {
  const [searchParams, setSearchParams] = useSearchParams();
  // Deep-link params (`?preset=real-analysis&symbol=limitAdd`), parsed ONCE at
  // mount: the preset seeds the initial source (so the very first analyze runs
  // on it, not on the default source), and the symbol is held pending until the
  // async analyze produces declarations to resolve it against.
  const [initialParams] = useState(() => parseEditorUrlParams(searchParams, LEAN_PRESETS));
  /** The preset the URL currently names — what the picker should display. */
  const currentPresetName = useMemo(() => {
    const p = searchParams.get('preset');
    return p ? (findPresetBySlug(LEAN_PRESETS, p)?.name ?? '') : '';
  }, [searchParams]);
  const [source, setSource] = useState(initialParams.preset?.code ?? DEFAULT_LEAN_SOURCE);
  const [mathlib, setMathlib] = useState(initialParams.preset?.mathlib ?? false);
  const [pendingSymbol, setPendingSymbol] = useState<string | null>(initialParams.symbol);
  const [wysiwyg, setWysiwyg] = useState(true);
  const [result, setResult] = useState<AnalyzeResult | null>(null);
  const [loading, setLoading] = useState(false);
  // Cursor in Lean convention: 1-based line, 0-based column.
  const [cursor, setCursor] = useState<{ line: number; col: number }>({ line: 1, col: 0 });

  const editorRef = useRef<editor.IStandaloneCodeEditor | null>(null);
  const monacoRef = useRef<typeof import('monaco-editor') | null>(null);

  const handleMount: OnMount = useCallback((ed, monaco) => {
    editorRef.current = ed;
    monacoRef.current = monaco;
    ed.onDidChangeCursorPosition((e) => {
      setCursor({ line: e.position.lineNumber, col: e.position.column - 1 });
    });
  }, []);

  // Did the latest source change come from a structured-proof write-back?
  // Those re-splice one decl's proof; the full-file analyze they trigger is
  // pure background (markers/decl list barely change) and must NOT contend
  // with the interactive goal refresh — so it gets a long debounce.
  const proofEditRef = useRef(false);

  // Imperatively set editor text (preset load) so cursor handling stays sane.
  const loadSource = useCallback((code: string, fromProofEdit = false) => {
    proofEditRef.current = fromProofEdit;
    setSource(code);
    const ed = editorRef.current;
    const model = ed?.getModel();
    if (model && model.getValue() !== code) model.setValue(code);
  }, []);

  const loadPreset = useCallback(
    (name: string) => {
      const p = LEAN_PRESETS.find((x) => x.name === name);
      if (!p) return;
      if (p.mathlib) setMathlib(true);
      // A deep-linked symbol belongs to the deep-linked preset; drop it and
      // keep the URL shareable for the newly chosen preset.
      setPendingSymbol(null);
      setSearchParams({ preset: presetSlug(p.name) }, { replace: true });
      loadSource(p.code);
    },
    [loadSource, setSearchParams],
  );

  // Debounced analyze on source / mathlib change. Proof write-backs wait much
  // longer: during an interactive proof burst (tactic click every second or
  // two) the timer keeps resetting, so the heavyweight full-file analyze only
  // runs once the user pauses — never racing the goal refresh for a worker.
  useEffect(() => {
    let cancelled = false;
    const delay = proofEditRef.current ? 2500 : 450;
    const handle = setTimeout(async () => {
      setLoading(true);
      try {
        // BACKGROUND + non-priority: this full-file analyze (decl cards,
        // markers, messages) is the slowest and least latency-critical
        // request — it must hold neither a browser connection nor a server
        // worker the goal refresh needs. Markers arriving a couple of seconds
        // late is fine; a stale goal is not.
        const data = await analyzeRequest({ source, mathlib }, { background: true });
        if (!data) throw new Error('analyze request failed');
        if (!cancelled) setResult(data);
      } catch (e) {
        if (!cancelled) {
          setResult({
            success: false,
            messages: [],
            goals: [],
            declarations: [],
            bridgeError: `Request failed: ${e instanceof Error ? e.message : String(e)}`,
            durationMs: 0,
          });
        }
      } finally {
        if (!cancelled) setLoading(false);
      }
    }, delay);
    return () => {
      cancelled = true;
      clearTimeout(handle);
    };
  }, [source, mathlib]);

  // Reflect messages as Monaco markers.
  useEffect(() => {
    const ed = editorRef.current;
    const monaco = monacoRef.current;
    if (!ed || !monaco) return;
    const model = ed.getModel();
    if (!model) return;
    const markers = (result?.messages ?? []).map((m) => ({
      severity: severityToMarker(m.severity),
      message: m.text,
      startLineNumber: m.startLine,
      startColumn: m.startCol + 1,
      endLineNumber: m.endLine,
      endColumn: m.endCol + 1,
    }));
    monaco.editor.setModelMarkers(model, 'lean', markers);
  }, [result]);

  const messages = result?.messages ?? [];
  const goals = result?.goals ?? [];
  const declarations = result?.declarations ?? [];
  const errorCount = messages.filter((m) => m.severity === 'error').length;

  // Deep-linked `?symbol=` → the canonical declaration name to auto-expand,
  // resolvable only once the async analyze has produced declarations.
  const autoExpandName = useMemo(
    () => (pendingSymbol && declarations.length > 0 ? resolveSymbolName(declarations, pendingSymbol) : null),
    [pendingSymbol, declarations],
  );
  // Declarations arrived but the symbol isn't among them → it never will be
  // (same source re-analyzes to the same list); drop it with a warning.
  useEffect(() => {
    if (pendingSymbol && declarations.length > 0 && autoExpandName === null) {
      console.warn(`?symbol=${pendingSymbol}: no declaration with that name in this preset`);
      setPendingSymbol(null);
    }
  }, [pendingSymbol, declarations, autoExpandName]);

  const activeGoal: LeanGoal | null = useMemo(
    () => pickGoalAtCursor(goals, cursor.line, cursor.col),
    [goals, cursor.line, cursor.col],
  );

  const statusText = loading
    ? 'checking…'
    : result
      ? result.bridgeError
        ? '⚠ bridge error'
        : result.success
          ? `✓ ok (${result.durationMs}ms)`
          : `✗ ${errorCount} error${errorCount === 1 ? '' : 's'} (${result.durationMs}ms)`
      : '—';

  return (
    <div style={{ display: 'flex', flexDirection: 'column', height: '100vh', background: C.bg, color: C.text, fontFamily: 'system-ui, sans-serif' }}>
      <header
        style={{
          display: 'flex',
          alignItems: 'center',
          gap: 16,
          padding: '8px 14px',
          borderBottom: `1px solid ${C.border}`,
          background: C.panel,
        }}
      >
        <strong style={{ color: C.text }}>leanUI</strong>
        <span style={{ fontSize: 11, color: C.label, textTransform: 'uppercase', letterSpacing: 0.5 }}>Lean 4</span>

        <label style={{ fontSize: 12, color: C.label }}>
          Example:{' '}
          <select
            // Driven by the URL, which loadPreset keeps current — so the
            // picker names what you are actually looking at, whether you chose
            // it here or arrived on a deep link. (It used to snap back to
            // "choose…" every time, so it never told you anything.)
            value={currentPresetName}
            onChange={(e) => {
              if (e.target.value) loadPreset(e.target.value);
            }}
            style={{ background: C.bg, color: C.text, border: `1px solid ${C.border}`, borderRadius: 4, padding: '2px 6px' }}
          >
            <option value="">choose…</option>
            {LEAN_PRESETS.map((p) => (
              <option key={p.name} value={p.name}>
                {p.name}
                {p.mathlib ? ' (Mathlib)' : ''}
              </option>
            ))}
          </select>
        </label>

        <label style={{ display: 'flex', alignItems: 'center', gap: 6, fontSize: 12, color: C.label }}>
          <input type="checkbox" checked={mathlib} onChange={(e) => setMathlib(e.target.checked)} />
          Mathlib
        </label>
        <label style={{ display: 'flex', alignItems: 'center', gap: 6, fontSize: 12, color: C.label }}>
          <input type="checkbox" checked={wysiwyg} onChange={(e) => setWysiwyg(e.target.checked)} />
          WYSIWYG
        </label>

        <span style={{ fontSize: 12, color: result?.success ? C.green : C.label }}>{statusText}</span>
        <span style={{ marginLeft: 'auto', fontSize: 11, color: C.faint }}>
          cursor {cursor.line}:{cursor.col}
        </span>
      </header>

      <div style={{ display: 'flex', flex: 1, minHeight: 0 }}>
        {/* Source */}
        <div style={{ flex: 1.3, minWidth: 0, borderRight: `1px solid ${C.border}`, display: 'flex', flexDirection: 'column' }}>
          <div style={sectionHeader}>Source</div>
          <div style={{ flex: 1, minHeight: 0 }}>
            <Editor
              height="100%"
              theme="vs-dark"
              defaultLanguage="plaintext"
              value={source}
              onChange={(v) => { proofEditRef.current = false; setSource(v ?? ''); }}
              onMount={handleMount}
              options={{ minimap: { enabled: false }, fontSize: 14, scrollBeyondLastLine: false, automaticLayout: true }}
            />
          </div>
        </div>

        {/* Right column: WYSIWYG structured editor, or goal/declarations/messages. */}
        <div style={{ flex: 1, minWidth: 0, display: 'flex', flexDirection: 'column' }}>
          {wysiwyg ? (
            <>
              <div style={{ flex: 1, minHeight: 0, borderBottom: `1px solid ${C.border}`, overflow: 'hidden' }}>
                <LeanWysiwygPanel
                  declarations={declarations}
                  goals={goals}
                  source={source}
                  mathlib={mathlib}
                  onSourceChange={(next) => loadSource(next, true)}
                  autoExpandSymbol={autoExpandName}
                  onAutoExpandConsumed={() => setPendingSymbol(null)}
                />
              </div>
              <MessagesPanel messages={messages} bridgeError={result?.bridgeError} loading={loading} />
            </>
          ) : (
            <>
              <GoalPanel goal={activeGoal} />
              <DeclarationsPanel declarations={declarations} />
              <MessagesPanel messages={messages} bridgeError={result?.bridgeError} loading={loading} />
            </>
          )}
        </div>
      </div>
    </div>
  );
}

function GoalPanel({ goal }: { goal: LeanGoal | null }) {
  return (
    <div style={{ flex: 1, minHeight: 0, display: 'flex', flexDirection: 'column', borderBottom: `1px solid ${C.border}` }}>
      <div style={sectionHeader}>Goal {goal ? `(${goal.goals.length})` : ''}</div>
      <div style={{ flex: 1, overflow: 'auto', padding: 12 }}>
        {!goal && <div style={{ color: C.faint, fontSize: 13 }}>Move the cursor into a proof to see the goal.</div>}
        {goal?.goals.length === 0 && <div style={{ color: C.green, fontSize: 13 }}>No goals — proof complete here. 🎉</div>}
        {goal?.goals.map((g, i) => (
          <GoalStateView key={i} state={g} index={i} count={goal.goals.length} />
        ))}
      </div>
    </div>
  );
}

/** One open goal rendered as WYSIWYG math: hypotheses then ⊢ target. */
function GoalStateView({ state, index, count }: { state: LeanGoalState; index: number; count: number }) {
  return (
    <div
      style={{
        margin: '0 0 12px',
        padding: 10,
        background: C.panel,
        border: `1px solid ${C.border}`,
        borderRadius: 6,
        fontSize: 14,
        lineHeight: 1.6,
        color: C.text,
      }}
    >
      {(count > 1 || state.case) && (
        <div style={{ fontSize: 11, color: C.faint, marginBottom: 6 }}>
          {count > 1 ? `goal ${index + 1}/${count}` : ''}
          {count > 1 && state.case ? ' · ' : ''}
          {state.case ? `case ${state.case}` : ''}
        </div>
      )}
      {state.hyps.map((h, hi) => (
        <div key={hi} style={{ marginBottom: 2 }}>
          <span style={{ fontFamily: mono, color: C.purple }}>{h.names.join(' ')}</span>
          <span style={{ color: C.label }}> : </span>
          <LeanMathView tagged={h.type} />
        </div>
      ))}
      <div style={{ marginTop: state.hyps.length ? 6 : 0, display: 'flex', gap: 6 }}>
        <span style={{ color: C.green }}>⊢</span>
        <LeanMathView tagged={state.targetTagged} fallback={state.plain} />
      </div>
    </div>
  );
}

function DeclarationsPanel({ declarations }: { declarations: LeanDeclaration[] }) {
  // Which declaration is being structurally edited (click to activate).
  const [activeKey, setActiveKey] = useState<string | null>(null);
  return (
    <div style={{ flex: 1, minHeight: 0, display: 'flex', flexDirection: 'column', borderBottom: `1px solid ${C.border}` }}>
      <div style={sectionHeader}>Declarations {declarations.length ? `(${declarations.length})` : ''}</div>
      <div style={{ flex: 1, overflow: 'auto', padding: 12 }}>
        {declarations.length === 0 && <div style={{ color: C.faint, fontSize: 13 }}>No declarations.</div>}
        {declarations.map((d) => {
          const key = `${d.name}@${d.line}:${d.col}`;
          return (
            <DeclarationCard
              key={key}
              decl={d}
              active={activeKey === key}
              onActivate={() => setActiveKey(key)}
            />
          );
        })}
      </div>
    </div>
  );
}

/**
 * One declaration as a structured-editor card. Shows read-only WYSIWYG math by
 * default; clicking activates the interactive structured editor (the real
 * MathEditor) over the same Lean-derived MathRow.
 */
function DeclarationCard({
  decl,
  active,
  onActivate,
}: {
  decl: LeanDeclaration;
  active: boolean;
  onActivate: () => void;
}) {
  return (
    <div
      onClick={active ? undefined : onActivate}
      style={{
        marginBottom: 10,
        padding: active ? 8 : 0,
        borderRadius: 6,
        border: active ? `1px solid ${C.border}` : '1px solid transparent',
        background: active ? C.panel : 'transparent',
        cursor: active ? 'default' : 'pointer',
      }}
    >
      <div style={{ display: 'flex', alignItems: 'baseline', gap: 6 }}>
        <span
          style={{
            fontSize: 10,
            fontWeight: 700,
            textTransform: 'uppercase',
            color: C.bg,
            background: KIND_COLOR[decl.kind],
            borderRadius: 4,
            padding: '1px 5px',
          }}
        >
          {decl.kind}
        </span>
        <span style={{ fontWeight: 600, fontFamily: mono, color: C.text }}>{decl.name}</span>
        {active && <span style={{ marginLeft: 'auto', fontSize: 10, color: C.faint }}>editing</span>}
      </div>

      {/* Type — interactive structured editor when active, static math otherwise. */}
      <div style={{ margin: '4px 0 0', fontSize: 15, color: C.text, lineHeight: 1.5 }}>
        <span style={{ color: C.label }}>: </span>
        {active ? (
          <LeanMathEditor tagged={decl.typeTagged} active />
        ) : (
          <LeanMathView tagged={decl.typeTagged} fallback={decl.prettyType} />
        )}
        {decl.valueTagged !== undefined && (
          <div style={{ marginTop: 2 }}>
            <span style={{ color: C.label }}>:= </span>
            {active ? (
              <LeanMathEditor tagged={decl.valueTagged} />
            ) : (
              <LeanMathView tagged={decl.valueTagged} fallback={decl.prettyValue ?? ''} />
            )}
          </div>
        )}
      </div>
    </div>
  );
}

function MessagesPanel({
  messages,
  bridgeError,
  loading,
}: {
  messages: LeanMessage[];
  bridgeError?: string;
  loading: boolean;
}) {
  return (
    <div style={{ flex: 1, minHeight: 0, display: 'flex', flexDirection: 'column' }}>
      <div style={sectionHeader}>Messages {messages.length ? `(${messages.length})` : ''}</div>
      <div style={{ flex: 1, overflow: 'auto', padding: 12, fontSize: 13 }}>
        {bridgeError && (
          <div style={{ color: C.red, marginBottom: 12, whiteSpace: 'pre-wrap' }}>
            <strong>Bridge error:</strong> {bridgeError}
          </div>
        )}
        {messages.length === 0 && !bridgeError && (
          <div style={{ color: C.faint }}>{loading ? 'Checking with Lean…' : 'No messages.'}</div>
        )}
        {messages.map((m, i) => (
          <div key={i} style={{ marginBottom: 10, paddingLeft: 8, borderLeft: `3px solid ${SEVERITY_COLOR[m.severity]}` }}>
            <div style={{ color: SEVERITY_COLOR[m.severity], fontWeight: 600 }}>
              {m.severity} · {m.startLine}:{m.startCol + 1}
            </div>
            <pre style={{ margin: '2px 0 0', whiteSpace: 'pre-wrap', fontFamily: mono, color: C.text }}>{m.text}</pre>
          </div>
        ))}
      </div>
    </div>
  );
}
