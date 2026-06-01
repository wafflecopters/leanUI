import { useCallback, useEffect, useMemo, useRef, useState } from 'react';
import Editor, { type OnMount } from '@monaco-editor/react';
import type { editor } from 'monaco-editor';
import type { AnalyzeResult, LeanDeclaration, LeanGoal, LeanMessage, LeanSeverity } from '../lean/types';
import { pickGoalAtCursor } from '../lean/goalAtCursor';

/**
 * Lean-backed editor page (route `/lean`).
 *
 * A real proof editor running entirely on Lean 4: Monaco source box, a live
 * goal-at-cursor panel (the InfoView equivalent, fed by the InfoTree extractor),
 * and a diagnostics list — all from `POST /api/analyze`. Deliberately separate
 * from the legacy TT/TTK `TextEditorPage` while the backend swap is in progress.
 */

const SAMPLE = `-- leanUI · running on real Lean 4
-- Put your cursor inside a proof to see the goal state on the right.

def double (n : Nat) : Nat := n + n

#check double

theorem add_zero_ex (n : Nat) : n + 0 = n := by
  rfl

theorem add_comm_ex (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ k ih => simp [Nat.succ_add, ih]

-- An error, to show diagnostics:
def bad : Nat := "not a nat"
`;

const SEVERITY_COLOR: Record<LeanSeverity, string> = {
  error: '#e5484d',
  warning: '#f5a623',
  information: '#3b82f6',
  hint: '#8b8b8b',
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

export function LeanEditorPage() {
  const [source, setSource] = useState(SAMPLE);
  const [mathlib, setMathlib] = useState(false);
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

  // Debounced analyze on source / mathlib change.
  useEffect(() => {
    let cancelled = false;
    const handle = setTimeout(async () => {
      setLoading(true);
      try {
        const resp = await fetch('/api/analyze', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({ source, mathlib }),
        });
        const data: AnalyzeResult = await resp.json();
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
    }, 450);
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
    <div style={{ display: 'flex', flexDirection: 'column', height: '100vh', fontFamily: 'system-ui, sans-serif' }}>
      <header
        style={{
          display: 'flex',
          alignItems: 'center',
          gap: 16,
          padding: '8px 16px',
          borderBottom: '1px solid #ddd',
          background: '#fafafa',
        }}
      >
        <strong>leanUI · Lean 4 backend</strong>
        <label style={{ display: 'flex', alignItems: 'center', gap: 6, fontSize: 13 }}>
          <input type="checkbox" checked={mathlib} onChange={(e) => setMathlib(e.target.checked)} />
          Mathlib
        </label>
        <span style={{ fontSize: 13, color: '#666' }}>{statusText}</span>
        <span style={{ marginLeft: 'auto', fontSize: 12, color: '#999' }}>
          cursor {cursor.line}:{cursor.col}
        </span>
      </header>

      <div style={{ display: 'flex', flex: 1, minHeight: 0 }}>
        {/* Source */}
        <div style={{ flex: 1.3, minWidth: 0, borderRight: '1px solid #ddd' }}>
          <Editor
            height="100%"
            defaultLanguage="plaintext"
            value={source}
            onChange={(v) => setSource(v ?? '')}
            onMount={handleMount}
            options={{ minimap: { enabled: false }, fontSize: 14, scrollBeyondLastLine: false }}
          />
        </div>

        {/* Right column: goal-at-cursor + declarations + diagnostics */}
        <div style={{ flex: 1, minWidth: 0, display: 'flex', flexDirection: 'column' }}>
          <GoalPanel goal={activeGoal} />
          <DeclarationsPanel declarations={declarations} />
          <MessagesPanel messages={messages} bridgeError={result?.bridgeError} loading={loading} />
        </div>
      </div>
    </div>
  );
}

function GoalPanel({ goal }: { goal: LeanGoal | null }) {
  return (
    <div style={{ flex: 1, minHeight: 0, overflow: 'auto', padding: 12, borderBottom: '1px solid #ddd' }}>
      <div style={{ fontSize: 12, fontWeight: 700, color: '#666', marginBottom: 8, letterSpacing: 0.5 }}>
        GOAL {goal ? `(${goal.goals.length})` : ''}
      </div>
      {!goal && <div style={{ color: '#999', fontSize: 13 }}>No goal at cursor.</div>}
      {goal?.goals.length === 0 && (
        <div style={{ color: '#2e9e5b', fontSize: 13 }}>No goals — proof complete here. 🎉</div>
      )}
      {goal?.goals.map((g, i) => (
        <pre
          key={i}
          style={{
            margin: '0 0 12px',
            padding: 10,
            background: '#f6f8fa',
            borderRadius: 6,
            whiteSpace: 'pre-wrap',
            fontFamily: 'ui-monospace, SFMono-Regular, monospace',
            fontSize: 13,
            lineHeight: 1.5,
          }}
        >
          {g}
        </pre>
      ))}
    </div>
  );
}

const KIND_COLOR: Record<LeanDeclaration['kind'], string> = {
  def: '#3b82f6',
  theorem: '#8b5cf6',
  inductive: '#0d9488',
  axiom: '#b45309',
  opaque: '#6b7280',
};

function DeclarationsPanel({ declarations }: { declarations: LeanDeclaration[] }) {
  return (
    <div style={{ flex: 1, minHeight: 0, overflow: 'auto', padding: 12, borderBottom: '1px solid #ddd' }}>
      <div style={{ fontSize: 12, fontWeight: 700, color: '#666', marginBottom: 8, letterSpacing: 0.5 }}>
        DECLARATIONS {declarations.length ? `(${declarations.length})` : ''}
      </div>
      {declarations.length === 0 && <div style={{ color: '#999', fontSize: 13 }}>No declarations.</div>}
      {declarations.map((d, i) => (
        <div key={i} style={{ marginBottom: 10 }}>
          <div style={{ display: 'flex', alignItems: 'baseline', gap: 6 }}>
            <span
              style={{
                fontSize: 10,
                fontWeight: 700,
                textTransform: 'uppercase',
                color: '#fff',
                background: KIND_COLOR[d.kind],
                borderRadius: 4,
                padding: '1px 5px',
              }}
            >
              {d.kind}
            </span>
            <span style={{ fontWeight: 600, fontFamily: 'ui-monospace, monospace' }}>{d.name}</span>
          </div>
          <pre
            style={{
              margin: '3px 0 0',
              whiteSpace: 'pre-wrap',
              fontFamily: 'ui-monospace, monospace',
              fontSize: 12.5,
              color: '#333',
            }}
          >
            {': '}
            {d.prettyType}
            {d.prettyValue !== undefined ? `\n:= ${d.prettyValue}` : ''}
          </pre>
        </div>
      ))}
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
    <div style={{ flex: 1, minHeight: 0, overflow: 'auto', padding: 12, fontSize: 13 }}>
      <div style={{ fontSize: 12, fontWeight: 700, color: '#666', marginBottom: 8, letterSpacing: 0.5 }}>
        MESSAGES {messages.length ? `(${messages.length})` : ''}
      </div>
      {bridgeError && (
        <div style={{ color: SEVERITY_COLOR.error, marginBottom: 12, whiteSpace: 'pre-wrap' }}>
          <strong>Bridge error:</strong> {bridgeError}
        </div>
      )}
      {messages.length === 0 && !bridgeError && (
        <div style={{ color: '#999' }}>{loading ? 'Checking with Lean…' : 'No messages.'}</div>
      )}
      {messages.map((m, i) => (
        <div key={i} style={{ marginBottom: 10, paddingLeft: 8, borderLeft: `3px solid ${SEVERITY_COLOR[m.severity]}` }}>
          <div style={{ color: SEVERITY_COLOR[m.severity], fontWeight: 600 }}>
            {m.severity} · {m.startLine}:{m.startCol + 1}
          </div>
          <pre style={{ margin: '2px 0 0', whiteSpace: 'pre-wrap', fontFamily: 'ui-monospace, monospace' }}>{m.text}</pre>
        </div>
      ))}
    </div>
  );
}
