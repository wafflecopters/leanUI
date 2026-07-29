import { useEffect, useMemo, useState } from 'react';
import katex from 'katex';
import type { LeanDeclaration, LeanGoal } from '../lean/types';
import { declKey } from '../lean/declProofSteps';
import { LeanMathView } from './LeanMathView';
import { LeanMathEditor } from './LeanMathEditor';
import { ProofTreeEditor } from './ProofTreeEditor';
import { proofSeedBlock } from '../lean/extractTacticBlock';
import { applySubgoalCount, rewriteSideGoalCount } from '../lean/rewriteCandidates';
import { taggedToInteractiveGoal } from '../lean/leanInteractiveGoal';
import type { TacticSuggestion } from '../proof-tree/tactic-suggestions';
import { useProofSession } from '../controller/useProofSession';
import { createTermBuilderProvider } from '../controller/termBuilder';

/**
 * The structured WYSIWYG editor on Lean — uses the REAL ProofTreeEditor (and the
 * real math editors), with goals supplied by the Lean round-trip provider
 * (proof tree → Lean tactic source → InfoTree goals → NodeGoalInfo). One card
 * per declaration: interactive type/value math, plus the full structured proof
 * editor for theorems, seeded from the user's actual proof.
 */
const C = {
  bg: '#0d1117',
  panel: '#161b22',
  header: '#21262d',
  border: '#30363d',
  label: '#8b949e',
  faint: '#484f58',
  text: '#c9d1d9',
  blue: '#58a6ff',
  green: '#3fb950',
  purple: '#a371f7',
};
const mono = '"JetBrains Mono", "Fira Code", Menlo, Consolas, monospace';

/** Result lines a suggestion pill shows before it collapses into "+N more" — a
 *  pill previews the transform, it isn't the goal panel. */
const MAX_PREVIEW_LINES = 3;

/** Render a LaTeX goal string (KaTeX) — used for suggestion previews. */
function PreviewMath({ latex }: { latex: string }) {
  let html: string;
  try {
    html = katex.renderToString(latex, { displayMode: false, throwOnError: false, trust: true, strict: false });
  } catch {
    return <span style={{ fontFamily: mono, fontSize: 11, color: C.text }}>{latex}</span>;
  }
  return <span style={{ fontSize: 13, color: C.text }} dangerouslySetInnerHTML={{ __html: html }} />;
}

// Probe binder for the slot builder. NOT `__`-prefixed: Lean's interactive
// goal display filters double-underscore names as internal, which would hide
// the probed term's type from us.
const PROBE_NAME = 'leanuiProbe';

const KIND_COLOR: Record<LeanDeclaration['kind'], string> = {
  def: C.blue,
  theorem: C.purple,
  inductive: C.green,
  axiom: '#d29922',
  opaque: C.faint,
};

export function LeanWysiwygPanel({
  declarations,
  goals: _goals,
  source,
  mathlib,
  onSourceChange,
  autoExpandSymbol,
  onAutoExpandConsumed,
}: {
  declarations: LeanDeclaration[];
  goals: LeanGoal[];
  source: string;
  mathlib?: boolean;
  /** Write-back: structural proof edits reprint + splice into the source. */
  onSourceChange?: (next: string) => void;
  /** Deep link (`?symbol=…`): declaration name whose card opens EXPANDED when
   *  it first renders. Resolved by the page once the async analyze delivers
   *  declarations; consumed one-shot via `onAutoExpandConsumed`. */
  autoExpandSymbol?: string | null;
  onAutoExpandConsumed?: () => void;
}) {
  // Declaration start lines (sorted) to bound each declaration's source slice.
  const sortedLines = useMemo(
    () => [...declarations].map((d) => d.line).sort((a, b) => a - b),
    [declarations],
  );
  const nextLineOf = (line: number): number | undefined => sortedLines.find((l) => l > line);

  // ONE active card: only the declaration the user is working on runs its
  // Lean round-trips (goals + suggestions). Without this, EVERY provable decl
  // (67 in the Real-analysis preset!) mounted live hooks that all re-fired on
  // every source write-back — and each decl AFTER the edited one saw a new
  // prefix, stampeding dozens of parallel prefix recompiles per tactic click.
  // The visible goal refresh queued behind all of it. O(file) → O(1).
  const [activeKey, setActiveKey] = useState<string | null>(null);

  return (
    <div style={{ height: '100%', display: 'flex', flexDirection: 'column', color: C.text }}>
      <div
        style={{
          padding: '12px 16px 8px',
          color: '#e6edf3',
          fontSize: 13,
          fontWeight: 600,
          letterSpacing: '0.02em',
          flexShrink: 0,
        }}
      >
        WYSIWYG Editor
      </div>
      <div style={{ flex: 1, overflowY: 'auto', padding: '0 16px 16px' }}>
        {declarations.length === 0 && <div style={{ color: C.faint, fontSize: 13 }}>No declarations.</div>}
        {declarations.map((d) => (
          <DeclCard
            key={declKey(d)}
            decl={d}
            allDeclarations={declarations}
            source={source}
            // Whether this declaration can host an interactive proof at all —
            // the session refuses inductives, axioms and computational defs.
            tacticBlock={proofSeedBlock(source, d, nextLineOf(d.line))}
            mathlib={mathlib}
            active={activeKey === declKey(d)}
            onActivate={() => setActiveKey(declKey(d))}
            autoExpand={autoExpandSymbol != null && d.name === autoExpandSymbol}
            onAutoExpandConsumed={onAutoExpandConsumed}
            // The session splices its own proof into the file and hands back the
            // whole text, so the panel no longer does any source surgery.
            onSourceChange={onSourceChange}
          />
        ))}
      </div>
    </div>
  );
}

function DeclCard({
  decl,
  allDeclarations,
  source,
  tacticBlock,
  mathlib,
  active,
  onActivate,
  autoExpand,
  onAutoExpandConsumed,
  onSourceChange,
}: {
  decl: LeanDeclaration;
  allDeclarations: LeanDeclaration[];
  source: string;
  /** Non-null when this declaration has an interactive proof body. */
  tacticBlock: string | null;
  mathlib?: boolean;
  /** Only the ACTIVE card runs Lean round-trips (goals/suggestions). Any click
   *  in the card activates it — including the click that performs a tactic. */
  active?: boolean;
  onActivate?: () => void;
  /** Deep link: open this card expanded. One-shot — consumed on arrival, so a
   *  later user collapse sticks (no re-expansion tug-of-war). */
  autoExpand?: boolean;
  onAutoExpandConsumed?: () => void;
  /** Write-back: the session hands over the whole file, already spliced. */
  onSourceChange?: (next: string) => void;
}) {
  const [editing, setEditing] = useState(false);
  // Cards usually mount only after the async analyze delivers declarations, so
  // a deep-linked card starts expanded via the initializer; the effect covers
  // the late-arrival path (autoExpand turning on after mount) and consumption.
  const [expanded, setExpanded] = useState(autoExpand ?? false);
  useEffect(() => {
    if (autoExpand) {
      setExpanded(true);
      onActivate?.(); // deep-linked card is the one being worked on
      onAutoExpandConsumed?.();
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [autoExpand]);
  // Any provable decl (theorem or def/example with a term/sorry body) gets the
  // structured proof-tree editor — select the sorry and build a proof.
  const isProof = tacticBlock !== null;

  const headerBtn = (active: boolean, activeColor = C.green): React.CSSProperties => ({
    background: 'none',
    border: `1px solid ${C.border}`,
    borderRadius: 4,
    cursor: 'pointer',
    color: active ? activeColor : C.label,
    fontSize: 11,
    padding: '2px 8px',
  });

  // The card body (type/value + structured proof editor). Rendered inline OR in
  // the expanded modal — never both, so the single LeanProofEditor keeps one
  // instance. Re-seeds from source on toggle (the proof itself is persisted).
  const body = (
    <>
      {/* Type (+ value for defs) — no leading ":" label; the type sits on its
          own line under the name, so a colon would just dangle. */}
      <div style={{ padding: '8px 10px', borderBottom: isProof ? `1px solid ${C.border}` : 'none' }}>
        <div style={{ fontSize: 15, lineHeight: 1.6 }}>
          {editing ? (
            <LeanMathEditor tagged={decl.typeTagged} active />
          ) : (
            <LeanMathView tagged={decl.typeTagged} fallback={decl.prettyType} />
          )}
        </div>
        {!isProof && decl.valueTagged !== undefined && (
          <div style={{ fontSize: 15, lineHeight: 1.6, marginTop: 4 }}>
            <span style={{ color: C.label }}>:= </span>
            {editing ? (
              <LeanMathEditor tagged={decl.valueTagged} active />
            ) : (
              <LeanMathView tagged={decl.valueTagged} fallback={decl.prettyValue ?? ''} />
            )}
          </div>
        )}
      </div>
      {isProof && tacticBlock !== null && (
        <LeanProofEditor
          decl={decl}
          allDeclarations={allDeclarations}
          source={source}
          mathlib={mathlib}
          active={active}
          onSourceChange={onSourceChange}
        />
      )}
    </>
  );

  const kindLabel = (
    <span style={{ fontSize: 11, fontWeight: 600, color: KIND_COLOR[decl.kind], textTransform: 'uppercase', letterSpacing: '0.04em' }}>
      {decl.kind}
    </span>
  );

  return (
    <div
      // Any interaction with the card makes it THE active one (live Lean
      // round-trips); the same click also performs its action (bubbling).
      onClick={active ? undefined : onActivate}
      style={{ marginBottom: 12, border: `1px solid ${active ? '#2f5c8f' : C.border}`, borderRadius: 6, overflow: 'hidden', backgroundColor: C.panel }}
    >
      <div style={{ display: 'flex', alignItems: 'center', gap: 8, padding: '6px 10px', backgroundColor: C.header, borderBottom: `1px solid ${C.border}` }}>
        {kindLabel}
        <span style={{ flex: 1, fontFamily: mono, fontSize: 13, fontWeight: 500, color: '#e6edf3' }}>{decl.name}</span>
        <button onClick={() => setExpanded(true)} title="Open in a large view" style={headerBtn(false)}>expand</button>
        <button onClick={() => setEditing((e) => !e)} style={headerBtn(editing)}>{editing ? 'done' : 'edit'}</button>
      </div>

      {/* Inline body only when not expanded (the body lives in the modal then). */}
      {expanded ? (
        <div style={{ padding: '14px 12px', color: C.faint, fontSize: 12, fontStyle: 'italic' }}>Opened in expanded view…</div>
      ) : (
        body
      )}

      {expanded && (
        <div
          onClick={() => setExpanded(false)}
          style={{ position: 'fixed', inset: 0, background: 'rgba(1, 4, 9, 0.78)', zIndex: 1000, display: 'flex', alignItems: 'center', justifyContent: 'center', padding: 24 }}
        >
          <div
            onClick={(e) => e.stopPropagation()}
            style={{ width: '92vw', height: '90vh', display: 'flex', flexDirection: 'column', backgroundColor: C.panel, border: `1px solid ${C.border}`, borderRadius: 8, overflow: 'hidden', boxShadow: '0 16px 48px rgba(0,0,0,0.6)' }}
          >
            <div style={{ display: 'flex', alignItems: 'center', gap: 8, padding: '10px 14px', backgroundColor: C.header, borderBottom: `1px solid ${C.border}`, flexShrink: 0 }}>
              {kindLabel}
              <span style={{ flex: 1, fontFamily: mono, fontSize: 15, fontWeight: 600, color: '#e6edf3' }}>{decl.name}</span>
              <button onClick={() => setEditing((e) => !e)} style={headerBtn(editing)}>{editing ? 'done' : 'edit'}</button>
              <button onClick={() => setExpanded(false)} style={headerBtn(false)}>collapse</button>
            </div>
            <div style={{ flex: 1, overflowY: 'auto' }}>{body}</div>
          </div>
        </div>
      )}
    </div>
  );
}

/**
 * The proof editor for one declaration — a VIEW over a `ProofSession`.
 *
 * Every decision (which tactics to try, what Lean said, what the user may do
 * next, what a move would produce) is the controller's; this component reads
 * `state` and renders it, and turns clicks into `session` calls. That's the
 * whole contract, and it's why the same proof flow can be driven from a test or
 * the REPL without a browser.
 */
function LeanProofEditor({
  decl,
  allDeclarations,
  source,
  mathlib,
  active = false,
  onSourceChange,
}: {
  decl: LeanDeclaration;
  allDeclarations: LeanDeclaration[];
  source: string;
  mathlib?: boolean;
  /** Only the active card runs Lean round-trips; inactive cards render the
   *  proof structure statically (their first click activates them). */
  active?: boolean;
  onSourceChange?: (next: string) => void;
}) {
  const { session, state, error, starting } = useProofSession({
    source,
    declarations: allDeclarations,
    declName: decl.name,
    mathlib,
    active,
    onSourceChange,
  });
  const [hoveredSuggestion, setHoveredSuggestion] = useState<string | null>(null);

  const termBuilderProvider = useMemo(
    () => (session ? createTermBuilderProvider(session) : undefined),
    [session],
  );

  // The clickable goal is rendered from Lean's tagged target.
  const interactiveGoal = useMemo(
    () => (session?.leanCursorGoal ? taggedToInteractiveGoal(session.leanCursorGoal.targetTagged) : null),
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [session, state?.goal?.targetText],
  );

  // The hypothesis action tray, straight from the action layer (so only moves
  // Lean accepted appear), with the prose labels the tray expects.
  const hypTraySuggestions = useMemo<TacticSuggestion[]>(
    () =>
      (state?.actions ?? [])
        .filter((a) => a.group === 'hypothesis')
        .map((a) => ({
          id: a.id,
          label: a.label,
          labelLatex: `\\text{${a.label.replace(/_/g, '\\_')}}`,
          description: a.description ?? '',
          ...(a.detail?.subgoals ? { numSubgoals: a.detail.subgoals } : {}),
        })),
    [state?.actions],
  );

  if (!session || !state) {
    return (
      <div style={{ padding: '6px 10px', fontSize: 12, color: C.faint }}>
        {starting ? '…' : (error ?? 'No interactive proof for this declaration.')}
      </div>
    );
  }

  const goalOpen = active && state.cursor.isHole && state.goal !== null;
  const errors = state.status.diagnostics.filter((d) => d.severity === 'error');
  const suggestionActions = state.actions.filter((a) => a.group === 'suggestion');
  const anyLoading = state.busy.goals || state.busy.suggestions;

  const suggestionPills =
    goalOpen && (suggestionActions.length > 0 || anyLoading) ? (
      <div style={{ marginTop: 8 }}>
        <div style={{ fontSize: 10, color: C.faint, marginBottom: 4, display: 'flex', gap: 8 }}>
          <span>SUGGESTIONS</span>
          {state.selection.subterm && (
            <span style={{ color: C.label }}>for {state.selection.subterm.text}</span>
          )}
          {anyLoading && <span style={{ color: C.label }}>searching…</span>}
        </div>
        <div style={{ display: 'flex', flexWrap: 'wrap', gap: 6 }}>
          {suggestionActions.map((a) => {
            // What the pill SHOWS above its tactic name: every goal the move
            // leaves, so a splitter reads as "you'd then owe 0 < ε and 0 < 2".
            // Capped — a pill is a preview, not the goal panel.
            const lines = a.detail?.previews ?? [];
            const shown = lines.slice(0, MAX_PREVIEW_LINES);
            const hidden = lines.length - shown.length;
            const closes = a.detail?.closes === true;
            const topLine = closes || shown.length > 0;
            return (
              <button
                key={a.id}
                onClick={() => session.dispatch({ id: a.id })}
                onMouseEnter={() => setHoveredSuggestion(a.id)}
                onMouseLeave={() => setHoveredSuggestion((h) => (h === a.id ? null : h))}
                title={a.detail?.tactic ?? a.label}
                style={{
                  display: 'flex',
                  flexDirection: 'column',
                  alignItems: 'flex-start',
                  gap: 1,
                  fontFamily: mono,
                  fontSize: 11,
                  color: C.text,
                  background: hoveredSuggestion === a.id ? C.header : C.bg,
                  border: `1px solid ${closes ? C.green : hoveredSuggestion === a.id ? C.blue : C.border}`,
                  borderRadius: 4,
                  padding: topLine ? '3px 8px' : '2px 8px',
                  cursor: 'pointer',
                  maxWidth: '100%',
                }}
              >
                {closes ? (
                  <span style={{ color: C.green, fontSize: 12, fontWeight: 600 }}>✓ Solve Goal</span>
                ) : shown.length > 0 ? (
                  <span style={{ display: 'flex', flexDirection: 'column', alignItems: 'flex-start', gap: 1 }}>
                    {shown.map((latex, i) => (
                      <span key={i} style={{ fontSize: 14, lineHeight: 1.2 }}>
                        <PreviewMath latex={latex} />
                      </span>
                    ))}
                    {hidden > 0 && <span style={{ color: C.faint, fontSize: 10 }}>+{hidden} more</span>}
                  </span>
                ) : null}
                <span style={{ color: topLine ? C.faint : C.text, fontSize: topLine ? 10 : 11 }}>{a.label}</span>
              </button>
            );
          })}
        </div>
      </div>
    ) : null;

  // While a goal refresh is in flight, the goal box above still shows the
  // PREVIOUS state — say so, loudly enough that "my tactic did nothing?!"
  // never happens again, but without hiding/reflowing anything.
  const goalUpdatingHint =
    goalOpen && state.busy.goals ? (
      <div style={{ marginTop: 6, fontSize: 11, color: '#d29922', fontFamily: mono }}>
        ⟳ goal updating — the state shown above may be one step behind…
      </div>
    ) : null;

  const suggestionSlot =
    goalUpdatingHint || suggestionPills ? (
      <>
        {goalUpdatingHint}
        {suggestionPills}
      </>
    ) : null;

  return (
    <div style={{ padding: '6px 10px' }}>
      <div style={{ fontSize: 10, color: C.faint, marginBottom: 4, letterSpacing: '0.03em', display: 'flex', gap: 8 }}>
        <span>PROOF</span>
        {state.busy.goals && <span style={{ color: C.label }}>checking…</span>}
        {state.status.complete && <span style={{ color: C.green }}>✓ complete</span>}
        {errors.length > 0 && <span style={{ color: '#f85149' }}>{errors.length} error{errors.length > 1 ? 's' : ''}</span>}
        {state.error && <span style={{ color: '#f85149' }}>⚠ {state.error.slice(0, 60)}</span>}
      </div>
      {/* What LEAN said about this proof. Silently swallowing these is how a
          structurally broken proof — a missing branch, an unsolved goal — ends
          up looking perfectly fine on screen. */}
      {errors.length > 0 && (
        <div
          style={{
            marginBottom: 6,
            border: `1px solid #f85149`,
            borderRadius: 4,
            background: 'rgba(248, 81, 73, 0.08)',
            padding: '6px 8px',
            fontFamily: mono,
            fontSize: 11,
            color: '#ffa198',
            maxHeight: 160,
            overflowY: 'auto',
          }}
        >
          {errors.map((d, i) => (
            <div key={i} style={{ whiteSpace: 'pre-wrap', marginBottom: i < errors.length - 1 ? 6 : 0 }}>
              ✗ {d.text}
            </div>
          ))}
        </div>
      )}
      <ProofTreeEditor
        history={session.treeHistory}
        onHistoryChange={(h) => session.adoptHistory(h)}
        goalMapOverride={session.leanGoalMap}
        typedContextOverride={session.leanTypedContext}
        interactiveGoalOverride={interactiveGoal}
        onGoalPathSelect={(path) => session.selectSubterm(path)}
        goalExtraSlot={suggestionSlot}
        applySubgoalCount={(name) => applySubgoalCount(allDeclarations, name)}
        rewriteSideGoalCount={(name) => rewriteSideGoalCount(allDeclarations, name)}
        hypSuggestionsOverride={hypTraySuggestions}
        onHypothesisSelect={(name) => session.selectHypothesis(name)}
        onApplySuggestionOverride={(s) => session.dispatch({ id: s.id }).ok}
        termBuilderProvider={termBuilderProvider}
      />
    </div>
  );
}
