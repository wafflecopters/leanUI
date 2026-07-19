import { useEffect, useMemo, useState } from 'react';
import katex from 'katex';
import type { LeanDeclaration, LeanGoal } from '../lean/types';
import { declKey } from '../lean/declProofSteps';
import { LeanMathView } from './LeanMathView';
import { LeanMathEditor } from './LeanMathEditor';
import { ProofTreeEditor } from './ProofTreeEditor';
import {
  createHistory,
  pushState,
  findNode,
  mkHole,
  replaceNode,
  withRewriteSideGoals,
  type ProofTreeHistory,
} from '../proof-tree/proof-tree';
import { findFirstHole } from '../proof-tree/tactic-to-tree';
import { leanTacticsToTree } from '../lean/leanTacticsToTree';
import { proofSeedBlock } from '../lean/extractTacticBlock';
import { spliceTacticBlock } from '../lean/spliceTacticBlock';
import { proofTreeToLean, proofTreeToSource } from '../lean/proofTreeToLean';
import { useLeanProofGoals } from '../lean/useLeanProofGoals';
import { useLeanSuggestions } from '../lean/useLeanSuggestions';
import { useLeanValidatedSuggestions } from '../lean/useLeanValidatedSuggestions';
import { equalityLemmas, rankByGoalOverlap, unfoldableDefs, applySubgoalCount, rewriteSideGoalCount } from '../lean/rewriteCandidates';
import { probeSimpFired } from '../lean/simpProbe';
import { taggedToInteractiveGoal, subtermTextMap, taggedText, posForGoalId, subtermLatexAtPos } from '../lean/leanInteractiveGoal';
import { targetedSuggestions, freshHypName, hypothesisSuggestions, type LeanSuggestion } from '../lean/leanSuggestions';
import type { TacticSuggestion } from '../proof-tree/tactic-suggestions';
import type { TermBuilderDisplay, TermBuilderProvider } from '../proof-tree/term-builder';
import { parseSlots, appliedExpr, appliedExprWithHoles, parseApplied, resolveGreekToHypNames, slotSuggestionNames, projectionCandidates, type TermSlot } from '../lean/termSlots';
import { assembleProofInSource } from '../lean/assembleProofDecl';
import { mathTextToLatex } from '../lean/codeWithInfos';
import { analyzeRequest } from '../lean/analyzeClient';
import { enrichInductionCaseNames } from '../lean/enrichInductionCases';

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
            nextDeclLine={nextLineOf(d.line)}
            tacticBlock={proofSeedBlock(source, d, nextLineOf(d.line))}
            mathlib={mathlib}
            active={activeKey === declKey(d)}
            onActivate={() => setActiveKey(declKey(d))}
            autoExpand={autoExpandSymbol != null && d.name === autoExpandSymbol}
            onAutoExpandConsumed={onAutoExpandConsumed}
            onProofChange={
              onSourceChange
                ? (newBlock) => onSourceChange(spliceTacticBlock(source, d, nextLineOf(d.line), newBlock))
                : undefined
            }
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
  nextDeclLine,
  tacticBlock,
  mathlib,
  active,
  onActivate,
  autoExpand,
  onAutoExpandConsumed,
  onProofChange,
}: {
  decl: LeanDeclaration;
  allDeclarations: LeanDeclaration[];
  source: string;
  nextDeclLine?: number;
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
  onProofChange?: (newBlock: string) => void;
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
          nextDeclLine={nextDeclLine}
          tacticBlock={tacticBlock}
          mathlib={mathlib}
          active={active}
          onProofChange={onProofChange}
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

function LeanProofEditor({
  decl,
  allDeclarations,
  source,
  nextDeclLine,
  tacticBlock,
  mathlib,
  active = false,
  onProofChange,
}: {
  decl: LeanDeclaration;
  allDeclarations: LeanDeclaration[];
  source: string;
  nextDeclLine?: number;
  tacticBlock: string;
  mathlib?: boolean;
  /** Only the active card runs Lean round-trips; inactive cards render the
   *  proof structure statically (their first click activates them). */
  active?: boolean;
  onProofChange?: (newBlock: string) => void;
}) {
  // Seed the proof tree from the user's actual Lean proof. Re-seed only on
  // EXTERNAL source edits — NOT on our own write-back. Re-seeding mints fresh
  // node ids, so the goal map (keyed by id) would match nothing and the whole
  // view would blank/flicker until the next round-trip. When the incoming
  // tacticBlock is just what the current tree already prints to (our write-back),
  // keep the existing tree (and its ids).
  const [history, setHistory] = useState<ProofTreeHistory>(() => seedHistory(tacticBlock));
  useEffect(() => {
    const currentPrinted = proofTreeToLean(history.current.root, 1, 1).source;
    const incomingPrinted = proofTreeToLean(leanTacticsToTree(tacticBlock), 1, 1).source;
    if (currentPrinted === incomingPrinted) return;
    setHistory(seedHistory(tacticBlock));
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [tacticBlock]);

  // Write-back: when a structural edit changes the printed proof, splice it into
  // the source. We compare against the printed form of the seed so cursor-only
  // moves and no-op edits don't trigger a source rewrite (which would re-seed).
  const handleHistoryChange = (h: ProofTreeHistory) => {
    setHistory(h);
    if (!onProofChange) return;
    // Compare via the analysis printer (stable canonical form) to detect real
    // structural change, but write back the SOURCE printer (no fabricated
    // trailing `sorry`s) so the user's file stays valid.
    const printed = proofTreeToLean(h.current.root, 1, 1).source;
    const seedPrinted = proofTreeToLean(leanTacticsToTree(tacticBlock), 1, 1).source;
    if (printed !== seedPrinted) onProofChange(proofTreeToSource(h.current.root, 1));
  };

  const state = history.current;
  const lean = useLeanProofGoals({
    source,
    declLine: decl.line,
    nextDeclLine,
    proof: state.root,
    cursorId: state.cursor.nodeId,
    mathlib,
    enabled: active,
  });

  // Once Lean reports each induction case's name + introduced hypotheses, bake
  // them into bullet-case inductions so the proof reprints as
  // `induction n with | zero => … | succ a a_ih => …`. This replaces Lean's
  // auto-generated INACCESSIBLE names (the `a✝` daggers) with accessible ones,
  // and the named hyps become clickable/usable. Idempotent: already-named cases
  // are left alone, so it settles after one pass (no oscillation).
  useEffect(() => {
    if (lean.goalMap.size === 0) return;
    const { root, changed } = enrichInductionCaseNames(state.root, lean.goalMap);
    if (changed) {
      handleHistoryChange(pushState(history, { root, cursor: state.cursor }));
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [lean.goalMap]);

  // Lean-backed suggestions for the cursor hole (exact?/simp?/apply?/rw?).
  const cursorNode = findNode(state.root, state.cursor.nodeId);
  const cursorIsHole = cursorNode?.tag === 'hole';
  // Only suggest at an OPEN goal — when the hole's goal is already solved
  // (cursorGoal is null), there's nothing to suggest.
  const goalOpen = active && cursorIsHole && lean.cursorGoal !== null;
  const suggest = useLeanSuggestions({
    source,
    declLine: decl.line,
    nextDeclLine,
    proof: state.root,
    cursorId: state.cursor.nodeId,
    cursorIsHole: goalOpen,
    mathlib,
    enabled: active,
  });

  const insertTactic = (tactic: string, subgoals?: number, subgoalTags?: string[]) => {
    let replacement = leanTacticsToTree(tactic);
    // A conditional rewrite (`rw [lemma]` whose lemma has premises) leaves side
    // goals — attach holes for them so they're visible as bullet branches
    // immediately, rather than surfacing later when the main goal closes.
    if (replacement.tag === 'rewrite' && !replacement.convPattern && !replacement.sideGoals) {
      const count = rewriteSideGoalCount(allDeclarations, replacement.name);
      if (count > 0) replacement = withRewriteSideGoals(replacement, count);
    }
    // A multi-subgoal opener (validation reported `subgoals`, e.g. constructor
    // on DPair → body + witness) gets one child hole PER subgoal, so every
    // obligation is a visible bullet branch immediately.
    if (
      subgoals !== undefined &&
      subgoals > 1 &&
      replacement.tag === 'apply' &&
      replacement.raw &&
      replacement.children.length === 1 &&
      replacement.children[0].tag === 'hole'
    ) {
      const children = Array.from({ length: subgoals }, () => mkHole());
      // With tags, subgoals print as `case <tag> =>` blocks in DISPLAY order
      // (witness before dependent body); untagged falls back to `·` bullets
      // in Lean's own order.
      replacement =
        subgoalTags && subgoalTags.length === subgoals
          ? { ...replacement, children, childTags: subgoalTags }
          : { ...replacement, children };
    }
    const newRoot = replaceNode(state.root, state.cursor.nodeId, replacement);
    const firstHole = findFirstHole(newRoot);
    handleHistoryChange(
      pushState(history, { root: newRoot, cursor: { nodeId: firstHole?.id ?? newRoot.id } }),
    );
  };

  const applySuggestion = (tactic: string, subgoals?: number, subgoalTags?: string[]) => {
    // A broad `simp [many lemmas]` → narrow to the subset that actually fired
    // (via `simp?`), so the proof reads `simp [<fired>]`. Insert immediately so
    // the UI is responsive; the narrowed form replaces it when the probe returns.
    const m = tactic.match(/^simp \[(.+)\]$/);
    if (m) {
      const lemmas = m[1].split(',').map((s) => s.trim()).filter(Boolean);
      probeSimpFired({ source, declLine: decl.line, nextDeclLine, proof: state.root, cursorId: state.cursor.nodeId, lemmas, mathlib })
        .then((fired) => {
          insertTactic(fired && fired.length ? `simp [${fired.join(', ')}]` : tactic);
        })
        .catch(() => insertTactic(tactic));
      return;
    }
    insertTactic(tactic, subgoals, subgoalTags);
  };

  // Build the clickable interactive goal + a map of subterm id → its text.
  const interactiveGoal = useMemo(
    () => (lean.cursorGoal ? taggedToInteractiveGoal(lean.cursorGoal.targetTagged) : null),
    [lean.cursorGoal],
  );
  const subtermTexts = useMemo(
    () => (lean.cursorGoal ? subtermTextMap(lean.cursorGoal.targetTagged) : new Map<string, string>()),
    [lean.cursorGoal],
  );
  const [selectedPath, setSelectedPath] = useState<string | null>(null);
  const [hoveredSuggestion, setHoveredSuggestion] = useState<string | null>(null);

  // ── hypothesis "use" flow: the REAL TT interaction, on Lean ───────────────
  // The user clicks a hypothesis in the GoalPanel's CONTEXT list (the real TT
  // gesture); the panel supplies the validated action tray
  // (Exact/Apply/Destructure/Use <field>) via hypSuggestionsOverride, routes
  // applies via onApplySuggestionOverride, and backs the REAL TermBuilderView
  // through termBuilderProvider (Lean probes instead of kernel metas).
  const [selectedHypName, setSelectedHypName] = useState<string | null>(null);
  const hypNames = useMemo(
    () => (lean.cursorGoal?.hyps ?? []).flatMap((h) => h.names),
    [lean.cursorGoal],
  );
  /** Hypotheses with plain type text (for slot suggestions / projections). */
  const hypsWithTypes = useMemo(
    () =>
      (lean.cursorGoal?.hyps ?? []).flatMap((h) =>
        h.names.map((name) => ({ name, type: taggedText(h.type) })),
      ),
    [lean.cursorGoal],
  );
  useEffect(() => {
    setSelectedHypName(null);
  }, [lean.cursorGoal]);

  // Probe: analyze `have leanuiProbe := <expr>` at the cursor hole and read the
  // probe binder's remaining FUNCTION type — its Pi binders are the open slots.
  const probeUse = async (
    expr: string,
  ): Promise<{ slots: TermSlot[]; returnType: string } | { error: string }> => {
    try {
      const sub = leanTacticsToTree(`have ${PROBE_NAME} := ${expr}`);
      const applied = replaceNode(state.root, state.cursor.nodeId, sub);
      const assembled = assembleProofInSource({ source, decl: { line: decl.line }, nextDeclLine, proof: applied });
      const tacLine = assembled.lean.nodeRanges.get(sub.id)?.startLine;
      const data = await analyzeRequest({
        source: assembled.source,
        prefix: assembled.prefixSource,
        body: assembled.bodySource,
        mathlib,
        priority: true,
      });
      if (!data) return { error: 'analyze request failed' };
      const err = (data.messages ?? []).find(
        (m: { severity: string; startLine: number }) => m.severity === 'error' && m.startLine === tacLine,
      );
      if (err) return { error: String(err.text).split('\n')[0] };
      const hole = findFirstHole(sub);
      const range = hole ? assembled.lean.nodeRanges.get(hole.id) : undefined;
      const g = range
        ? data.goals.find((x: { startLine: number; startCol: number }) => x.startLine === range.startLine && x.startCol === range.startCol)
        : undefined;
      const hyp = g?.goals?.[0]?.hyps?.find((h: { names: string[] }) => h.names.includes(PROBE_NAME));
      if (!hyp) return { error: 'could not read the built term' };
      return parseSlots(taggedText(hyp.type));
    } catch (e) {
      return { error: e instanceof Error ? e.message : String(e) };
    }
  };

  /** Build a TermBuilderDisplay from probed slots + current fill values. */
  const displayFrom = (
    fn: string,
    baseSlots: TermSlot[],
    returnType: string,
    values: Array<string | null>,
  ): TermBuilderDisplay => {
    const slots = baseSlots.map((sl, i) => ({
      index: i,
      name: sl.name ?? `arg${i + 1}`,
      typeLatex: mathTextToLatex(sl.type),
      typePlain: sl.type,
      implicit: false,
      value: values[i] ?? null,
      sourceExpr: values[i] ?? undefined,
      valueLatex: values[i] ? mathTextToLatex(values[i]!) : undefined,
    }));
    const slotSuggestions = new Map<number, string[]>(
      slots.map((sl, i) => [i, sl.value === null ? slotSuggestionNames(sl.typePlain ?? '', hypsWithTypes) : []]),
    );
    return { fnDisplayName: fn, slots, slotSuggestions, returnTypeLatex: mathTextToLatex(returnType) };
  };

  /** Values array from a display (sourceExpr for filled, null for holes). */
  const valuesOf = (d: TermBuilderDisplay): Array<string | null> =>
    d.slots.map((sl) => (sl.value !== null && sl.sourceExpr ? sl.sourceExpr : null));

  // The REAL TermBuilderView's engine, Lean-backed. The have's expression
  // updates live on every fill (unfilled slots print as `?_` — Lean goals).
  const termBuilderProvider: TermBuilderProvider = {
    open: async (haveExpr: string) => {
      const { fn, values } = parseApplied(haveExpr);
      if (!fn) return null;
      const r = await probeUse(fn);
      if ('error' in r) return null;
      const padded = r.slots.map((_, i) => values[i] ?? null);
      return displayFrom(fn, r.slots, r.returnType, padded);
    },
    fill: async (display, slotIndex, sourceExpr) => {
      const fn = display.fnDisplayName;
      const values = valuesOf(display);
      values[slotIndex] = sourceExpr;
      let expr = appliedExprWithHoles(fn, values);
      // Validate the whole application with this fill in place.
      let check = await probeUse(expr);
      if ('error' in check) {
        // Typed Greek (ε) against an ASCII-named hypothesis (eps)? Resolve
        // against the context and retry once.
        const resolved = resolveGreekToHypNames(sourceExpr, hypNames);
        if (resolved) {
          const retryValues = [...values];
          retryValues[slotIndex] = resolved;
          const retryExpr = appliedExprWithHoles(fn, retryValues);
          const retry = await probeUse(retryExpr);
          if (!('error' in retry)) {
            values[slotIndex] = resolved;
            sourceExpr = resolved;
            expr = retryExpr;
            check = retry;
          }
        }
      }
      if ('error' in check) {
        const slots = display.slots.map((sl, i) =>
          i === slotIndex ? { ...sl, error: check.error } : sl,
        );
        return { display: { ...display, slots }, expr: appliedExprWithHoles(fn, valuesOf(display)) };
      }
      // Specialize remaining slot types when the fill state is a pure prefix
      // (the common flow): probe the applied prefix and re-derive the rest.
      const firstHole = values.findIndex((v) => v === null);
      const isPrefix = firstHole === -1 || values.slice(firstHole).every((v) => v === null);
      let baseSlots: TermSlot[] = display.slots.map((sl) => ({ name: sl.name, type: sl.typePlain ?? '' }));
      let returnPlain = '';
      if (isPrefix) {
        const prefixExpr = appliedExpr(fn, values.filter((v): v is string => v !== null));
        const spec = await probeUse(prefixExpr);
        if (!('error' in spec)) {
          const filledCount = firstHole === -1 ? values.length : firstHole;
          baseSlots = [
            ...baseSlots.slice(0, filledCount),
            ...spec.slots,
          ].slice(0, values.length);
          returnPlain = spec.returnType;
        }
      }
      const d = displayFrom(fn, baseSlots, returnPlain, values);
      return { display: d, expr };
    },
    clear: async (display, slotIndex) => {
      const fn = display.fnDisplayName;
      const values = valuesOf(display);
      values[slotIndex] = null;
      const baseSlots: TermSlot[] = display.slots.map((sl) => ({ name: sl.name, type: sl.typePlain ?? '' }));
      const d = displayFrom(fn, baseSlots, '', values);
      return { display: d, expr: appliedExprWithHoles(fn, values) };
    },
    // TT's hoist: eject an unfilled slot's obligation into `have hN : <type>`
    // (with its own proof subtree) above, and fill the slot with hN. Sync —
    // correct by construction; the goal round-trip validates it.
    hoist: (display, slotIndex) => {
      const slot = display.slots[slotIndex];
      if (!slot || slot.value !== null || !slot.typePlain) return null;
      // TT naming: h<slotName>, falling back to the index for defaulted names.
      const base = /^arg\d+$/.test(slot.name) ? `${slotIndex}` : slot.name;
      let haveName = `h${base}`;
      if (hypNames.includes(haveName)) haveName = freshHypName(hypNames);
      const values = valuesOf(display);
      values[slotIndex] = haveName;
      const slots = display.slots.map((sl, i) =>
        i === slotIndex
          ? { ...sl, value: haveName, sourceExpr: haveName, valueLatex: mathTextToLatex(haveName), error: undefined }
          : sl,
      );
      const suggestions = new Map(display.slotSuggestions);
      suggestions.set(slotIndex, []);
      return {
        display: { ...display, slots, slotSuggestions: suggestions },
        expr: appliedExprWithHoles(display.fnDisplayName, values),
        haveName,
        haveTypeExpr: slot.typePlain,
      };
    },
  };

  // Candidate tactics to VALIDATE before showing ("try before suggest"):
  // 1. the file's rewrite lemmas (core-Lean stand-in for rw?), ranked by overlap
  //    with the goal and capped — each trialed via `rw [lemma]`;
  // 2. subterm/goal heuristics — `exact .refl` on an equality goal, and
  //    induction/cases on a clicked variable.
  // Each is trialed at the hole; only the ones that actually APPLY are surfaced.
  const goalText = lean.cursorGoal?.plain ?? '';
  const selectedSubtermText = selectedPath ? (subtermTexts.get(selectedPath) ?? '').trim() : '';
  // Rank against the SELECTED subterm when there is one (so lemmas about it
  // surface first), else the whole goal.
  const scopeText = selectedSubtermText || goalText;
  // Local equality HYPOTHESES are rewrite candidates too (esp. the induction
  // hypothesis, e.g. `rw [a_ih]`) — and usually the most relevant, so list them
  // before the file lemmas.
  const hypEqNames = useMemo(() => {
    const out: string[] = [];
    for (const h of lean.cursorGoal?.hyps ?? []) {
      if (/\s=\s/.test(taggedText(h.type))) out.push(...h.names);
    }
    return out;
  }, [lean.cursorGoal]);
  const rewriteCandidates = useMemo(() => {
    const fileLemmas = rankByGoalOverlap(equalityLemmas(allDeclarations, decl.name), scopeText, 10).map((c) => c.name);
    const names = [...hypEqNames, ...fileLemmas];
    const out: LeanSuggestion[] = [];
    for (const name of names) {
      // When a subterm is selected, prefer a subterm-SCOPED rewrite
      // (`conv in (sub) => rw [..]`); list it first so it wins dedup. Always also
      // offer the whole-goal form as a fallback (e.g. lemmas with side goals
      // can't run inside conv).
      if (selectedSubtermText) {
        out.push({ id: `lean-convrw:${name}`, label: `rw [${name}]`, tactic: `conv in (${selectedSubtermText}) => rw [${name}]`, kind: 'rw' });
      }
      out.push({ id: `lean-rw:${name}`, label: `rw [${name}]`, tactic: `rw [${name}]`, kind: 'rw' });
    }
    return out;
  }, [allDeclarations, decl.name, scopeText, selectedSubtermText, hypEqNames]);
  // When a subterm is selected, also offer `unfold <def>` for the file's
  // definitions (e.g. selecting ∑… → `unfold sum`, which unblocks the sum
  // lemmas). Validated like everything else; only shown on selection to keep
  // the default view uncluttered and bound the trial count.
  const unfoldCandidates = useMemo(
    () =>
      selectedSubtermText
        ? unfoldableDefs(allDeclarations, decl.name, 12).map(
            (name): LeanSuggestion => ({ id: `lean-unfold:${name}`, label: `unfold ${name}`, tactic: `unfold ${name}`, kind: 'unfold' }),
          )
        : [],
    [allDeclarations, decl.name, selectedSubtermText],
  );
  const heuristicCandidates = useMemo(() => {
    const subterm = selectedPath ? targetedSuggestions(subtermTexts.get(selectedPath) ?? '') : [];
    const goalLevel = lean.cursorGoal ? targetedSuggestions(lean.cursorGoal.plain) : [];
    const seen = new Set<string>();
    return [...subterm, ...goalLevel].filter((s) => (seen.has(s.id) ? false : (seen.add(s.id), true)));
  }, [selectedPath, subtermTexts, lean.cursorGoal]);
  // A poor-man's ring solver: `simp` with all the file's equality lemmas
  // (distrib/comm/assoc/…). Validated → only shows when it closes the goal, as a
  // one-click "Solve Goal". (The custom MyNat isn't a Mathlib ring, so `ring`
  // itself is unavailable; this fills that gap from the preset's own lemmas.)
  const ringCandidate = useMemo(() => {
    const names = equalityLemmas(allDeclarations, decl.name).map((c) => c.name);
    return names.length ? [{ id: 'lean-simp-ring', label: 'simp [ring lemmas]', tactic: `simp [${names.join(', ')}]`, kind: 'simp' as const }] : [];
  }, [allDeclarations, decl.name]);
  // Always try `constructor` — it unifies the goal with its inductive type's
  // constructors. Generic (no domain names); validated, so it only shows when
  // it applies. Closing (`0 ≤ a` ↦ `Leq.LeqZero`) shows as ✓ Solve Goal;
  // non-closing opens the constructor's field as the next goal (e.g. a Limit
  // goal ↦ its eps_delta obligation — the way into an ε-δ proof).
  const constructorCandidate = useMemo(
    () => [{ id: 'lean-constructor', label: 'constructor', tactic: 'constructor', kind: 'apply' as const }],
    [],
  );
  // A clicked hypothesis contributes its own use-actions (exact/apply/cases),
  // trialed like everything else so only the applicable ones show.
  const hypActionCandidates = useMemo(() => {
    if (!selectedHypName) return [];
    const out = hypothesisSuggestions(selectedHypName);
    // Projections to USE on this hypothesis (TT's "Use <field>"): every dotted
    // declaration is a candidate, ranked by type-token overlap with the hyp;
    // validation (a `have __use := <hyp>.<field>` trial) drops non-typechecking
    // ones. Clicking opens the slot builder rather than inserting directly.
    const hypType = hypsWithTypes.find((h) => h.name === selectedHypName)?.type ?? '';
    for (const expr of projectionCandidates(selectedHypName, hypType, allDeclarations)) {
      out.push({ id: `hyp-use:${expr}`, label: `use ${expr}`, tactic: `have ${PROBE_NAME} := ${expr}`, kind: 'apply' });
    }
    return out;
  }, [selectedHypName, hypsWithTypes, allDeclarations]);
  // Dedup the combined candidate list by id. ORDER = trial priority (results
  // stream in as they validate): hypothesis actions, heuristics and
  // `constructor` are cheap and high-value (constructor is the way INTO
  // structure goals like Limit), so they go before the larger rewrite/unfold
  // batches.
  const candSeen = new Set<string>();
  const validateCandidates = [...hypActionCandidates, ...heuristicCandidates, ...constructorCandidate, ...rewriteCandidates, ...unfoldCandidates, ...ringCandidate].filter((s) =>
    candSeen.has(s.id) ? false : (candSeen.add(s.id), true),
  );
  const validated = useLeanValidatedSuggestions({
    source,
    declLine: decl.line,
    nextDeclLine,
    proof: state.root,
    cursorId: state.cursor.nodeId,
    cursorIsHole: goalOpen,
    candidates: validateCandidates,
    focusPos: selectedPath ? posForGoalId(selectedPath) : null,
    focusOriginal:
      selectedPath && lean.cursorGoal
        ? subtermLatexAtPos(lean.cursorGoal.targetTagged, posForGoalId(selectedPath) ?? '')
        : null,
    mathlib,
    enabled: active,
  });

  // The TT-style hypothesis action TRAY: built from the VALIDATED pipeline
  // results (only actions Lean accepts appear), with TT's exact labels.
  const hypTraySuggestions = useMemo<TacticSuggestion[]>(() => {
    if (!selectedHypName) return [];
    const h = selectedHypName;
    const out: TacticSuggestion[] = [];
    for (const s of validated.suggestions) {
      if (s.id === `hyp-exact:${h}`) {
        out.push({ id: s.id, label: `Exact ${h}`, labelLatex: `\\text{exact } \\textbf{${h}}`, description: `Use ${h} to close the goal` });
      } else if (s.id === `hyp-apply:${h}`) {
        out.push({ id: s.id, label: `Apply ${h}`, labelLatex: `\\text{apply } \\textbf{${h}}`, description: `Apply ${h} to the goal`, numSubgoals: s.subgoals });
      } else if (s.id === `hyp-cases:${h}`) {
        out.push({ id: s.id, label: `Destructure ${h}`, labelLatex: `\\text{cases } \\textbf{${h}}`, description: `Pattern-match on ${h}` });
      } else if (s.id.startsWith('hyp-use:')) {
        const expr = s.id.slice('hyp-use:'.length);
        if (!expr.startsWith(`${h}.`)) continue;
        const field = expr.slice(h.length + 1);
        out.push({ id: s.id, label: `Use ${field}`, labelLatex: `\\text{Use } \\textbf{${field.replace(/_/g, '\\_')}}`, description: `have h := ${expr} …` });
      }
    }
    return out;
  }, [selectedHypName, validated.suggestions]);

  // Route tray clicks: insert the validated tactic, or (Use …) create the
  // have with `?_` holes — its ✎ affordance opens the REAL TermBuilderView.
  const handleTraySuggestion = (s: TacticSuggestion): boolean => {
    const h = selectedHypName;
    if (!h) return false;
    if (s.id === `hyp-exact:${h}`) {
      insertTactic(`exact ${h}`);
      return true;
    }
    if (s.id === `hyp-apply:${h}`) {
      insertTactic(`apply ${h}`, s.numSubgoals);
      return true;
    }
    if (s.id === `hyp-cases:${h}`) {
      insertTactic(`cases ${h}\n·\n  sorry`);
      return true;
    }
    if (s.id.startsWith('hyp-use:')) {
      const expr = s.id.slice('hyp-use:'.length);
      void probeUse(expr).then((r) => {
        const n = 'error' in r ? 0 : r.slots.length;
        insertTactic(`have ${freshHypName(hypNames)} := ${appliedExprWithHoles(expr, Array(n).fill(null))}`);
      });
      return true;
    }
    return false;
  };


  // Merge validated suggestions with Lean's own discovery (exact?/simp?/apply?,
  // which Lean already vetted as applicable), deduped by LABEL. The scoped
  // `conv in (..) => rw [L]` and the whole-goal `rw [L]` share a label and
  // collapse to one: keep the scoped form's apply tactic (listed first), but
  // adopt the whole-goal form's preview (conv hides its exit goal from Lean's
  // InfoTree, so only the whole-goal trial produces a usable preview).
  const byLabel = new Map<string, LeanSuggestion>();
  for (const s of [...validated.suggestions, ...suggest.suggestions]) {
    // Hypothesis actions render in the CONTEXT tray (TT-style), not here.
    if (s.id.startsWith('hyp-')) continue;
    const existing = byLabel.get(s.label);
    if (!existing) byLabel.set(s.label, s);
    else if (!existing.preview && s.preview) byLabel.set(s.label, { ...existing, preview: s.preview });
  }
  const allSuggestions = [...byLabel.values()];
  const anyLoading = suggest.loading || validated.loading;

  const suggestionPills =
    goalOpen && (allSuggestions.length > 0 || anyLoading) ? (
      <div style={{ marginTop: 8 }}>
        <div style={{ fontSize: 10, color: C.faint, marginBottom: 4, display: 'flex', gap: 8 }}>
          <span>SUGGESTIONS</span>
          {selectedPath && subtermTexts.get(selectedPath) && (
            <span style={{ color: C.label }}>for {subtermTexts.get(selectedPath)}</span>
          )}
          {anyLoading && <span style={{ color: C.label }}>searching…</span>}
        </div>
        <div style={{ display: 'flex', flexWrap: 'wrap', gap: 6 }}>
          {allSuggestions.map((s) => {
            // Closers show a green "Solve Goal"; otherwise, when there's a
            // focus-transform preview, the result shows PROMINENTLY — both with
            // the tactic name subtle beneath.
            const topLine = s.closes || !!s.preview;
            return (
              <button
                key={s.id}
                onClick={() => applySuggestion(s.tactic, s.subgoals, s.subgoalTags)}
                onMouseEnter={() => setHoveredSuggestion(s.id)}
                onMouseLeave={() => setHoveredSuggestion((h) => (h === s.id ? null : h))}
                title={s.tactic}
                style={{
                  display: 'flex',
                  flexDirection: 'column',
                  alignItems: 'flex-start',
                  gap: 1,
                  fontFamily: mono,
                  fontSize: 11,
                  color: C.text,
                  background: hoveredSuggestion === s.id ? C.header : C.bg,
                  border: `1px solid ${s.closes ? C.green : hoveredSuggestion === s.id ? C.blue : C.border}`,
                  borderRadius: 4,
                  padding: topLine ? '3px 8px' : '2px 8px',
                  cursor: 'pointer',
                  maxWidth: '100%',
                }}
              >
                {s.closes ? (
                  <span style={{ color: C.green, fontSize: 12, fontWeight: 600 }}>✓ Solve Goal</span>
                ) : s.preview ? (
                  <span style={{ fontSize: 14, lineHeight: 1.2 }}>
                    <PreviewMath latex={s.preview} />
                  </span>
                ) : null}
                <span style={{ color: topLine ? C.faint : C.text, fontSize: topLine ? 10 : 11 }}>{s.label}</span>
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
    goalOpen && lean.loading ? (
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
        {lean.loading && <span style={{ color: C.label }}>checking…</span>}
        {lean.error && <span style={{ color: '#f85149' }}>⚠ {lean.error.slice(0, 60)}</span>}
      </div>
      <ProofTreeEditor
        history={history}
        onHistoryChange={handleHistoryChange}
        goalMapOverride={lean.goalMap}
        typedContextOverride={lean.typedContext}
        interactiveGoalOverride={interactiveGoal}
        onGoalPathSelect={setSelectedPath}
        goalExtraSlot={suggestionSlot}
        applySubgoalCount={(name) => applySubgoalCount(allDeclarations, name)}
        rewriteSideGoalCount={(name) => rewriteSideGoalCount(allDeclarations, name)}
        hypSuggestionsOverride={hypTraySuggestions}
        onHypothesisSelect={setSelectedHypName}
        onApplySuggestionOverride={handleTraySuggestion}
        termBuilderProvider={termBuilderProvider}
      />
    </div>
  );
}

function seedHistory(tacticBlock: string): ProofTreeHistory {
  const root = leanTacticsToTree(tacticBlock);
  const firstHole = findFirstHole(root);
  return createHistory({ root, cursor: { nodeId: firstHole?.id ?? root.id } });
}
