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
  replaceNode,
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
import { equalityLemmas, rankByGoalOverlap, unfoldableDefs } from '../lean/rewriteCandidates';
import { taggedToInteractiveGoal, subtermTextMap, taggedText, posForGoalId } from '../lean/leanInteractiveGoal';
import { targetedSuggestions, type LeanSuggestion } from '../lean/leanSuggestions';
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
}: {
  declarations: LeanDeclaration[];
  goals: LeanGoal[];
  source: string;
  mathlib?: boolean;
  /** Write-back: structural proof edits reprint + splice into the source. */
  onSourceChange?: (next: string) => void;
}) {
  // Declaration start lines (sorted) to bound each declaration's source slice.
  const sortedLines = useMemo(
    () => [...declarations].map((d) => d.line).sort((a, b) => a - b),
    [declarations],
  );
  const nextLineOf = (line: number): number | undefined => sortedLines.find((l) => l > line);

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
  onProofChange,
}: {
  decl: LeanDeclaration;
  allDeclarations: LeanDeclaration[];
  source: string;
  nextDeclLine?: number;
  tacticBlock: string | null;
  mathlib?: boolean;
  onProofChange?: (newBlock: string) => void;
}) {
  const [editing, setEditing] = useState(false);
  const [expanded, setExpanded] = useState(false);
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
      {/* Type (+ value for defs) */}
      <div style={{ padding: '8px 10px', borderBottom: isProof ? `1px solid ${C.border}` : 'none' }}>
        <div style={{ fontSize: 15, lineHeight: 1.6 }}>
          <span style={{ color: C.label }}>: </span>
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
    <div style={{ marginBottom: 12, border: `1px solid ${C.border}`, borderRadius: 6, overflow: 'hidden', backgroundColor: C.panel }}>
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
  onProofChange,
}: {
  decl: LeanDeclaration;
  allDeclarations: LeanDeclaration[];
  source: string;
  nextDeclLine?: number;
  tacticBlock: string;
  mathlib?: boolean;
  onProofChange?: (newBlock: string) => void;
}) {
  // Seed the proof tree from the user's actual Lean proof. Re-seed if the source
  // proof changes (keyed by the block text).
  const [history, setHistory] = useState<ProofTreeHistory>(() => seedHistory(tacticBlock));
  useEffect(() => {
    setHistory(seedHistory(tacticBlock));
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
  const suggest = useLeanSuggestions({
    source,
    declLine: decl.line,
    nextDeclLine,
    proof: state.root,
    cursorId: state.cursor.nodeId,
    cursorIsHole,
    mathlib,
  });

  const applySuggestion = (tactic: string) => {
    const replacement = leanTacticsToTree(tactic);
    const newRoot = replaceNode(state.root, state.cursor.nodeId, replacement);
    const firstHole = findFirstHole(newRoot);
    handleHistoryChange(
      pushState(history, { root: newRoot, cursor: { nodeId: firstHole?.id ?? newRoot.id } }),
    );
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
  // Dedup the combined candidate list by id.
  const candSeen = new Set<string>();
  const validateCandidates = [...heuristicCandidates, ...rewriteCandidates, ...unfoldCandidates, ...ringCandidate].filter((s) =>
    candSeen.has(s.id) ? false : (candSeen.add(s.id), true),
  );
  const validated = useLeanValidatedSuggestions({
    source,
    declLine: decl.line,
    nextDeclLine,
    proof: state.root,
    cursorId: state.cursor.nodeId,
    cursorIsHole,
    candidates: validateCandidates,
    focusPos: selectedPath ? posForGoalId(selectedPath) : null,
    mathlib,
  });

  // Merge validated suggestions with Lean's own discovery (exact?/simp?/apply?,
  // which Lean already vetted as applicable), deduped by LABEL. The scoped
  // `conv in (..) => rw [L]` and the whole-goal `rw [L]` share a label and
  // collapse to one: keep the scoped form's apply tactic (listed first), but
  // adopt the whole-goal form's preview (conv hides its exit goal from Lean's
  // InfoTree, so only the whole-goal trial produces a usable preview).
  const byLabel = new Map<string, LeanSuggestion>();
  for (const s of [...validated.suggestions, ...suggest.suggestions]) {
    const existing = byLabel.get(s.label);
    if (!existing) byLabel.set(s.label, s);
    else if (!existing.preview && s.preview) byLabel.set(s.label, { ...existing, preview: s.preview });
  }
  const allSuggestions = [...byLabel.values()];
  const anyLoading = suggest.loading || validated.loading;

  const suggestionSlot =
    cursorIsHole && (allSuggestions.length > 0 || anyLoading) ? (
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
                onClick={() => applySuggestion(s.tactic)}
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
      />
    </div>
  );
}

function seedHistory(tacticBlock: string): ProofTreeHistory {
  const root = leanTacticsToTree(tacticBlock);
  const firstHole = findFirstHole(root);
  return createHistory({ root, cursor: { nodeId: firstHole?.id ?? root.id } });
}
