import { useEffect, useMemo, useState } from 'react';
import type { LeanDeclaration, LeanGoal } from '../lean/types';
import { declKey } from '../lean/declProofSteps';
import { LeanMathView } from './LeanMathView';
import { LeanMathEditor } from './LeanMathEditor';
import { ProofTreeEditor } from './ProofTreeEditor';
import {
  createHistory,
  type ProofTreeHistory,
} from '../proof-tree/proof-tree';
import { findFirstHole } from '../proof-tree/tactic-to-tree';
import { leanTacticsToTree } from '../lean/leanTacticsToTree';
import { extractTacticBlock } from '../lean/extractTacticBlock';
import { useLeanProofGoals } from '../lean/useLeanProofGoals';

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
}: {
  declarations: LeanDeclaration[];
  goals: LeanGoal[];
  source: string;
  mathlib?: boolean;
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
            tacticBlock={extractTacticBlock(source, d, nextLineOf(d.line))}
            mathlib={mathlib}
          />
        ))}
      </div>
    </div>
  );
}

function DeclCard({
  decl,
  tacticBlock,
  mathlib,
}: {
  decl: LeanDeclaration;
  tacticBlock: string | null;
  mathlib?: boolean;
}) {
  const [editing, setEditing] = useState(false);
  const isProof = decl.kind === 'theorem' && tacticBlock !== null;

  return (
    <div
      style={{
        marginBottom: 12,
        border: `1px solid ${C.border}`,
        borderRadius: 6,
        overflow: 'hidden',
        backgroundColor: C.panel,
      }}
    >
      <div
        style={{
          display: 'flex',
          alignItems: 'center',
          gap: 8,
          padding: '6px 10px',
          backgroundColor: C.header,
          borderBottom: `1px solid ${C.border}`,
        }}
      >
        <span
          style={{
            fontSize: 11,
            fontWeight: 600,
            color: KIND_COLOR[decl.kind],
            textTransform: 'uppercase',
            letterSpacing: '0.04em',
          }}
        >
          {decl.kind}
        </span>
        <span style={{ flex: 1, fontFamily: mono, fontSize: 13, fontWeight: 500, color: '#e6edf3' }}>{decl.name}</span>
        <button
          onClick={() => setEditing((e) => !e)}
          style={{
            background: 'none',
            border: `1px solid ${C.border}`,
            borderRadius: 4,
            cursor: 'pointer',
            color: editing ? C.green : C.label,
            fontSize: 11,
            padding: '2px 8px',
          }}
        >
          {editing ? 'done' : 'edit'}
        </button>
      </div>

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
        {decl.valueTagged !== undefined && (
          <div style={{ fontSize: 15, lineHeight: 1.6, marginTop: 4 }}>
            <span style={{ color: C.label }}>:= </span>
            {editing ? (
              <LeanMathEditor tagged={decl.valueTagged} />
            ) : (
              <LeanMathView tagged={decl.valueTagged} fallback={decl.prettyValue ?? ''} />
            )}
          </div>
        )}
      </div>

      {/* Structured proof editor (the REAL ProofTreeEditor, goals from Lean) */}
      {isProof && (
        <LeanProofEditor decl={decl} tacticBlock={tacticBlock} mathlib={mathlib} />
      )}
    </div>
  );
}

function LeanProofEditor({
  decl,
  tacticBlock,
  mathlib,
}: {
  decl: LeanDeclaration;
  tacticBlock: string;
  mathlib?: boolean;
}) {
  // Seed the proof tree from the user's actual Lean proof. Re-seed if the source
  // proof changes (keyed by name + block).
  const [history, setHistory] = useState<ProofTreeHistory>(() => seedHistory(tacticBlock));
  useEffect(() => {
    setHistory(seedHistory(tacticBlock));
  }, [tacticBlock]);

  const state = history.current;
  const lean = useLeanProofGoals({
    name: decl.name,
    typeSource: decl.prettyType,
    proof: state.root,
    cursorId: state.cursor.nodeId,
    mathlib,
  });

  return (
    <div style={{ padding: '6px 10px' }}>
      <div style={{ fontSize: 10, color: C.faint, marginBottom: 4, letterSpacing: '0.03em', display: 'flex', gap: 8 }}>
        <span>PROOF</span>
        {lean.loading && <span style={{ color: C.label }}>checking…</span>}
        {lean.error && <span style={{ color: '#f85149' }}>⚠ {lean.error.slice(0, 60)}</span>}
      </div>
      <ProofTreeEditor
        history={history}
        onHistoryChange={setHistory}
        goalMapOverride={lean.goalMap}
        typedContextOverride={lean.typedContext}
      />
    </div>
  );
}

function seedHistory(tacticBlock: string): ProofTreeHistory {
  const root = leanTacticsToTree(tacticBlock);
  const firstHole = findFirstHole(root);
  return createHistory({ root, cursor: { nodeId: firstHole?.id ?? root.id } });
}
