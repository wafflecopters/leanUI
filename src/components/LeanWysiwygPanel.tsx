import { useMemo, useState } from 'react';
import type { LeanDeclaration, LeanGoal } from '../lean/types';
import { groupGoalsByDeclaration, declKey, type ProofStep } from '../lean/declProofSteps';
import { LeanMathView } from './LeanMathView';
import { LeanMathEditor } from './LeanMathEditor';

/**
 * The structured WYSIWYG editor panel — restores the original two-column layout
 * on Lean data: one card per declaration, each with an interactive math editor
 * for the type (and value, for defs) and a Proof section that shows the proof's
 * goal states as WYSIWYG math, step by step.
 *
 * Interactive proof *construction* (the old ProofTreeEditor's click-to-build
 * tactics) is M4 — it was bound to the TT tactic engine and needs an async
 * Lean-backed rebuild. This panel restores the structure and the WYSIWYG
 * display; the proof steps are read from Lean's tactic goal states.
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
  goals,
}: {
  declarations: LeanDeclaration[];
  goals: LeanGoal[];
}) {
  const stepsByDecl = useMemo(() => groupGoalsByDeclaration(declarations, goals), [declarations, goals]);

  return (
    <div style={{ height: '100%', display: 'flex', flexDirection: 'column', color: C.text }}>
      <div
        style={{
          margin: 0,
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
          <DeclCard key={declKey(d)} decl={d} steps={stepsByDecl.get(declKey(d)) ?? []} />
        ))}
      </div>
    </div>
  );
}

function DeclCard({ decl, steps }: { decl: LeanDeclaration; steps: ProofStep[] }) {
  const [editing, setEditing] = useState(false);
  const isProof = decl.kind === 'theorem';

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
      {/* Header */}
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
          title={editing ? 'Done editing' : 'Edit structurally'}
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
      <div style={{ padding: '8px 10px', borderBottom: steps.length ? `1px solid ${C.border}` : 'none' }}>
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

      {/* Proof steps (theorems) */}
      {isProof && steps.length > 0 && <ProofSteps steps={steps} />}
    </div>
  );
}

function ProofSteps({ steps }: { steps: ProofStep[] }) {
  return (
    <div style={{ padding: '8px 10px' }}>
      <div style={{ fontSize: 10, color: C.faint, marginBottom: 6, letterSpacing: '0.03em' }}>PROOF</div>
      {steps.map((step, i) => {
        const state = step.goal.goals[0];
        return (
          <div key={i} style={{ marginBottom: 8, paddingLeft: 8, borderLeft: `2px solid ${C.border}` }}>
            <div style={{ fontSize: 10, color: C.faint, marginBottom: 2 }}>
              step {i + 1} · line {step.startLine}
              {state?.case ? ` · case ${state.case}` : ''}
            </div>
            {!state && <span style={{ color: C.green, fontSize: 12 }}>goals solved</span>}
            {state && (
              <div style={{ fontSize: 13.5, lineHeight: 1.5 }}>
                {state.hyps.map((h, hi) => (
                  <div key={hi}>
                    <span style={{ fontFamily: mono, color: C.purple }}>{h.names.join(' ')}</span>
                    <span style={{ color: C.label }}> : </span>
                    <LeanMathView tagged={h.type} />
                  </div>
                ))}
                <div style={{ display: 'flex', gap: 6, marginTop: state.hyps.length ? 2 : 0 }}>
                  <span style={{ color: C.green }}>⊢</span>
                  <LeanMathView tagged={state.targetTagged} fallback={state.plain} />
                </div>
              </div>
            )}
          </div>
        );
      })}
    </div>
  );
}
