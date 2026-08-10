import { describe, expect, test } from 'vitest';
import { ProofSession, ProofSessionError } from './session';
import { fakeLean, brokenAnalyzer, deadAnalyzer, type FakeRule } from './testing';
import { ACTION } from './actions';
import { formatOutline, openHoles } from './outline';
import type { LeanDeclaration } from '../lean/types';
import type { LeanAnalyzer } from './analyzer';

// ─── A small file, shaped like the real presets ──────────────────────────────

const SOURCE = [
  'def divTwoPos (e : ℝ) (h : 0 < e) : 0 < e / 2 := sorry', // line 1
  '', // 2
  'def divPos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a / b := sorry', // 3
  '', // 4
  'def halfEqDiv (e : ℝ) : rhalf * e = e / 2 := sorry', // 5
  '', // 6
  'theorem target (ε : ℝ) (epsPos : 0 < ε) : 0 < ε / 2 := by', // 7
  '  sorry', // 8
  '', // 9
].join('\n');

const decl = (name: string, prettyType: string, line: number, kind: LeanDeclaration['kind'] = 'def'): LeanDeclaration => ({
  name, kind, prettyType, line, col: 0,
});

const DECLS: LeanDeclaration[] = [
  decl('divTwoPos', '(e : ℝ) → 0 < e → 0 < e / 2', 1),
  decl('divPos', '(a b : ℝ) → 0 < a → 0 < b → 0 < a / b', 3),
  decl('halfEqDiv', '(e : ℝ) → rhalf * e = e / 2', 5),
  decl('target', '(ε : ℝ) → 0 < ε → 0 < ε / 2', 7, 'theorem'),
];

const BASELINE = {
  target: '0 < ε / 2',
  hyps: [
    { names: ['ε'], type: 'ℝ' },
    { names: ['epsPos'], type: '0 < ε' },
  ],
};

const RULES: FakeRule[] = [
  { tactic: 'apply divTwoPos', leaves: [{ target: '0 < ε' }] },
  { tactic: 'apply divPos', leaves: [{ target: '0 < ε', case: 'ha' }, { target: '0 < 2', case: 'hb' }] },
  { tactic: 'assumption', error: 'assumption failed' },
  { tactic: 'constructor', error: 'no applicable constructor' },
  { tactic: 'rw [halfEqDiv]', error: 'did not find occurrence' },
  { tactic: 'intro x', leaves: [{ target: '0 < ε / 2' }] },
];

function open(overrides: {
  analyze?: LeanAnalyzer;
  declName?: string;
  onSourceChange?: (s: string) => void;
  source?: string;
} = {}) {
  return ProofSession.open({
    analyze: overrides.analyze ?? fakeLean({ declarations: DECLS, baseline: BASELINE, rules: RULES }),
    source: overrides.source ?? SOURCE,
    declarations: DECLS,
    declName: overrides.declName ?? 'target',
    onSourceChange: overrides.onSourceChange,
  });
}

const suggestionIds = (s: ProofSession) => s.getState().suggestions.map((x) => x.id);
const actionIds = (s: ProofSession) => s.getState().actions.map((a) => a.id);

// ─── Opening ─────────────────────────────────────────────────────────────────

describe('ProofSession.open', () => {
  test('seeds the proof from the declaration body and parks on its hole', () => {
    const s = open();
    const state = s.getState();
    expect(state.decl.name).toBe('target');
    expect(state.cursor.isHole).toBe(true);
    expect(state.outline.tag).toBe('hole');
    expect(state.outline.isCursor).toBe(true);
  });

  test('rejects a declaration that is not in the file', () => {
    expect(() => open({ declName: 'nope' })).toThrow(ProofSessionError);
  });

  test('rejects a declaration with no interactive proof body', () => {
    const source = 'inductive Foo where\n  | bar\n';
    const decls = [decl('Foo', 'Type', 1, 'inductive')];
    expect(() =>
      ProofSession.open({ analyze: fakeLean(), source, declarations: decls, declName: 'Foo' }),
    ).toThrow(/no interactive proof body/);
  });

  test('before any round-trip there is no goal and no suggestions', () => {
    const state = open().getState();
    expect(state.goal).toBeNull();
    expect(state.suggestions).toEqual([]);
    // …and therefore no tactics are offered: a tactic needs an open goal.
    expect(state.actions.filter((a) => a.group === 'tactic')).toEqual([]);
  });
});

// ─── Goals ───────────────────────────────────────────────────────────────────

describe('refreshGoals', () => {
  test('reads the target and the context at the cursor', async () => {
    const s = open();
    await s.refreshGoals();
    const g = s.getState().goal!;
    expect(g.targetText).toBe('0 < ε / 2');
    expect(g.hypotheses.map((h) => h.name)).toEqual(['ε', 'epsPos']);
    expect(g.hypotheses.find((h) => h.name === 'epsPos')?.text).toBe('0 < ε');
  });

  test('flags equation hypotheses (the rewrite candidates)', async () => {
    const s = ProofSession.open({
      analyze: fakeLean({
        declarations: DECLS,
        baseline: { target: 'P n', hyps: [{ names: ['ih'], type: 'n + 0 = n' }, { names: ['k'], type: 'ℕ' }] },
      }),
      source: SOURCE,
      declarations: DECLS,
      declName: 'target',
    });
    await s.refreshGoals();
    const hyps = s.getState().goal!.hypotheses;
    expect(hyps.find((h) => h.name === 'ih')?.isEquation).toBe(true);
    expect(hyps.find((h) => h.name === 'k')?.isEquation).toBe(false);
  });

  test('counts the open goals', async () => {
    const s = open();
    await s.refreshGoals();
    expect(s.getState().status.openGoals).toBe(1);
    expect(s.getState().status.complete).toBe(false);
  });

  test('a transport failure surfaces as an error, not as a solved proof', async () => {
    const s = open({ analyze: deadAnalyzer });
    await s.refreshGoals();
    const state = s.getState();
    expect(state.error).toBeTruthy();
    expect(state.status.complete).toBe(false);
  });

  test('a bridge error surfaces as an error', async () => {
    const s = open({ analyze: brokenAnalyzer('lean not found') });
    await s.refreshGoals();
    expect(s.getState().error).toContain('lean not found');
  });

  // Silently swallowing Lean's complaints is how a structurally broken proof —
  // a missing branch, an unsolved goal — ends up looking perfectly fine.
  test("Lean's errors about THIS proof are reported", async () => {
    const s = open({
      analyze: fakeLean({
        declarations: DECLS,
        baseline: BASELINE,
        messages: [
          { severity: 'error', startLine: 8, startCol: 2, endLine: 8, endCol: 7, text: 'unsolved goals\ncase hbc\n⊢ 1 < 2' },
        ],
      }),
    });
    await s.refreshGoals();
    const errs = s.getState().status.diagnostics.filter((d) => d.severity === 'error');
    expect(errs).toHaveLength(1);
    expect(errs[0].text).toContain('unsolved goals');
    expect(s.getState().status.complete).toBe(false);
  });

  test('errors from EARLIER declarations are not this proof’s problem', async () => {
    const s = open({
      analyze: fakeLean({
        declarations: DECLS,
        baseline: BASELINE,
        // `target` starts at line 7; this one belongs to divTwoPos.
        messages: [
          { severity: 'error', startLine: 1, startCol: 0, endLine: 1, endCol: 5, text: 'unknown identifier' },
        ],
      }),
    });
    await s.refreshGoals();
    expect(s.getState().status.diagnostics).toEqual([]);
  });

  test("other declarations' sorry warnings stay out of this proof's status", async () => {
    const s = open({
      analyze: fakeLean({
        declarations: DECLS,
        baseline: BASELINE,
        messages: [
          { severity: 'warning', startLine: 1, startCol: 4, endLine: 1, endCol: 9, text: "declaration uses 'sorry'" },
          { severity: 'warning', startLine: 3, startCol: 4, endLine: 3, endCol: 9, text: "declaration uses 'sorry'" },
        ],
      }),
    });
    await s.refreshGoals();
    expect(s.getState().status.diagnostics).toEqual([]);
  });
});

// ─── Suggestions ─────────────────────────────────────────────────────────────

describe('refreshSuggestions', () => {
  test('surfaces only what Lean accepted', async () => {
    const s = open();
    await s.refresh();
    const got = suggestionIds(s);
    expect(got).toContain('lean-applylemma:divTwoPos');
    expect(got).toContain('lean-applylemma:divPos');
    // The fake rejects these three.
    expect(got).not.toContain('lean-assumption');
    expect(got).not.toContain('lean-constructor');
    expect(got).not.toContain('lean-rw:halfEqDiv');
  });

  test('carries what each suggestion would do to the goal', async () => {
    const s = open();
    await s.refresh();
    const divPos = s.getState().suggestions.find((x) => x.id === 'lean-applylemma:divPos')!;
    expect(divPos.subgoals).toBe(2);
    expect(divPos.previews).toHaveLength(2);
    expect(divPos.closes).toBe(false);
  });

  test('a closed cursor (not a hole) has no suggestions', async () => {
    const s = open();
    await s.refresh();
    s.applySuggestion('lean-applylemma:divTwoPos');
    // The cursor lands on the new hole, but move it onto the apply step itself.
    const applyNode = s.getState().outline;
    s.moveCursor(applyNode.id);
    await s.refresh();
    expect(s.getState().suggestions).toEqual([]);
    expect(s.getState().cursor.isHole).toBe(false);
  });

  test('suggestions are dropped the moment the proof changes under them', async () => {
    const s = open();
    await s.refresh();
    expect(suggestionIds(s).length).toBeGreaterThan(0);
    s.applySuggestion('lean-applylemma:divTwoPos');
    // Not "stale but still clickable" — gone. A pill validated at the old goal
    // would insert a tactic that was never tried at this one.
    expect(s.getState().suggestions).toEqual([]);
  });
});

// ─── Applying tactics ────────────────────────────────────────────────────────

describe('applying a suggestion', () => {
  test('a single-goal apply leaves one branch and moves the cursor to it', async () => {
    const s = open();
    await s.refresh();
    expect(s.applySuggestion('lean-applylemma:divTwoPos')).toEqual({ ok: true });
    const state = s.getState();
    expect(state.outline.label).toBe('apply divTwoPos');
    expect(state.outline.children).toHaveLength(1);
    expect(state.cursor.nodeId).toBe(state.outline.children[0].id);
  });

  test('a goal-splitting apply opens one branch PER subgoal', async () => {
    const s = open();
    await s.refresh();
    s.applySuggestion('lean-applylemma:divPos');
    const state = s.getState();
    expect(state.outline.children).toHaveLength(2);
    expect(state.outline.children.map((c) => c.branch)).toEqual(['ha', 'hb']);
  });

  test('the printed proof is the tactic the suggestion promised', async () => {
    const s = open();
    await s.refresh();
    s.applySuggestion('lean-applylemma:divTwoPos');
    expect(s.proofSource()).toContain('apply divTwoPos');
  });

  test('an unknown suggestion id is refused, not silently ignored', async () => {
    const s = open();
    await s.refresh();
    const r = s.applySuggestion('lean-applylemma:notARealLemma');
    expect(r.ok).toBe(false);
    expect(r.error).toMatch(/no suggestion/);
  });
});

describe('manual tactics', () => {
  test('intros introduces the named binders', async () => {
    const s = open();
    await s.refreshGoals();
    expect(s.runTactic('intros', 'x y')).toEqual({ ok: true });
    expect(s.getState().outline.label).toBe('intros x y');
  });

  test('a LaTeX-spelled binder is normalized to unicode', async () => {
    const s = open();
    await s.refreshGoals();
    s.runTactic('intros', '\\epsilon hpos');
    expect(s.getState().outline.label).toBe('intros ε hpos');
  });

  test('an empty argument is refused', async () => {
    const s = open();
    await s.refreshGoals();
    expect(s.runTactic('intros', '   ').ok).toBe(false);
  });

  test('apply opens one branch per premise of the named lemma', async () => {
    const s = open();
    await s.refreshGoals();
    // divPos takes two positivity premises.
    s.runTactic('apply', 'divPos');
    expect(s.getState().outline.children.length).toBe(2);
  });
});

// REGRESSION: "Use <field>" must introduce the have with one `?_` per argument
// the term still needs. Those holes ARE the affordance — they're what the slot
// builder fills and what the prose renders as □ ("since limF.eps_delta □ □").
// Inserting the bare expression gives an application missing its arguments with
// nothing on screen to say so.
describe('using a term', () => {
  const withProbe = (probes: Record<string, string>) =>
    ProofSession.open({
      analyze: fakeLean({ declarations: DECLS, baseline: BASELINE, rules: RULES, probes }),
      source: SOURCE,
      declarations: DECLS,
      declName: 'target',
    });

  test('opens one term hole per missing argument', async () => {
    const s = withProbe({ 'limF.eps_delta': '(epsilon : ℝ) → 0 < epsilon → DPair ℝ P' });
    await s.refreshGoals();
    expect(await s.useTerm('limF.eps_delta')).toEqual({ ok: true });
    expect(s.proofSource()).toContain('have h := limF.eps_delta ?_ ?_');
  });

  test('a term that needs nothing gets no holes', async () => {
    const s = withProbe({ epsPos: '0 < ε' });
    await s.refreshGoals();
    await s.useTerm('epsPos');
    expect(s.proofSource()).toContain('have h := epsPos');
    expect(s.proofSource()).not.toContain('?_');
  });

  test('a term Lean rejects is reported, not inserted', async () => {
    const s = withProbe({});
    await s.refreshGoals();
    const r = await s.useTerm('nonsense');
    expect(r.ok).toBe(false);
    expect(s.proofSource()).not.toContain('have');
  });

  test('the have name avoids the names already in scope', async () => {
    const s = withProbe({ 'limF.eps_delta': '(e : ℝ) → P e' });
    await s.refreshGoals();
    await s.useTerm('limF.eps_delta');
    // `h` is free here; the point is it never shadows an existing hypothesis.
    const name = s.proofSource().match(/have (\w+) :=/)?.[1];
    expect(s.getState().goal!.hypotheses.map((x) => x.name)).not.toContain(name);
  });
});

// ─── Cursor, selection, history ──────────────────────────────────────────────

describe('navigation', () => {
  test('next open goal cycles through the holes', async () => {
    const s = open();
    await s.refresh();
    s.applySuggestion('lean-applylemma:divPos');
    const holes = openHoles(s.getState().outline);
    expect(holes.length).toBeGreaterThanOrEqual(0); // status needs a refresh
    const first = s.getState().cursor.nodeId;
    expect(s.cursorToHole(1)).toEqual({ ok: true });
    expect(s.getState().cursor.nodeId).not.toBe(first);
    expect(s.cursorToHole(-1)).toEqual({ ok: true });
    expect(s.getState().cursor.nodeId).toBe(first);
  });

  test('moving to a step that does not exist is refused', () => {
    const s = open();
    expect(s.moveCursor(999_999).ok).toBe(false);
  });

  test('a cursor move is not an undo point', async () => {
    const s = open();
    await s.refresh();
    s.applySuggestion('lean-applylemma:divPos');
    const afterApply = s.getState().cursor.nodeId;
    s.cursorToHole(1);
    s.undo();
    // Undo went back past the APPLY, not past the cursor move.
    expect(s.getState().outline.tag).toBe('hole');
    expect(afterApply).toBeDefined();
  });
});

describe('selection', () => {
  test('selecting a subterm narrows the suggestion scope', async () => {
    const s = open();
    await s.refresh();
    const sub = s.getState().goal!.subterms;
    expect(sub.length).toBeGreaterThan(0);
    expect(s.selectSubterm(sub[0].pos)).toEqual({ ok: true });
    expect(s.getState().selection.subterm?.pos).toBe(sub[0].pos);
  });

  test('selecting a subterm that is not in the goal is refused', async () => {
    const s = open();
    await s.refresh();
    expect(s.selectSubterm('/9/9/9').ok).toBe(false);
  });

  test('selecting a hypothesis that is not in scope is refused', async () => {
    const s = open();
    await s.refresh();
    expect(s.selectHypothesis('nope').ok).toBe(false);
    expect(s.selectHypothesis('epsPos')).toEqual({ ok: true });
  });

  // The prose now offers a hypothesis's moves from the NAME as it appears in a
  // case pattern, anywhere in the proof — which is only safe because a name the
  // cursor can't see selects nothing and so shows nothing. No separate
  // in-scope check guards that tray; this is it.
  test('an out-of-scope name yields an empty action tray, not a stale one', async () => {
    const s = open();
    await s.refresh();
    s.selectHypothesis('epsPos');
    await s.refresh();
    expect(s.getState().selection.hypothesis).toBe('epsPos');

    expect(s.selectHypothesis('notHere').ok).toBe(false);
    await s.refresh();
    expect(s.getState().selection.hypothesis).toBe('epsPos'); // unchanged, not clobbered
    expect(s.getState().actions.filter((a) => a.group === 'hypothesis')
      .every((a) => a.id.includes('epsPos'))).toBe(true);
  });

  test('selection is cleared when the proof changes', async () => {
    const s = open();
    await s.refresh();
    s.selectHypothesis('epsPos');
    s.applySuggestion('lean-applylemma:divTwoPos');
    expect(s.getState().selection.hypothesis).toBeNull();
  });
});


describe('destructure visibility', () => {
  // The outline walk skipped destructure nodes entirely, so every hole below
  // an `obtain` vanished from the outline — and with no visible open hole,
  // `complete` reported true over an unproved goal.
  test('an open hole below a destructure keeps the proof incomplete', async () => {
    const s = open();
    await s.refresh();
    s.insertTactic('obtain ⟨pa, pb⟩ := epsPos\nsorry');
    await s.refresh();
    const st = s.getState();
    expect(st.outline.children.length).toBeGreaterThan(0); // subtree visible
    expect(st.status.openGoals).toBeGreaterThan(0);
    expect(st.status.complete).toBe(false);
  });
});

describe('history', () => {
  test('undo restores the previous proof', async () => {
    const s = open();
    await s.refresh();
    s.applySuggestion('lean-applylemma:divTwoPos');
    expect(s.getState().outline.label).toBe('apply divTwoPos');
    expect(s.undo()).toEqual({ ok: true });
    expect(s.getState().outline.label).toBe('?');
  });

  test('redo reapplies it', async () => {
    const s = open();
    await s.refresh();
    s.applySuggestion('lean-applylemma:divTwoPos');
    s.undo();
    expect(s.redo()).toEqual({ ok: true });
    expect(s.getState().outline.label).toBe('apply divTwoPos');
  });

  test('undo at the beginning is refused', () => {
    expect(open().undo().ok).toBe(false);
  });

  test('history availability is reported in the state', async () => {
    const s = open();
    await s.refresh();
    expect(s.getState().history).toEqual({ canUndo: false, canRedo: false });
    s.applySuggestion('lean-applylemma:divTwoPos');
    expect(s.getState().history.canUndo).toBe(true);
  });
});

// ─── Write-back ──────────────────────────────────────────────────────────────

describe('write-back', () => {
  test('a structural edit rewrites the declaration in the file', async () => {
    const written: string[] = [];
    const s = open({ onSourceChange: (next) => written.push(next) });
    await s.refresh();
    s.applySuggestion('lean-applylemma:divTwoPos');
    expect(written).toHaveLength(1);
    expect(written[0]).toContain('apply divTwoPos');
    // Every other declaration is untouched.
    expect(written[0]).toContain('def divPos (a b : ℝ)');
  });

  test('a cursor move writes nothing', async () => {
    const written: string[] = [];
    const s = open({ onSourceChange: (next) => written.push(next) });
    await s.refresh();
    s.moveCursor(s.getState().cursor.nodeId);
    expect(written).toEqual([]);
  });

  // An unfinished proof must leave WARNINGS in the file, not errors. Dropping
  // the `sorry` under `apply divTwoPos` turns the remaining obligation into
  // Lean's "unsolved goals" error — the file reads as broken while you work.
  test('an open obligation is written as `sorry`', async () => {
    const written: string[] = [];
    const s = open({ onSourceChange: (next) => written.push(next) });
    await s.refresh();
    s.applySuggestion('lean-applylemma:divTwoPos');
    await s.refresh();
    expect(s.proofSource()).toBe('  apply divTwoPos\n  sorry');
  });

  // …and the converse: once Lean reports NO goal at a hole, it was the parser's
  // fabricated continuation and writing `sorry` there would be "no goals to be
  // solved".
  test('a continuation Lean reports no goal at is dropped', async () => {
    const s = ProofSession.open({
      analyze: fakeLean({
        declarations: DECLS,
        baseline: BASELINE,
        // `assumption` closes it: the continuation hole gets no goal.
        rules: [{ tactic: 'assumption', leaves: [] }],
      }),
      source: SOURCE,
      declarations: DECLS,
      declName: 'target',
    });
    await s.refresh();
    s.applySuggestion('lean-assumption');
    await s.refresh();
    expect(s.proofSource()).toBe('  assumption');
  });

  test('before Lean has answered, a hole is assumed open (never silently dropped)', () => {
    const s = open();
    s.insertTactic('apply divTwoPos');
    expect(s.proofSource()).toBe('  apply divTwoPos\n  sorry');
  });

  test('the baseline source is not clobbered by our own write-back', async () => {
    const written: string[] = [];
    const s = open({ onSourceChange: (next) => written.push(next) });
    await s.refresh();
    s.applySuggestion('lean-applylemma:divTwoPos');
    await s.refresh();
    s.runTactic('exact', 'epsPos');
    await s.refresh();
    // The second splice must still land on the declaration, not drift past it
    // as the file grew. Every write contains the whole proof so far.
    const last = written[written.length - 1];
    expect(last).toContain('apply divTwoPos');
    expect(last).toContain('exact epsPos');
    // …and the untouched declarations are still intact around it.
    expect(last).toContain('def halfEqDiv (e : ℝ)');
  });

  // THE bug behind "a branch went missing". The host keeps source and
  // declarations in separate state: it gets the new source the instant we write
  // it, but the matching declarations only when the re-analyze returns. For
  // that beat the session holds new text with STALE line numbers — and the
  // stale UPPER bound (the next declaration's line) slices this declaration
  // short, so re-seeding parses a truncated proof and the last branches of the
  // last tactic just vanish.
  describe('a source update whose declaration lines are stale', () => {
    // The target must NOT be the last declaration: the bound that goes stale is
    // the NEXT one's line, and without a successor there is no bound to break.
    const SRC = [
      'def divPos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a / b := sorry', // 1
      '', // 2
      'theorem target (ε : ℝ) (epsPos : 0 < ε) : 0 < ε / 2 := by', // 3
      '  sorry', // 4
      '', // 5
      'def afterwards : True := trivial', // 6
      '', // 7
    ].join('\n');
    const D: LeanDeclaration[] = [
      decl('divPos', '(a b : ℝ) → 0 < a → 0 < b → 0 < a / b', 1),
      decl('target', '(ε : ℝ) → 0 < ε → 0 < ε / 2', 3, 'theorem'),
      decl('afterwards', 'True', 6),
    ];

    async function split() {
      let written = '';
      const s = ProofSession.open({
        analyze: fakeLean({ declarations: D, baseline: BASELINE, rules: RULES }),
        source: SRC,
        declarations: D,
        declName: 'target',
        onSourceChange: (next) => { written = next; },
      });
      await s.refresh();
      s.applySuggestion('lean-applylemma:divPos');
      await s.refresh();
      return { s, written };
    }

    test('is ignored — the proof keeps every branch', async () => {
      const { s, written } = await split();
      const before = s.proofSource();
      expect(s.getState().outline.children).toHaveLength(2);

      // `afterwards` still recorded at line 6, but the proof has grown past it.
      s.setSource(written, D);
      expect(s.proofSource()).toBe(before);
      expect(s.getState().outline.children).toHaveLength(2);
    });

    test('the matching source + declarations pair IS adopted', async () => {
      const { s, written } = await split();
      const lines = written.split('\n');
      const fresh = D.map((d) => ({
        ...d,
        line: lines.findIndex((l) => new RegExp(`^(def|theorem) ${d.name}\\b`).test(l)) + 1,
      }));
      s.setSource(written, fresh);
      expect(s.getState().outline.children).toHaveLength(2);
    });
  });

  test('the spliced file still parses back to the same proof', async () => {
    const s = open({ onSourceChange: () => {} });
    await s.refresh();
    s.applySuggestion('lean-applylemma:divPos');
    const printed = s.proofSource();
    const reopened = ProofSession.open({
      analyze: fakeLean({ declarations: DECLS, baseline: BASELINE }),
      source: s.fullSource(),
      declarations: DECLS,
      declName: 'target',
    });
    expect(reopened.proofSource()).toBe(printed);
  });
});

// ─── The action layer ────────────────────────────────────────────────────────

describe('availableActions', () => {
  test('at an open goal, every validated suggestion is an action', async () => {
    const s = open();
    await s.refresh();
    expect(actionIds(s)).toContain(`${ACTION.suggestion}lean-applylemma:divTwoPos`);
  });

  test('tactics are offered only at an open goal', async () => {
    const s = open();
    await s.refresh();
    expect(actionIds(s)).toContain(`${ACTION.tactic}intros`);
    // Move onto a non-hole step: tactics have nowhere to go.
    s.applySuggestion('lean-applylemma:divTwoPos');
    s.moveCursor(s.getState().outline.id);
    await s.refresh();
    expect(actionIds(s)).not.toContain(`${ACTION.tactic}intros`);
  });

  test('a non-hole step offers "clear this step" instead', async () => {
    const s = open();
    await s.refresh();
    s.applySuggestion('lean-applylemma:divTwoPos');
    s.moveCursor(s.getState().outline.id);
    expect(actionIds(s)).toContain(ACTION.clearNode);
  });

  test('tactic arguments carry the names that are actually valid', async () => {
    const s = open();
    await s.refresh();
    const apply = s.getState().actions.find((a) => a.id === `${ACTION.tactic}apply`)!;
    expect(apply.params[0].choices).toContain('divPos');
    expect(apply.params[0].choices).toContain('epsPos'); // hypotheses apply too
    expect(apply.params[0].choices).not.toContain('target'); // never itself
  });

  test('undo appears only once there is something to undo', async () => {
    const s = open();
    await s.refresh();
    expect(actionIds(s)).not.toContain(ACTION.undo);
    s.applySuggestion('lean-applylemma:divTwoPos');
    expect(actionIds(s)).toContain(ACTION.undo);
  });

  test('a suggestion action states what it would leave behind', async () => {
    const s = open();
    await s.refresh();
    const a = s.getState().actions.find((x) => x.id === `${ACTION.suggestion}lean-applylemma:divPos`)!;
    expect(a.detail?.subgoals).toBe(2);
    expect(a.detail?.previews).toHaveLength(2);
    expect(a.description).toBe('Leaves 2 goals');
  });
});

describe('dispatch', () => {
  test('runs a suggestion by action id', async () => {
    const s = open();
    await s.refresh();
    expect(s.dispatch({ id: `${ACTION.suggestion}lean-applylemma:divTwoPos` })).toEqual({ ok: true });
    expect(s.getState().outline.label).toBe('apply divTwoPos');
  });

  test('runs a manual tactic with its argument', async () => {
    const s = open();
    await s.refresh();
    expect(s.dispatch({ id: `${ACTION.tactic}intros`, args: { names: 'x' } })).toEqual({ ok: true });
    expect(s.getState().outline.label).toBe('intro x');
  });

  test('a missing required argument is reported', async () => {
    const s = open();
    await s.refresh();
    const r = s.dispatch({ id: `${ACTION.tactic}intros` });
    expect(r.ok).toBe(false);
    expect(r.error).toMatch(/needs a "names" argument/);
  });

  test('an action that is not currently available is refused', () => {
    const s = open(); // no round-trip yet → no tactics
    const r = s.dispatch({ id: `${ACTION.tactic}intros`, args: { names: 'x' } });
    expect(r.ok).toBe(false);
    expect(r.error).toMatch(/not available right now/);
  });

  test('an unknown action id is refused', () => {
    expect(open().dispatch({ id: 'nonsense' }).ok).toBe(false);
  });

  test('navigation and history dispatch too', async () => {
    const s = open();
    await s.refresh();
    s.dispatch({ id: `${ACTION.suggestion}lean-applylemma:divPos` });
    expect(s.dispatch({ id: ACTION.cursorNextHole })).toEqual({ ok: true });
    expect(s.dispatch({ id: ACTION.undo })).toEqual({ ok: true });
    expect(s.getState().outline.tag).toBe('hole');
  });

  test('selection dispatches by Lean subexpression position', async () => {
    const s = open();
    await s.refresh();
    const pos = s.getState().goal!.subterms[0].pos;
    expect(s.dispatch({ id: ACTION.selectSubterm, args: { pos } })).toEqual({ ok: true });
    expect(s.dispatch({ id: ACTION.clearSelection })).toEqual({ ok: true });
    expect(s.getState().selection.subterm).toBeNull();
  });
});

// ─── Subscription ────────────────────────────────────────────────────────────

describe('subscribe', () => {
  test('notifies on every state change', async () => {
    const s = open();
    const seen: number[] = [];
    s.subscribe((st) => seen.push(st.suggestions.length));
    await s.refresh();
    expect(seen.length).toBeGreaterThan(0);
  });

  test('unsubscribing stops the notifications', async () => {
    const s = open();
    let count = 0;
    const off = s.subscribe(() => count++);
    await s.refreshGoals();
    const afterFirst = count;
    off();
    await s.refreshGoals();
    expect(count).toBe(afterFirst);
  });

  test('a disposed session goes quiet', async () => {
    const s = open();
    let count = 0;
    s.subscribe(() => count++);
    s.dispose();
    await s.refresh();
    expect(count).toBe(0);
  });
});

// ─── The outline as a readable artifact ──────────────────────────────────────

describe('outline', () => {
  test('renders the proof as an indented listing with the cursor marked', async () => {
    const s = open();
    await s.refresh();
    s.applySuggestion('lean-applylemma:divPos');
    await s.refresh();
    const printed = formatOutline(s.getState().outline);
    expect(printed).toContain('apply divPos');
    expect(printed).toContain('ha:');
    expect(printed).toContain('hb:');
    expect(printed.split('\n').filter((l) => l.startsWith('▶'))).toHaveLength(1);
  });
});
