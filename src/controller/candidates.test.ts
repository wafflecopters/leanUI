import { describe, expect, test } from 'vitest';
import { tacticCandidates, type CandidateInput } from './candidates';
import type { LeanDeclaration } from '../lean/types';

const decl = (name: string, prettyType: string, kind: LeanDeclaration['kind'] = 'def'): LeanDeclaration => ({
  name,
  kind,
  prettyType,
  line: 1,
  col: 0,
});

/** The real-analysis preset's shape, trimmed to what ranking looks at. */
const REAL_ANALYSIS: LeanDeclaration[] = [
  decl('divTwoPos', '{R : Real} → (e : ℝ) → 0 < e → 0 < e / 2'),
  decl('divPos', '{R : Real} → (a b : ℝ) → 0 < a → 0 < b → 0 < a / b'),
  decl('leLtTrans', '{R : Real} → (a b c : ℝ) → a ≤ b → b < c → a < c'),
  decl('halfEqDiv', '{R : Real} → (e : ℝ) → rhalf R * e = e / 2'),
  decl('divTwoAddEq', '{R : Real} → (e : ℝ) → e / 2 + e / 2 = e'),
  decl('divDenomExpand', '{R : Real} → (x b d : ℝ) → x / b = x * d / (b * d)'),
  decl('plusComm', '∀ (n m : MyNat), n + m = m + n'),
  decl('Carrier', 'Real → Type'),
  decl('rabs', '{R : Real} → ℝ → ℝ'),
];

const base: CandidateInput = {
  declarations: REAL_ANALYSIS,
  currentDeclName: 'limitAdd',
  goalText: '0 < ε / 2',
  hypotheses: [
    { name: 'epsPos', type: '0 < ε' },
    { name: 'limF', type: 'lim⟦x0⟧ f = L' },
  ],
};

const ids = (input: CandidateInput) => tacticCandidates(input).map((s) => s.id);

describe('tacticCandidates', () => {
  // A goal still wrapped in binders can't be worked on until they're opened,
  // and typing the names is the first chore of every ε-δ proof.
  describe('opening the goal\u2019s binders', () => {
    const withGoal = (goalText: string, hyps = base.hypotheses) =>
      tacticCandidates({ ...base, goalText, hypotheses: hyps });

    test('offers one move that introduces the whole telescope', () => {
      const s = withGoal('(epsilon : ℝ) → 0 < epsilon → DPair ℝ (fun d => P d)', []);
      const intro = s.find((x) => x.id.startsWith('lean-intros:'));
      expect(intro?.tactic).toBe('intro ε h');
    });

    test('it is offered BEFORE the lemma searches — nothing else applies yet', () => {
      const ids = withGoal('(epsilon : ℝ) → 0 < epsilon → P', []).map((x) => x.id);
      const intro = ids.findIndex((id) => id.startsWith('lean-intros:'));
      expect(intro).toBeGreaterThanOrEqual(0);
      expect(intro).toBeLessThan(ids.indexOf('lean-assumption'));
      expect(intro).toBeLessThan(ids.indexOf('lean-constructor'));
    });

    test('a goal with nothing at the front offers no intro', () => {
      expect(withGoal('0 < ε / 2').some((x) => x.id.startsWith('lean-intros:'))).toBe(false);
    });

    test('the names never shadow what is already in scope', () => {
      const s = withGoal('(epsilon : ℝ) → 0 < epsilon → P', [
        { name: 'ε', type: 'ℝ' },
        { name: 'h', type: 'True' },
      ]);
      expect(s.find((x) => x.id.startsWith('lean-intros:'))?.tactic).toBe('intro ε1 h1');
    });
  });

  test('always offers assumption and constructor', () => {
    const got = ids(base);
    expect(got).toContain('lean-assumption');
    expect(got).toContain('lean-constructor');
  });

  test('offers the goal-shaped apply lemmas, best first', () => {
    const applies = tacticCandidates(base)
      .filter((s) => s.id.startsWith('lean-applylemma:'))
      .map((s) => s.id.slice('lean-applylemma:'.length));
    expect(applies.slice(0, 2)).toEqual(['divTwoPos', 'divPos']);
    // An equality lemma is not a candidate for a `<` goal.
    expect(applies).not.toContain('plusComm');
  });

  // REGRESSION: the panel used to pass `cursorGoal.plain` — the whole goal
  // state. `limF : lim⟦x0⟧ f = L` in the context made the goal read as an
  // EQUALITY, so every `<` lemma was filtered out and the pills were equality
  // lemmas that all failed validation. The contract is now explicit: goalText
  // is the TARGET.
  test('an equation in the CONTEXT never changes the goal-shape read', () => {
    const withNoisyContext: CandidateInput = {
      ...base,
      hypotheses: [
        ...base.hypotheses,
        { name: 'hEq', type: 'f = g' },
        { name: 'hEq2', type: 'x + y = z' },
      ],
    };
    const applies = tacticCandidates(withNoisyContext)
      .filter((s) => s.id.startsWith('lean-applylemma:'))
      .map((s) => s.id.slice('lean-applylemma:'.length));
    expect(applies.slice(0, 2)).toEqual(['divTwoPos', 'divPos']);
  });

  test('equality hypotheses are rewrite candidates, ahead of file lemmas', () => {
    const got = ids(base);
    const hypRw = got.indexOf('lean-rw:limF');
    const fileRw = got.findIndex((id) => id.startsWith('lean-rw:') && id !== 'lean-rw:limF');
    expect(hypRw).toBeGreaterThanOrEqual(0);
    expect(hypRw).toBeLessThan(fileRw);
  });

  test('the current declaration is never a candidate for its own proof', () => {
    const selfReferential: CandidateInput = {
      ...base,
      declarations: [...REAL_ANALYSIS, decl('limitAdd', '{R : Real} → (a : ℝ) → 0 < a')],
    };
    expect(ids(selfReferential)).not.toContain('lean-applylemma:limitAdd');
  });

  test('no subterm selected → no unfold candidates (they are a big batch)', () => {
    expect(ids(base).some((id) => id.startsWith('lean-unfold:'))).toBe(false);
  });

  test('a selected subterm adds unfolds and a conv-scoped rewrite per lemma', () => {
    const got = ids({ ...base, selectedSubtermText: 'ε / 2' });
    expect(got.some((id) => id.startsWith('lean-unfold:'))).toBe(true);
    // The scoped form is listed BEFORE the whole-goal form so dedup-by-label
    // keeps the scoped tactic.
    const conv = got.indexOf('lean-convrw:divDenomExpand');
    const plain = got.indexOf('lean-rw:divDenomExpand');
    expect(conv).toBeGreaterThanOrEqual(0);
    expect(conv).toBeLessThan(plain);
  });

  test('the conv rewrite targets the selected subterm verbatim', () => {
    const conv = tacticCandidates({ ...base, selectedSubtermText: 'ε / 2' }).find(
      (s) => s.id === 'lean-convrw:divDenomExpand',
    );
    expect(conv?.tactic).toBe('conv in (ε / 2) => rw [divDenomExpand]');
  });

  test('a selected hypothesis contributes exact/apply/cases, listed FIRST', () => {
    const got = ids({ ...base, selectedHypName: 'limF' });
    expect(got.slice(0, 3)).toEqual(['hyp-exact:limF', 'hyp-apply:limF', 'hyp-cases:limF']);
  });

  test('no hypothesis selected → no hypothesis actions', () => {
    expect(ids(base).some((id) => id.startsWith('hyp-'))).toBe(false);
  });

  test('candidate ids are unique (dedup across sources)', () => {
    const got = ids({ ...base, selectedSubtermText: 'ε / 2', selectedHypName: 'epsPos' });
    expect(new Set(got).size).toBe(got.length);
  });

  test('trial order puts the cheap high-yield candidates before the long tail', () => {
    const got = ids(base);
    const at = (id: string) => got.indexOf(id);
    expect(at('lean-constructor')).toBeLessThan(at('lean-applylemma:divTwoPos'));
    expect(at('lean-applylemma:divTwoPos')).toBeLessThan(at('lean-rw:limF'));
    // The `simp [everything]` ring probe is one expensive trial — dead last.
    expect(at('lean-simp-ring')).toBe(got.length - 1);
  });

  test('an empty goal (no round-trip yet) still yields the always-on candidates', () => {
    const got = ids({ ...base, goalText: '' });
    expect(got).toContain('lean-assumption');
    expect(got).toContain('lean-constructor');
    expect(got.some((id) => id.startsWith('lean-applylemma:'))).toBe(false);
  });

  test('a file with no equality lemmas offers no ring probe', () => {
    const got = ids({ ...base, declarations: [decl('foo', 'Nat → Nat')] });
    expect(got).not.toContain('lean-simp-ring');
  });
});

/**
 * One code path has to serve someone who axiomatises ℝ from scratch AND someone
 * who imports Mathlib. It does that by never asking which it has: solvers from
 * both worlds are always PROPOSED here, and the ones that don't exist are killed
 * by validation (see validate.test.ts, "a tactic this Lean doesn't have").
 */
describe('solvers are proposed without asking what Lean has', () => {
  test('core and Mathlib solvers are both offered, on any file', () => {
    // A file with nothing in it — no lemmas to rank, no imports to inspect.
    const got = ids({ ...base, declarations: [], hypotheses: [] });
    // Core Lean.
    expect(got).toContain('lean-solver:omega');
    expect(got).toContain('lean-solver:decide');
    // Mathlib. Offered even though this preset plainly has no Mathlib: proposing
    // is free, and only a real trial can answer whether it's there.
    expect(got).toContain('lean-solver:positivity');
    expect(got).toContain('lean-solver:linarith');
    expect(got).toContain('lean-solver:norm_num');
  });

  test('closing the goal outright is offered before splitting it up', () => {
    const got = ids(base);
    // A solver discharges `0 < ε / 2`; `constructor` only turns it into two
    // more goals. Rank the finisher first.
    expect(got.indexOf('lean-solver:positivity')).toBeLessThan(got.indexOf('lean-constructor'));
    // But after `assumption`, which is cheaper and even more final.
    expect(got.indexOf('lean-assumption')).toBeLessThan(got.indexOf('lean-solver:rfl'));
  });

  test('a solver that a goal-shape heuristic already offers is not doubled up', () => {
    const got = tacticCandidates({ ...base, goalText: 'e / 2 + e / 2 = e' });
    // The `=` heuristic offers `rfl`; so does the blanket solver list. One pill.
    expect(got.filter((s) => s.tactic === 'rfl')).toHaveLength(1);
  });
});

describe('Compute (subterm reduction via the file’s @[simp] rules)', () => {
  test('a clicked subterm offers the scoped conv simp AND a whole-goal twin, same label', () => {
    const s = tacticCandidates({ ...base, goalText: '0 < 2 + -1', selectedSubtermText: '2 + -1' });
    const scoped = s.find((x) => x.id === 'lean-compute-conv');
    const whole = s.find((x) => x.id === 'lean-compute');
    expect(scoped?.tactic).toBe('conv in (2 + -1) => simp');
    expect(whole?.tactic).toBe('simp');
    // Shared label: after validation, dedupeByLabel collapses them to one pill,
    // keeping whichever form actually fired on this goal's term representation.
    expect(scoped?.label).toBe('Compute');
    expect(whole?.label).toBe('Compute');
    // Both are kind 'rw' so validation computes the focused-subterm preview
    // ("2 + -1" -> "1"), which is the pill's whole message.
    expect(scoped?.kind).toBe('rw');
    expect(whole?.kind).toBe('rw');
  });

  test('the scoped form comes first (dedupe keeps the click-shaped tactic when both fire)', () => {
    const s = tacticCandidates({ ...base, goalText: '0 < 2 + -1', selectedSubtermText: '2 + -1' });
    const scopedIdx = s.findIndex((x) => x.id === 'lean-compute-conv');
    const wholeIdx = s.findIndex((x) => x.id === 'lean-compute');
    expect(scopedIdx).toBeGreaterThanOrEqual(0);
    expect(scopedIdx).toBeLessThan(wholeIdx);
  });

  test('no selection, no Compute — it is a subterm move, not goal clutter', () => {
    const s = tacticCandidates({ ...base, goalText: '0 < 2 + -1' });
    expect(s.find((x) => x.id.startsWith('lean-compute'))).toBeUndefined();
  });

describe('a clicked hypothesis that is a FUNCTION can be used', () => {
  const base = (over: Partial<CandidateInput> = {}): CandidateInput => ({
    declarations: REAL_ANALYSIS,
    currentDeclName: 'limitAdd',
    goalText: '|f x + g x - (L + M)| < \u03b5',
    hypotheses: [
      { name: 'dfPos', type: '0 < \u03b4F', isFun: false, fields: [] },
      // The ε-δ workhorse: feed it the point and two bounds, get the estimate.
      // Note the RENDERED type here — the preset prints implications as prose,
      // so there is no `→` in it anywhere. The first version of this feature
      // tested the text for an arrow and missed this exact hypothesis; `isFun`
      // comes from the elaborator and does not care how the type is displayed.
      {
        name: 'fnF',
        type: '\u2200x \u2208 \u211d, 0 < |x - x0| and |x - x0| < \u03b4F, then |f x - L| < \u03b5 / 2',
        isFun: true,
        fields: [],
      },
    ],
    ...over,
  });

  // REGRESSION: clicking the one hypothesis carrying the fact you need produced
  // NOTHING. `exact`/`apply` want its conclusion to match the goal (it doesn't),
  // and a function has no fields for the projection path to find.
  test('offers `use <hyp>`, which opens the builder for its arguments', () => {
    const tactics = tacticCandidates(base({ selectedHypName: 'fnF' })).map((c) => c.tactic);
    expect(tactics).toContain('have leanuiProbe := fnF');
  });

  test('a non-function hypothesis gets no `use` — there is nothing to apply', () => {
    const tactics = tacticCandidates(base({ selectedHypName: 'dfPos' })).map((c) => c.tactic);
    expect(tactics).not.toContain('have leanuiProbe := dfPos');
    // The ordinary hypothesis actions are still there.
    expect(tactics).toContain('exact dfPos');
  });
});
});
