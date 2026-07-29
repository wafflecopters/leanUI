/**
 * The positivity toolkit is PROVED, not assumed.
 *
 * Compiling without errors proves nothing here: a `sorry`ed lemma compiles
 * perfectly happily, and the whole ε-δ development is built on these. The only
 * honest check is Lean's own — `#print axioms f` lists what `f` actually rests
 * on, and `sorryAx` in that list means it isn't a proof.
 *
 * Real Lean; run with `npm run test:e2e`.
 */
import { afterAll, expect, test } from 'vitest';
import { analyzeLeanSource, shutdownLeanBridge } from '../../server/lean-bridge';
import { LEAN_PRESETS } from './presets';

const MINUTES = 60_000;

/**
 * Strict positivity, from the ordered-field axioms up to `0 < ε / 2`.
 *
 * Each rests only on the `OrderedField` structure's own fields — `0 < 1` is not
 * an extra axiom, it's `zeroLeOne` paired with `zeroNeOne`, because `a < b` is
 * defined as `a ≤ b` together with `a ≠ b`.
 */
const MUST_BE_PROVED = [
  // Cancellation, which the strict (≠) halves all lean on.
  'addZeroLeft',
  'addCancelRightHelper',
  'addCancelRight',
  'mulZeroRight',
  // Strict order on the literals.
  'zeroLtOne',
  'oneNeTwo',
  'oneLtTwo',
  'zeroLtTwo',
  // Translation invariance for `<` (the field gives it only for `≤`), and its
  // inverse — cancellation — which read backwards is the "add the same thing to
  // both sides" move on a `<` goal.
  'addLtRight',
  'addLtLeft',
  'addLtRightCancel',
  'addLtLeftCancel',
  // Products and inverses: in a field a product of nonzeros is nonzero.
  'mulInvLeft',
  'mulNeZero',
  'invNeZero',
  'mulPos',
  'invPosStrict',
  // …and therefore the ε-δ workhorses.
  'halfPosStrict',
  'halfMulEpsPos',
  'divPos',
  'divTwoPos',
  // The Compute (@[simp]) arithmetic: cancellation and the literal bridges.
  'negLeft',
  'addSumNeg',
  'twoAddNegOne',
  'litZero',
  'litOne',
  'litTwo',
  // The limitAdd toolkit: the neg family (formerly sorries), the sub-of-sums
  // rearrangement, the min family, and the triangle inequality they feed.
  'negUnique',
  'negAddCancel',
  'negAdd',
  'addAddSwap',
  'subAddSub',
  'rmin',
  'minLeLeft',
  'minLeRight',
  'ltMin',
  'minPos',
  'absTriangle',
  'convertEps',
  'addLtBoth',
];

afterAll(() => {
  shutdownLeanBridge();
});

test(
  'the strict-positivity chain up to 0 < ε/2 does not rest on sorry',
  async () => {
    const preset = LEAN_PRESETS.find((p) => p.name === 'Real Analysis (chain rule)');
    if (!preset) throw new Error('missing preset');

    const source = `${preset.code}\n${MUST_BE_PROVED.map((n) => `#print axioms ${n}`).join('\n')}\n`;
    const result = await analyzeLeanSource(source, { timeoutMs: 10 * MINUTES });
    expect(result.bridgeError).toBeUndefined();
    expect(result.messages.filter((m) => m.severity === 'error').map((m) => m.text)).toEqual([]);

    // `#print axioms f` answers on an information message beginning with 'f'.
    const verdicts = new Map<string, string>();
    for (const m of result.messages) {
      if (m.severity !== 'information') continue;
      const text = m.text.trim();
      const name = text.match(/^'([^']+)'/)?.[1];
      if (name) verdicts.set(name, text);
    }

    const missing = MUST_BE_PROVED.filter((n) => !verdicts.has(n));
    expect(missing, 'every checked declaration must exist').toEqual([]);

    const sorried = MUST_BE_PROVED.filter((n) => /sorryAx/.test(verdicts.get(n) ?? ''));
    expect(sorried, 'these are not actually proved').toEqual([]);
  },
  10 * MINUTES,
);

/**
 * limitAdd is PROVABLE with the preset's toolkit — the ground truth the
 * editor's move set must be able to reproduce click by click. The preset
 * deliberately ships `limitAdd := sorry` (it is the demo exercise), so the
 * proof lives here: if a refactor drops a lemma this proof needs, this test
 * names the break before a user finds a dead end mid-demo.
 */
const LIMIT_ADD_PROOF = `
def limitAddProved {R : Real} (f g : Carrier R → Carrier R) (x0 L M : Carrier R)
    (limF : Limit f x0 L) (limG : Limit g x0 M) :
    Limit (fun x => radd (f x) (g x)) x0 (radd L M) :=
  Limit.mk (fun epsilon epsPos =>
    let h1 := divTwoPos epsilon epsPos
    let p1 := limF.eps_delta (rdiv epsilon (rtwo R)) h1
    let p2 := limG.eps_delta (rdiv epsilon (rtwo R)) h1
    DPair.mk (rmin p1.fst p2.fst)
      (Pair.mk (minPos p1.fst p2.fst p1.snd.fst p2.snd.fst)
        (fun x hx0 hxd =>
          let hf := p1.snd.snd x hx0
            (ltLeTrans (rabs (rsub x x0)) (rmin p1.fst p2.fst) p1.fst hxd
              (minLeLeft p1.fst p2.fst))
          let hg := p2.snd.snd x hx0
            (ltLeTrans (rabs (rsub x x0)) (rmin p1.fst p2.fst) p2.fst hxd
              (minLeRight p1.fst p2.fst))
          let le1 := replace
            (fun z => rle (rabs z) (radd (rabs (rsub (f x) L)) (rabs (rsub (g x) M))))
            (eqSym (subAddSub (f x) (g x) L M))
            (absTriangle (rsub (f x) L) (rsub (g x) M))
          convertEps epsilon (rabs (rsub (radd (f x) (g x)) (radd L M)))
            (leLtTrans (rabs (rsub (radd (f x) (g x)) (radd L M)))
              (radd (rabs (rsub (f x) L)) (rabs (rsub (g x) M)))
              (radd (rdiv epsilon (rtwo R)) (rdiv epsilon (rtwo R)))
              le1
              (addLtBoth (rabs (rsub (f x) L)) (rdiv epsilon (rtwo R))
                (rabs (rsub (g x) M)) (rdiv epsilon (rtwo R)) hf hg)))))
#print axioms limitAddProved
`;

test(
  'limitAdd is provable from the preset toolkit, sorry-free',
  async () => {
    const preset = LEAN_PRESETS.find((p) => p.name === 'Real Analysis (chain rule)');
    if (!preset) throw new Error('missing preset');
    const base = preset.code.endsWith('\n') ? preset.code : `${preset.code}\n`;
    const r = await analyzeLeanSource(base + LIMIT_ADD_PROOF, {
      timeoutMs: 10 * MINUTES,
      prefix: base,
      body: LIMIT_ADD_PROOF,
    });
    expect(r.bridgeError).toBeUndefined();
    expect(r.messages.filter((m) => m.severity === 'error').map((m) => m.text)).toEqual([]);
    const axioms = r.messages.find(
      (m) => m.severity === 'information' && /limitAddProved/.test(m.text),
    );
    expect(axioms?.text ?? '(missing)').not.toMatch(/sorryAx/);
  },
  10 * MINUTES,
);

/**
 * The Compute move actually computes: plain `simp` (the preset's @[simp]
 * bridges + facts) reduces `2 + -1` to `1` in EVERY term representation a goal
 * can hold the numerals in. The three forms are not interchangeable — a
 * user-typed `2` is `OfNat.ofNat 2` while a lemma-substituted one is `rtwo R`,
 * identical in display and disjoint for syntactic matching — which is exactly
 * the regression this pins: lemmas stated on one form silently missed the
 * others (the "none of these can reduce 2 + -1" screenshot).
 */
test(
  'Compute: simp reduces 2 + -1 to 1 in literal, mixed, and constant form',
  async () => {
    const preset = LEAN_PRESETS.find((p) => p.name === 'Real Analysis (chain rule)');
    if (!preset) throw new Error('missing preset');
    const base = preset.code.endsWith('\n') ? preset.code : `${preset.code}\n`;
    const baseLines = base.split('\n').length - 1;

    const forms: Array<[string, string]> = [
      ['literal', '(0 : Carrier R) < 2 + -1'],
      ['mixed', 'rlt (rzero R) (radd (2 : Carrier R) (rneg (rone R)))'],
      ['constant', 'rlt (rzero R) (radd (rtwo R) (rneg (rone R)))'],
    ];
    for (const [form, goalType] of forms) {
      const body = `\ndef probeReduce {R : Real} : ${goalType} := by\n  simp\n  sorry\n`;
      const r = await analyzeLeanSource(base + body, {
        timeoutMs: 10 * MINUTES,
        prefix: base,
        body,
      });
      expect(r.bridgeError, form).toBeUndefined();
      // simp itself must be accepted (it errors on "no progress").
      const errsAtTactic = r.messages.filter(
        (m) => m.severity === 'error' && m.startLine - baseLines === 4,
      );
      expect(errsAtTactic.map((m) => m.text), form).toEqual([]);
      // …and the goal it leaves at the sorry is the reduced one.
      const after = r.goals.filter((g) => g.startLine - baseLines >= 5);
      expect(after.length, form).toBeGreaterThan(0);
      const target = after[after.length - 1].goals.map((g) => g.plain.split('⊢')[1]?.trim());
      expect(target, form).toEqual(['0 < 1']);
    }
  },
  10 * MINUTES,
);
