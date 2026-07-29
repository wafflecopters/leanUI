import { describe, expect, test } from 'vitest';
import { dedupeByLabel, validateOne, validateSuggestions, type ValidateInput } from './validate';
import { fakeLean, brokenAnalyzer, deadAnalyzer } from './testing';
import { leanTacticsToTree } from '../lean/leanTacticsToTree';
import { findFirstHole } from '../proof-tree/tactic-to-tree';
import { taggedToLatex } from '../lean/codeWithInfos';
import { taggedTerm } from './testing';
import type { LeanSuggestion } from '../lean/leanSuggestions';
import type { LeanAnalyzer } from './analyzer';

/** Previews are LaTeX by contract — render the expected goal the same way
 *  rather than pinning the renderer's exact output in every assertion. */
const asPreview = (goal: string) => taggedToLatex(taggedTerm(goal));

const SOURCE = ['def foo : True := by', '  sorry', ''].join('\n');

function inputFor(analyze: LeanAnalyzer, candidates: LeanSuggestion[]): ValidateInput {
  const proof = leanTacticsToTree('sorry');
  const hole = findFirstHole(proof)!;
  return { analyze, source: SOURCE, declLine: 1, proof, cursorId: hole.id, candidates };
}

const cand = (id: string, tactic: string, kind: LeanSuggestion['kind'] = 'apply'): LeanSuggestion => ({
  id,
  label: tactic,
  tactic,
  kind,
});

describe('validateOne', () => {
  test('a tactic Lean rejects at its own line is dropped', async () => {
    const analyze = fakeLean({
      baseline: { target: '0 < ε / 2' },
      rules: [{ tactic: 'apply zeroLtOne', error: 'could not unify' }],
    });
    const c = cand('a', 'apply zeroLtOne');
    expect(await validateOne(c, inputFor(analyze, [c]))).toBeNull();
  });

  test('a tactic that leaves one goal previews it and does not close', async () => {
    const analyze = fakeLean({
      baseline: { target: '0 < ε / 2' },
      rules: [{ tactic: 'apply divTwoPos', leaves: [{ target: '0 < ε' }] }],
    });
    const c = cand('a', 'apply divTwoPos');
    const got = await validateOne(c, inputFor(analyze, [c]));
    expect(got?.closes).toBe(false);
    expect(got?.previews).toEqual([asPreview('0 < ε')]);
    // One goal is not a "subgoals" split — no branch count is carried.
    expect(got?.subgoals).toBeUndefined();
  });

  test('a goal-splitting tactic carries every goal, and its count', async () => {
    const analyze = fakeLean({
      baseline: { target: '0 < ε / 2' },
      rules: [
        { tactic: 'apply divPos', leaves: [{ target: '0 < ε', case: 'ha' }, { target: '0 < 2', case: 'hb' }] },
      ],
    });
    const c = cand('a', 'apply divPos');
    const got = await validateOne(c, inputFor(analyze, [c]));
    expect(got?.subgoals).toBe(2);
    expect(got?.previews).toEqual([asPreview('0 < ε'), asPreview('0 < 2')]);
    expect(got?.subgoalTags).toEqual(['ha', 'hb']);
  });

  test('previews follow the DISPLAY order, so line N is branch N', async () => {
    // Lean postpones the dependent goal: it reports [body-with-?fst, fst].
    // The witness must be presented first, and the previews must agree.
    const analyze = fakeLean({
      baseline: { target: '∃ δ, P δ' },
      rules: [
        {
          tactic: 'constructor',
          leaves: [{ target: 'P ?w.fst', case: 'snd' }, { target: 'ℝ', case: 'fst' }],
        },
      ],
    });
    const c = cand('a', 'constructor');
    const got = await validateOne(c, inputFor(analyze, [c]));
    expect(got?.subgoalTags).toEqual(['fst', 'snd']);
    expect(got?.previews).toEqual([asPreview('ℝ'), asPreview('P ?w.fst')]);
  });

  test('a tactic that leaves no goal is a closer', async () => {
    const analyze = fakeLean({
      baseline: { target: '0 < ε' },
      rules: [{ tactic: 'assumption', leaves: [] }],
    });
    const c = cand('a', 'assumption', 'exact');
    const got = await validateOne(c, inputFor(analyze, [c]));
    expect(got?.closes).toBe(true);
    expect(got?.previews ?? []).toEqual([]);
  });

  test('a tactic whose only result IS the current goal previews nothing', async () => {
    const analyze = fakeLean({
      baseline: { target: '0 < ε / 2' },
      rules: [{ tactic: 'unfold Carrier', leaves: [{ target: '0 < ε / 2' }] }],
    });
    const c = cand('a', 'unfold Carrier', 'unfold');
    const input = { ...inputFor(analyze, [c]), goalOriginal: asPreview('0 < ε / 2') };
    const got = await validateOne(c, input);
    expect(got).not.toBeNull();
    expect(got?.previews).toBeUndefined();
  });

  test('a result headed by a raw match is dropped as unreduced', async () => {
    const analyze = fakeLean({
      baseline: { target: 'n + 0 = n' },
      rules: [{ tactic: 'unfold plus', leaves: [{ target: 'match n with | .zero => n' }] }],
    });
    const c = cand('a', 'unfold plus', 'unfold');
    expect(await validateOne(c, inputFor(analyze, [c]))).toBeNull();
  });

  test('a transport failure is not a validation', async () => {
    const c = cand('a', 'assumption');
    expect(await validateOne(c, inputFor(deadAnalyzer, [c]))).toBeNull();
  });

  test('a bridge error is not a validation (would read as a spurious closer)', async () => {
    const c = cand('a', 'assumption');
    expect(await validateOne(c, inputFor(brokenAnalyzer(), [c]))).toBeNull();
  });

  // A tactic that parses to a bare hole is a NO-OP splice: the trial would
  // validate the unchanged proof, read the untouched goal back, and surface a
  // pill that does nothing when clicked.
  test.each([
    ['blank', ''],
    ['whitespace', '   '],
    ['a literal sorry', 'sorry'],
  ])('%s is dropped without an analyze round-trip', async (_name, tactic) => {
    let calls = 0;
    const analyze = fakeLean({ baseline: { target: 'G' }, onRequest: () => { calls++; } });
    const c = cand('a', tactic);
    expect(await validateOne(c, inputFor(analyze, [c]))).toBeNull();
    expect(calls).toBe(0);
  });

  test('validateTactic is what gets TRIED when it differs from the applied form', async () => {
    const sent: string[] = [];
    const analyze = fakeLean({
      baseline: { target: 'P n' },
      rules: [{ tactic: 'induction n', leaves: [{ target: 'P 0' }] }],
      onRequest: (i) => sent.push(i.source),
    });
    const c: LeanSuggestion = {
      id: 'i',
      label: 'induction n',
      // The APPLIED form carries case bullets…
      tactic: 'induction n\n·\n  sorry\n·\n  sorry',
      // …but the TRIAL is the bare tactic.
      validateTactic: 'induction n',
      kind: 'apply',
    };
    await validateOne(c, inputFor(analyze, [c]));
    expect(sent[0]).toContain('induction n');
    expect(sent[0]).not.toContain('·');
  });
});

describe('validateSuggestions', () => {
  test('keeps the caller order regardless of which trial lands first', async () => {
    const analyze: LeanAnalyzer = async (input) => {
      // The later candidate answers fast, the earlier one slowly.
      const slow = input.source.includes('first');
      await new Promise((r) => setTimeout(r, slow ? 20 : 0));
      return fakeLean({ baseline: { target: 'G' }, rules: [] })(input);
    };
    const cands = [cand('a', 'first'), cand('b', 'second')];
    const got = await validateSuggestions({ ...inputFor(analyze, cands), concurrency: 2 });
    expect(got.map((s) => s.id)).toEqual(['a', 'b']);
  });

  test('streams partial results in caller order as trials land', async () => {
    const analyze = fakeLean({ baseline: { target: 'G' } });
    const cands = [cand('a', 'one'), cand('b', 'two'), cand('c', 'three')];
    const seen: string[][] = [];
    await validateSuggestions({
      ...inputFor(analyze, cands),
      concurrency: 1,
      onProgress: (p) => seen.push(p.map((s) => s.id)),
    });
    expect(seen).toEqual([['a'], ['a', 'b'], ['a', 'b', 'c']]);
  });

  test('a cancelled run contributes nothing', async () => {
    const analyze = fakeLean({ baseline: { target: 'G' } });
    const cands = [cand('a', 'one'), cand('b', 'two')];
    const cancel = { cancelled: true };
    const got = await validateSuggestions({ ...inputFor(analyze, cands), cancel });
    expect(got).toEqual([]);
  });

  test('rejected candidates simply do not appear', async () => {
    const analyze = fakeLean({
      baseline: { target: 'G' },
      rules: [{ tactic: 'bad', error: 'nope' }],
    });
    const cands = [cand('a', 'good'), cand('b', 'bad')];
    const got = await validateSuggestions(inputFor(analyze, cands));
    expect(got.map((s) => s.id)).toEqual(['a']);
  });
});

describe('dedupeByLabel', () => {
  const s = (id: string, label: string, extra: Partial<LeanSuggestion> = {}): LeanSuggestion => ({
    id,
    label,
    tactic: id,
    kind: 'rw',
    ...extra,
  });

  test('the first entry wins the tactic, a later one donates a missing preview', () => {
    const got = dedupeByLabel([
      s('conv', 'rw [L]'),
      s('plain', 'rw [L]', { preview: '\\alpha' }),
    ]);
    expect(got).toHaveLength(1);
    expect(got[0].tactic).toBe('conv'); // the scoped form is kept
    expect(got[0].preview).toBe('\\alpha'); // …with the whole-goal preview
  });

  test('a later entry donates goal previews when the first has none', () => {
    const got = dedupeByLabel([s('conv', 'rw [L]'), s('plain', 'rw [L]', { previews: ['x = y'] })]);
    expect(got[0].previews).toEqual(['x = y']);
  });

  test('an existing preview is never overwritten', () => {
    const got = dedupeByLabel([
      s('conv', 'rw [L]', { preview: 'kept' }),
      s('plain', 'rw [L]', { preview: 'ignored' }),
    ]);
    expect(got[0].preview).toBe('kept');
  });

  test('distinct labels all survive', () => {
    expect(dedupeByLabel([s('a', 'rw [A]'), s('b', 'rw [B]')])).toHaveLength(2);
  });
});

/**
 * How one editor serves two audiences.
 *
 * `candidates.ts` proposes solvers from core Lean and from Mathlib together,
 * without checking which is loaded — because it CAN'T check cheaply, and
 * shouldn't have to. Validation is what makes that safe: a tactic the current
 * environment doesn't have errors at its own line, which is the same signal as
 * a lemma that fails to apply, so it's dropped by the same code.
 *
 * The payoff is that support for a library is not a mode. Someone building ℝ
 * from their own axioms sees their file's lemmas and the core solvers; someone
 * importing Mathlib additionally sees `positivity` close `0 < ε / 2` outright.
 * Neither configures anything, and nothing in the controller branches on it.
 */
describe('capability is discovered by trying, never declared', () => {
  const solverInput = (analyze: LeanAnalyzer, tactics: string[]) =>
    inputFor(analyze, tactics.map((t) => cand(`lean-solver:${t}`, t, 'exact')));

  test("a tactic this Lean doesn't have is dropped like any other failure", async () => {
    // Core Lean on `positivity`, in the shape it was measured to produce:
    // `unknown tactic` at the tactic's line PLUS a knock-on `unsolved goals`
    // back at the `by`. Nothing here says "Mathlib" — it's just a failure.
    const analyze = fakeLean({
      baseline: { target: '0 < ε / 2' },
      rules: [{ tactic: 'positivity', error: 'unknown tactic', alsoUnsolvedAtDecl: true }],
    });
    const c = cand('lean-solver:positivity', 'positivity', 'exact');
    expect(await validateOne(c, inputFor(analyze, [c]))).toBeNull();
  });

  test('with the library present the same candidate closes the goal', async () => {
    // Same candidate, same code path, different environment.
    const analyze = fakeLean({
      baseline: { target: '0 < ε / 2' },
      rules: [{ tactic: 'positivity', leaves: [] }],
    });
    const c = cand('lean-solver:positivity', 'positivity', 'exact');
    const got = await validateOne(c, inputFor(analyze, [c]));
    expect(got?.closes).toBe(true);
  });

  test('a mixed core/Mathlib list survives on core Lean, keeping what works', async () => {
    // What the from-scratch user's session really looks like: the Mathlib half
    // of SOLVER_TACTICS evaporates and the rest is unharmed.
    const analyze = fakeLean({
      baseline: { target: '0 < ε / 2' },
      rules: [
        { tactic: 'positivity', error: 'unknown tactic', alsoUnsolvedAtDecl: true },
        { tactic: 'linarith', error: 'unknown tactic', alsoUnsolvedAtDecl: true },
        { tactic: 'norm_num', error: 'unknown tactic', alsoUnsolvedAtDecl: true },
        { tactic: 'omega', error: 'omega could not prove the goal' },
        { tactic: 'decide', leaves: [] },
      ],
    });
    const got = await validateSuggestions(
      solverInput(analyze, ['positivity', 'linarith', 'norm_num', 'omega', 'decide']),
    );
    expect(got.map((s) => s.tactic)).toEqual(['decide']);
  });
});
