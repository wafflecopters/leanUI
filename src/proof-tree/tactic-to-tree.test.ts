import { describe, test, expect } from 'vitest';
import { tacticCommandsToProofTree, surfaceTermToString, findFirstHole } from './tactic-to-tree';
import { TacticCommand, TTerm, flatParamsToCasePatterns } from '../compiler/surface';

// Helper to create a Const TTerm
const cst = (name: string): TTerm => ({ tag: 'Const', name });

// Helper to create an App TTerm
const app = (fn: TTerm, arg: TTerm): TTerm => ({ tag: 'App', fn, arg });

// Helper to create a TacticCommand
function tc(name: string, args: TTerm[] = [], opts?: Partial<TacticCommand>): TacticCommand {
  return { name, args, ...opts };
}

describe('surfaceTermToString', () => {
  test('Const', () => {
    expect(surfaceTermToString(cst('refl'))).toBe('refl');
  });

  test('App', () => {
    expect(surfaceTermToString(app(cst('f'), cst('x')))).toBe('(f x)');
  });

  test('nested App', () => {
    expect(surfaceTermToString(app(app(cst('f'), cst('a')), cst('b')))).toBe('(f a b)');
  });

  test('lambda', () => {
    const lam: TTerm = {
      tag: 'Binder', name: 'x', binderKind: { tag: 'BLamTT' },
      body: cst('x'),
    };
    expect(surfaceTermToString(lam)).toBe('(fun x => x)');
  });

  test('Hole', () => {
    const hole: TTerm = { tag: 'Hole', id: '_', type: cst('Nat'), context: [] };
    expect(surfaceTermToString(hole)).toBe('_');
  });

  // REGRESSION (image #37): the structured editor's `case 'exact'` flow calls
  // `parseExpr(input)` then `surfaceTermToString(parsed)` to store the proof
  // node's expr string. If a literal tag falls through to the default '?' arm,
  // the stored expr becomes "?" and validation surfaces "Type definition not
  // found: ?". `NatLit`/`RatLit` must round-trip.
  test('NatLit round-trips', () => {
    expect(surfaceTermToString({ tag: 'NatLit', value: 5n })).toBe('5');
  });

  test('RatLit (integer-shaped, negative) round-trips as signed integer', () => {
    expect(surfaceTermToString({ tag: 'RatLit', num: -1n, den: 1n })).toBe('-1');
  });

  test('RatLit (terminating decimal, negative) round-trips as decimal', () => {
    // 3/2 (canonical of 1.5) → "1.5"; -3/2 → "-1.5"
    expect(surfaceTermToString({ tag: 'RatLit', num: -3n, den: 2n })).toBe('-1.5');
    expect(surfaceTermToString({ tag: 'RatLit', num: 3n, den: 2n })).toBe('1.5');
  });

  test('RatLit (non-terminating) falls back to fraction syntax', () => {
    // 1/3 has no finite decimal expansion.
    expect(surfaceTermToString({ tag: 'RatLit', num: 1n, den: 3n })).toBe('(1 / 3)');
  });
});

describe('tacticCommandsToProofTree', () => {
  test('empty commands → HoleNode', () => {
    const tree = tacticCommandsToProofTree([]);
    expect(tree.tag).toBe('hole');
  });

  test('intro n; exact refl', () => {
    const tree = tacticCommandsToProofTree([
      tc('intro', [cst('n')]),
      tc('exact', [cst('refl')]),
    ]);
    expect(tree.tag).toBe('intros');
    if (tree.tag !== 'intros') return;
    expect(tree.names).toEqual(['n']);
    expect(tree.child.tag).toBe('exact');
    if (tree.child.tag !== 'exact') return;
    expect(tree.child.expr).toBe('refl');
  });

  test('intros a b c', () => {
    const tree = tacticCommandsToProofTree([
      tc('intros', [cst('a'), cst('b'), cst('c')]),
    ]);
    expect(tree.tag).toBe('intros');
    if (tree.tag !== 'intros') return;
    expect(tree.names).toEqual(['a', 'b', 'c']);
    expect(tree.child.tag).toBe('hole');
  });

  test('apply sym; exact proof', () => {
    const tree = tacticCommandsToProofTree([
      tc('apply', [cst('sym')]),
      tc('exact', [app(cst('plusZeroRight'), cst('m'))]),
    ]);
    expect(tree.tag).toBe('apply');
    if (tree.tag !== 'apply') return;
    expect(tree.name).toBe('sym');
    expect(tree.children).toHaveLength(1);
    expect(tree.children[0].tag).toBe('exact');
  });

  test('induction with case branches', () => {
    const tree = tacticCommandsToProofTree([
      tc('induction', [cst('n')], {
        caseBranches: [
          { constructor: 'Zero', params: flatParamsToCasePatterns([]), tactics: [tc('exact', [cst('refl')])] },
          { constructor: 'Succ', params: flatParamsToCasePatterns(['k', 'IH']), tactics: [tc('exact', [app(cst('congSucc'), cst('IH'))])] },
        ],
      }),
    ]);
    expect(tree.tag).toBe('induction');
    if (tree.tag !== 'induction') return;
    expect(tree.scrutinee).toBe('n');
    expect(tree.cases).toHaveLength(2);

    expect(tree.cases[0].constructorName).toBe('Zero');
    expect(tree.cases[0].body.tag).toBe('exact');

    expect(tree.cases[1].constructorName).toBe('Succ');
    expect(tree.cases[1].constructorParamNames).toEqual(['k', 'IH']);
    expect(tree.cases[1].body.tag).toBe('exact');
  });

  test('rw h1, h2; exact refl → rewrite chain', () => {
    const tree = tacticCommandsToProofTree([
      tc('rw', [cst('h1'), cst('h2')]),
      tc('exact', [cst('refl')]),
    ]);
    expect(tree.tag).toBe('rewrite');
    if (tree.tag !== 'rewrite') return;
    expect(tree.name).toBe('h1');
    expect(tree.child.tag).toBe('rewrite');
    if (tree.child.tag !== 'rewrite') return;
    expect(tree.child.name).toBe('h2');
    expect(tree.child.child.tag).toBe('exact');
  });

  test('unfold f g; exact refl → unfold chain', () => {
    const tree = tacticCommandsToProofTree([
      tc('unfold', [cst('f'), cst('g')]),
      tc('exact', [cst('refl')]),
    ]);
    expect(tree.tag).toBe('unfold');
    if (tree.tag !== 'unfold') return;
    expect(tree.name).toBe('f');
    expect(tree.child.tag).toBe('unfold');
    if (tree.child.tag !== 'unfold') return;
    expect(tree.child.name).toBe('g');
    expect(tree.child.child.tag).toBe('exact');
  });

  test('simp foo bar; exact refl → simp node with continuation', () => {
    const tree = tacticCommandsToProofTree([
      tc('simp', [cst('foo'), cst('bar')]),
      tc('exact', [cst('refl')]),
    ]);
    expect(tree.tag).toBe('simp');
    if (tree.tag !== 'simp') return;
    expect(tree.lemmas).toEqual(['foo', 'bar']);
    expect(tree.steps).toEqual([]);
    expect(tree.child.tag).toBe('exact');
  });

  test('unknown tactics are skipped', () => {
    const tree = tacticCommandsToProofTree([
      tc('sorry'),
      tc('exact', [cst('refl')]),
    ]);
    // sorry is skipped, continuation is exact
    expect(tree.tag).toBe('exact');
  });

  test('nested induction in case branch', () => {
    // intro n; induction n with
    //   | Zero => intro m; exact refl
    //   | Succ k IH => intro m; exact (congSucc (IH m))
    const tree = tacticCommandsToProofTree([
      tc('intro', [cst('n')]),
      tc('induction', [cst('n')], {
        caseBranches: [
          {
            constructor: 'Zero', params: flatParamsToCasePatterns([]),
            tactics: [tc('intro', [cst('m')]), tc('exact', [cst('refl')])],
          },
          {
            constructor: 'Succ', params: flatParamsToCasePatterns(['k', 'IH']),
            tactics: [tc('intro', [cst('m')]), tc('exact', [app(cst('congSucc'), app(cst('IH'), cst('m')))])],
          },
        ],
      }),
    ]);

    expect(tree.tag).toBe('intros');
    if (tree.tag !== 'intros') return;
    expect(tree.names).toEqual(['n']);

    const ind = tree.child;
    expect(ind.tag).toBe('induction');
    if (ind.tag !== 'induction') return;
    expect(ind.cases).toHaveLength(2);

    // Zero case: intros → exact
    const zeroBody = ind.cases[0].body;
    expect(zeroBody.tag).toBe('intros');
    if (zeroBody.tag !== 'intros') return;
    expect(zeroBody.child.tag).toBe('exact');

    // Succ case: intros → exact
    const succBody = ind.cases[1].body;
    expect(succBody.tag).toBe('intros');
  });
});

describe('findFirstHole', () => {
  test('hole returns itself', () => {
    const tree = tacticCommandsToProofTree([]);
    expect(findFirstHole(tree)).toBe(tree);
  });

  test('complete proof has no hole', () => {
    const tree = tacticCommandsToProofTree([tc('exact', [cst('refl')])]);
    expect(findFirstHole(tree)).toBeNull();
  });

  test('finds hole after intros', () => {
    const tree = tacticCommandsToProofTree([tc('intros', [cst('a'), cst('b')])]);
    expect(tree.tag).toBe('intros');
    const hole = findFirstHole(tree);
    expect(hole).not.toBeNull();
    expect(hole!.tag).toBe('hole');
  });

  test('finds hole in first induction case', () => {
    const tree = tacticCommandsToProofTree([
      tc('induction', [cst('n')], {
        caseBranches: [
          { constructor: 'Zero', params: flatParamsToCasePatterns([]), tactics: [] },
          { constructor: 'Succ', params: flatParamsToCasePatterns(['k']), tactics: [tc('exact', [cst('refl')])] },
        ],
      }),
    ]);
    const hole = findFirstHole(tree);
    expect(hole).not.toBeNull();
    expect(hole!.tag).toBe('hole');
  });
});
