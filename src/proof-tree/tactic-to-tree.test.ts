import { describe, test, expect } from 'vitest';
import { tacticCommandsToProofTree, findFirstHole } from './tactic-to-tree';
import { TacticCommand, flatParamsToCasePatterns } from './tactic-command';

// A tactic argument is source text — see ./tactic-command.
const cst = (name: string): string => name;
const app = (fn: string, arg: string): string => `(${fn} ${arg})`;

function tc(name: string, args: string[] = [], opts?: Partial<TacticCommand>): TacticCommand {
  return { name, args, ...opts };
}

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
