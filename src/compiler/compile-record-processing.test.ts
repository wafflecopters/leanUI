import { describe, expect, test } from 'vitest';
import { mkConst, mkPi, mkSort, mkULit, type TTKTerm } from './kernel';
import { addInductiveDefinition, createDefinitionsMap } from './term';
import {
  extractParentRecordFields,
  insertFieldImplicitHoles,
  substituteInheritedFieldRefs,
} from './compile-record-processing';

const Type0: TTKTerm = mkSort(mkULit(0));

describe('compile-record-processing', () => {
  test('extractParentRecordFields skips params and preserves implicit field flags', () => {
    let defs = createDefinitionsMap();
    const pairCtorType = mkPi(
      Type0,
      mkPi(
        mkConst('A'),
        mkPi(
          mkConst('A'),
          mkConst('Pair'),
          'snd'
        ),
        'fst'
      ),
      'A'
    );

    defs = addInductiveDefinition(
      defs,
      'Pair',
      mkPi(Type0, Type0, 'A'),
      [{ name: 'MkPair', type: pairCtorType }],
      [],
      undefined,
      {
        fieldNames: ['fst', 'snd'],
        implicitFields: [1],
        projections: ['Pair.fst', 'Pair.snd'],
        isEtaExpandable: true,
        paramCount: 1,
      }
    );

    expect(extractParentRecordFields('Pair', defs)).toEqual([
      { name: 'fst', type: mkConst('A'), implicit: false },
      { name: 'snd', type: mkConst('A'), implicit: true },
    ]);
  });

  test('substituteInheritedFieldRefs rewrites inherited consts and shifts later vars', () => {
    const term = {
      tag: 'App',
      fn: { tag: 'Const', name: 'op' },
      arg: { tag: 'Var', index: 1 },
    } as any;

    expect(substituteInheritedFieldRefs(term, ['op', 'assoc'], 1)).toEqual({
      tag: 'App',
      fn: { tag: 'Var', index: 2 },
      arg: { tag: 'Var', index: 3 },
      argName: undefined,
    });
  });

  test('substituteInheritedFieldRefs handles nested clause binder depth', () => {
    const term = {
      tag: 'Match',
      scrutinee: { tag: 'Const', name: 'x' },
      clauses: [{
        patterns: [{ tag: 'PVar', name: 'p' }],
        rhs: { tag: 'Const', name: 'assoc' },
      }],
    } as any;

    const rewritten = substituteInheritedFieldRefs(term, ['op', 'assoc'], 0) as any;
    expect(rewritten.clauses[0].rhs).toEqual({ tag: 'Var', index: 1 });
  });

  test('insertFieldImplicitHoles inserts missing implicit args for previous field references', () => {
    const term = {
      tag: 'App',
      fn: { tag: 'Var', index: 0 },
      arg: { tag: 'Const', name: 'Zero' },
    } as any;

    const rewritten = insertFieldImplicitHoles(
      term,
      1,
      new Map([[0, { namedArgMap: new Map([['P', 0]]), totalArity: 2 }]])
    ) as any;

    expect(rewritten.tag).toBe('App');
    expect(rewritten.arg).toEqual({ tag: 'Const', name: 'Zero' });
    expect(rewritten.fn.tag).toBe('App');
    expect(rewritten.fn.fn).toEqual({ tag: 'Var', index: 0 });
    expect(rewritten.fn.arg.tag).toBe('Hole');
    expect(rewritten.fn.arg.id).toContain('_field_implicit_f1_');
  });

  test('insertFieldImplicitHoles also works for local binder references with implicit domains', () => {
    const term = {
      tag: 'Binder',
      name: 'f',
      binderKind: { tag: 'BPiTT' },
      domain: {
        tag: 'Binder',
        name: 'P',
        binderKind: { tag: 'BPiTT' },
        domain: { tag: 'Const', name: 'Nat' },
        body: {
          tag: 'Binder',
          name: 'x',
          binderKind: { tag: 'BPiTT' },
          domain: { tag: 'Const', name: 'Nat' },
          body: { tag: 'Const', name: 'Nat' },
        },
        named: true,
      },
      body: {
        tag: 'App',
        fn: { tag: 'Var', index: 0 },
        arg: { tag: 'Const', name: 'Zero' },
      },
    } as any;

    const rewritten = insertFieldImplicitHoles(term, 0, new Map()) as any;
    expect(rewritten.body.fn.tag).toBe('App');
    expect(rewritten.body.fn.fn).toEqual({ tag: 'Var', index: 0 });
    expect(rewritten.body.fn.arg.tag).toBe('Hole');
  });
});
