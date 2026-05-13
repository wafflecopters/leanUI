import { describe, expect, test } from 'vitest';

import { mkConst, mkLambda, type TTKTerm } from './kernel';
import { compileTTFromText } from './compile';
import { recheckZonkedTerm } from './compile-zonk-recheck';

const NAT_PRELUDE = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat
`;

describe('zonked term recheck', () => {
  test('accepts a well-typed closed kernel term', () => {
    const definitions = compileTTFromText(NAT_PRELUDE).definitions;
    expect(recheckZonkedTerm(mkConst('Zero'), definitions, 'Zero value')).toBeUndefined();
  });

  test('rejects leftover metas before re-type-checking', () => {
    const definitions = compileTTFromText(NAT_PRELUDE).definitions;
    const error = recheckZonkedTerm({ tag: 'Meta', id: 'm0' }, definitions, 'bad meta');
    expect(error).toContain('unsolved meta');
    expect(error).toContain('m0');
  });

  test('rejects malformed binder terms during fresh kernel re-type-checking', () => {
    const definitions = compileTTFromText(NAT_PRELUDE).definitions;
    const badLambda: TTKTerm = mkLambda(mkConst('Nat'), { tag: 'Var', index: 1 }, 'x');
    const error = recheckZonkedTerm(badLambda, definitions, 'bad lambda');
    expect(error).toContain('re-type-check');
  });

  test('skips Match terms so compiler-generated case trees are not re-inferred ad hoc', () => {
    const definitions = compileTTFromText(NAT_PRELUDE).definitions;
    const generatedMatch: TTKTerm = {
      tag: 'Match',
      scrutinee: { tag: 'Meta', id: 'generated' },
      clauses: [{ patterns: [], rhs: { tag: 'Meta', id: 'generated_rhs' } }],
    };
    expect(recheckZonkedTerm(generatedMatch, definitions, 'generated match')).toBeUndefined();
  });
});
