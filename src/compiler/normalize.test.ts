import { describe, expect, test } from 'vitest';
import { normalize } from './normalize';
import { TTKClause, TTKTerm, mkConst, mkVar } from './kernel';

const mkCtor = (name: string, ...args: TTKTerm[]): TTKTerm =>
  args.reduce<TTKTerm>((fn, arg) => ({ tag: 'App', fn, arg }), mkConst(name));

describe('normalize', () => {
  test('ι-reduces match on constructor scrutinee', () => {
    const term: TTKTerm = {
      tag: 'Match',
      scrutinee: mkConst('Zero'),
      clauses: [
        {
          patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }],
          rhs: mkConst('True'),
        },
        {
          patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] }],
          rhs: mkConst('False'),
        },
      ],
    };

    expect(normalize(term)).toEqual(mkConst('True'));
  });

  test('substitutes pattern bindings into reduced clause rhs', () => {
    const term: TTKTerm = {
      tag: 'Match',
      scrutinee: mkCtor('Succ', mkConst('Zero')),
      clauses: [
        {
          patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }],
          rhs: mkConst('Impossible'),
        },
        {
          patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] }],
          rhs: mkVar(0),
        },
      ],
    };

    expect(normalize(term)).toEqual(mkConst('Zero'));
  });

  test('reduces nested constructor patterns with bindings in order', () => {
    const term: TTKTerm = {
      tag: 'Match',
      scrutinee: mkCtor('Pair', mkCtor('Succ', mkConst('Zero')), mkConst('True')),
      clauses: [
        {
          patterns: [{
            tag: 'PCtor',
            name: 'Pair',
            args: [
              { tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] },
              { tag: 'PVar', name: 'b' },
            ],
          }],
          rhs: mkCtor('Pair', mkVar(1), mkVar(0)),
        },
      ],
    };

    expect(normalize(term)).toEqual(mkCtor('Pair', mkConst('Zero'), mkConst('True')));
  });

  test('keeps match stuck when nested constructor arguments do not match', () => {
    const term: TTKTerm = {
      tag: 'Match',
      scrutinee: mkCtor('Pair', mkConst('Zero'), mkConst('True')),
      clauses: [
        {
          patterns: [{
            tag: 'PCtor',
            name: 'Pair',
            args: [
              { tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] },
              { tag: 'PWild', name: '_' },
            ],
          }],
          rhs: mkConst('Impossible'),
        },
      ],
    };

    expect(normalize(term)).toEqual(term);
  });

  test('keeps stuck matches when no clause matches', () => {
    const clauses: TTKClause[] = [{
      patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }],
      rhs: mkConst('True'),
    }];
    const term: TTKTerm = {
      tag: 'Match',
      scrutinee: mkCtor('Succ', mkConst('Zero')),
      clauses,
    };

    expect(normalize(term)).toEqual({
      tag: 'Match',
      scrutinee: mkCtor('Succ', mkConst('Zero')),
      clauses,
    });
  });
});
