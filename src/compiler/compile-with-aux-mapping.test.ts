import { describe, expect, test } from 'vitest';
import {
  mergeAuxTypeInfoIntoMain,
  remapWithClauseElabMap,
  remapWithScrutineeInMainElabMap,
} from './compile-with-aux-mapping';
import type { CompiledDeclaration } from './compile';

function emptyCompiledDeclaration(): CompiledDeclaration {
  return {
    name: 'test',
    kind: 'term',
    checkSuccess: true,
    checkErrors: [],
    elabMap: new Map(),
    sourceMap: new Map(),
  };
}

describe('compile-with-aux-mapping', () => {
  test('remapWithClauseElabMap offsets with-pattern indices and scrutinee rhs paths', () => {
    const compiled = {
      ...emptyCompiledDeclaration(),
      kernelValue: {
        tag: 'Match',
        scrutinee: { tag: 'Hole', id: '_scrutinee' },
        clauses: [{ patterns: [{ tag: 'PVar', name: 'x' }, { tag: 'PVar', name: 'y' }], rhs: { tag: 'Var', index: 0 } }],
      } as any,
      surfaceValue: {
        tag: 'Match',
        scrutinee: { tag: 'Const', name: 'x' },
        clauses: [{ patterns: [{ tag: 'PVar', name: 'x' }, { tag: 'PVar', name: 'y' }], rhs: { tag: 'Const', name: 'rhs' } }],
      } as any,
    };
    const sourceMap = new Map<string, any>([
      ['value.clauses[0].withClauses[0].patterns[0]', {}],
      ['value.clauses[0].withClauses[0].rhs.scrutinee.fn', {}],
    ]);

    remapWithClauseElabMap(compiled, sourceMap, 1, 1);

    expect(compiled.elabMap?.get('value.clauses[0].patterns[1]')).toBe('value.clauses[0].withClauses[0].patterns[0]');
    expect(compiled.elabMap?.get('value.clauses[0].rhs.arg.fn')).toBe('value.clauses[0].withClauses[0].rhs.scrutinee.fn');
  });

  test('remapWithScrutineeInMainElabMap maps direct scrutinees to rhs arg paths', () => {
    const compiled = emptyCompiledDeclaration();
    const sourceMap = new Map<string, any>([
      ['value.clauses[1].scrutinee', {}],
      ['value.clauses[1].scrutinee.fn', {}],
      ['value.clauses[1].withClauses[0].rhs.scrutinee', {}],
    ]);

    remapWithScrutineeInMainElabMap(compiled, sourceMap);

    expect(compiled.elabMap?.get('value.clauses[1].rhs.arg')).toBe('value.clauses[1].scrutinee');
    expect(compiled.elabMap?.get('value.clauses[1].rhs.arg.fn')).toBe('value.clauses[1].scrutinee.fn');
    expect(compiled.elabMap?.has('value.clauses[1].withClauses[0].rhs.arg')).toBe(false);
  });

  test('mergeAuxTypeInfoIntoMain lifts mapped descendants onto surface paths', () => {
    const mainCompiled = {
      ...emptyCompiledDeclaration(),
      typeInfoMap: new Map(),
    };
    const auxCompiled = {
      ...emptyCompiledDeclaration(),
      elabMap: new Map([
        ['value.clauses[0].rhs', 'value.clauses[2].withClauses[0].rhs'],
      ]),
      typeInfoMap: new Map([
        ['value.clauses[0].rhs.fn', { kernelPath: 'value.clauses[0].rhs.fn', type: { tag: 'Const', name: 'Nat' } }],
      ]),
    };

    mergeAuxTypeInfoIntoMain(mainCompiled, auxCompiled as any);

    expect(mainCompiled.typeInfoMap?.get('value.clauses[2].withClauses[0].rhs.fn')).toMatchObject({
      kernelPath: 'value.clauses[2].withClauses[0].rhs.fn',
    });
  });
});
