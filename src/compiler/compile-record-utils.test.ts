import { describe, expect, test } from 'vitest';
import {
  addRecordCtorTypeElabMappings,
  buildRecordTypeFromParams,
  buildSurfaceConstructorType,
  extractZonkedFieldTypes,
} from './compile-record-utils';

describe('compile-record-utils', () => {
  test('buildSurfaceConstructorType threads params through the return type with correct de Bruijn indices', () => {
    const type = buildSurfaceConstructorType(
      [
        { name: 'A', type: { tag: 'Const', name: 'Type' } as any },
        { name: 'B', type: { tag: 'Const', name: 'Type' } as any },
      ],
      [
        { name: 'x', type: { tag: 'Const', name: 'A' } as any },
      ],
      'Pairish'
    ) as any;

    expect(type.tag).toBe('Binder');
    expect(type.body.tag).toBe('Binder');
    expect(type.body.body.tag).toBe('Binder');

    const returnType = type.body.body.body;
    expect(returnType.tag).toBe('App');
    expect(returnType.arg).toEqual({ tag: 'Var', index: 1 });
    expect(returnType.fn.tag).toBe('App');
    expect(returnType.fn.arg).toEqual({ tag: 'Var', index: 2 });
    expect(returnType.fn.fn).toEqual({ tag: 'Const', name: 'Pairish' });
  });

  test('extractZonkedFieldTypes skips params and preserves field metadata', () => {
    const ctorType = {
      tag: 'Binder',
      binderKind: { tag: 'BPi' },
      name: 'A',
      domain: { tag: 'Const', name: 'Type' },
      body: {
        tag: 'Binder',
        binderKind: { tag: 'BPi' },
        name: 'x',
        domain: { tag: 'Const', name: 'Nat' },
        body: {
          tag: 'Binder',
          binderKind: { tag: 'BPi' },
          name: 'y',
          domain: { tag: 'Const', name: 'Bool' },
          body: { tag: 'Const', name: 'MyRecord' },
        },
      },
    } as any;

    expect(extractZonkedFieldTypes(ctorType, 1, [
      { name: 'x', type: { tag: 'Const', name: 'OldX' } as any, implicit: false },
      { name: 'y', type: { tag: 'Const', name: 'OldY' } as any, implicit: true },
    ])).toEqual([
      { name: 'x', type: { tag: 'Const', name: 'Nat' }, implicit: false },
      { name: 'y', type: { tag: 'Const', name: 'Bool' }, implicit: true },
    ]);
  });

  test('addRecordCtorTypeElabMappings aligns constructor binder domains with params then fields', () => {
    const elabMap = new Map<string, string>();
    addRecordCtorTypeElabMappings(elabMap, 2, 2);

    expect(Array.from(elabMap.entries())).toEqual([
      ['constructors[0].type.domain', 'params[0].type'],
      ['constructors[0].type.body.domain', 'params[1].type'],
      ['constructors[0].type.body.body.domain', 'fields[0].type'],
      ['constructors[0].type.body.body.body.domain', 'fields[1].type'],
    ]);
  });

  test('buildRecordTypeFromParams nests kernel pis right-to-left', () => {
    const type = buildRecordTypeFromParams([
      { name: 'A', type: { tag: 'Const', name: 'Type' } as any, implicit: false },
      { name: 'x', type: { tag: 'Const', name: 'A' } as any, implicit: false },
    ], { tag: 'Sort', level: { tag: 'ULit', n: 0 } } as any) as any;

    expect(type.tag).toBe('Binder');
    expect(type.name).toBe('A');
    expect(type.body.tag).toBe('Binder');
    expect(type.body.name).toBe('x');
    expect(type.body.body.tag).toBe('Sort');
  });
});
