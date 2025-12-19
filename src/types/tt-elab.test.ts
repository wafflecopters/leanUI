/**
 * Tests for TT Elaboration Layer
 *
 * Tests:
 * 1. elabToKernel - converting TT terms to TTK terms
 * 2. inlineExtension - inlining record extensions
 * 3. elabRecordFull - full record elaboration pipeline
 */

import { describe, it, expect } from 'bun:test';
import { mkType, mkPi, mkVar, type RecordDef } from './tt-core';
import {
  elabToKernel,
  inlineExtension,
  elabRecordToKernel,
  elabRecordFull,
  createRecordRegistry,
  RecordExtensionError,
} from './tt-elab';

const Type0 = mkType(0);
const Prop = mkType(0);

describe('elabToKernel', () => {
  it('should convert Var', () => {
    const tt = { tag: 'Var' as const, index: 0 };
    const ttk = elabToKernel(tt);
    expect(ttk.tag).toBe('Var');
    expect((ttk as any).index).toBe(0);
  });

  it('should convert Sort', () => {
    const tt = { tag: 'Sort' as const, level: 1 };
    const ttk = elabToKernel(tt);
    expect(ttk.tag).toBe('Sort');
    expect((ttk as any).level).toBe(1);
  });

  it('should convert Pi binders', () => {
    const tt = mkPi(Type0, Type0, 'A');
    const ttk = elabToKernel(tt);
    expect(ttk.tag).toBe('Binder');
    expect((ttk as any).binderKind.tag).toBe('BPi');
    expect((ttk as any).name).toBe('A');
  });

  it('should convert nested terms', () => {
    // Π (A : Type) → Π (x : A) → A
    const tt = mkPi(Type0, mkPi(mkVar(0), mkVar(1), 'x'), 'A');
    const ttk = elabToKernel(tt);
    expect(ttk.tag).toBe('Binder');
    expect((ttk as any).body.tag).toBe('Binder');
    expect((ttk as any).body.body.tag).toBe('Var');
  });
});

describe('inlineExtension', () => {
  // Helper to create an arrow type
  const mkArrow = (a: any, b: any) => mkPi(a, b, '_');

  // Create Magma record (with param A)
  const makeMagmaRecord = (): RecordDef => ({
    name: 'Magma',
    type: mkArrow(Type0, Type0),
    params: [{ name: 'A', type: Type0 }],
    fields: [
      {
        name: 'op',
        // op : A → A → A (in param context where A is at index 0)
        type: mkPi(mkVar(0), mkPi(mkVar(1), mkVar(2), '_'), '_'),
      },
    ],
  });

  // Create Semigroup record that extends Magma
  const makeSemigroupRecord = (): RecordDef => ({
    name: 'Semigroup',
    type: mkArrow(Type0, Type0),
    params: [{ name: 'A', type: Type0 }],
    extends: ['Magma'],
    fields: [
      {
        name: 'assoc',
        type: Prop,  // Simplified for tests
      },
    ],
  });

  // Create Monoid record that extends Semigroup
  const makeMonoidRecord = (): RecordDef => ({
    name: 'Monoid',
    type: mkArrow(Type0, Type0),
    params: [{ name: 'A', type: Type0 }],
    extends: ['Semigroup'],
    fields: [
      {
        name: 'e',
        type: mkVar(0),  // e : A (in param context)
      },
    ],
  });

  it('should return record unchanged if no extends', () => {
    const magma = makeMagmaRecord();
    const registry = createRecordRegistry([magma]);

    const result = inlineExtension(magma, registry);

    expect(result.name).toBe('Magma');
    expect(result.fields.length).toBe(1);
    expect(result.fields[0].name).toBe('op');
    expect(result.extends).toBeUndefined();
  });

  it('should inline parent fields for Semigroup extending Magma', () => {
    const magma = makeMagmaRecord();
    const semigroup = makeSemigroupRecord();
    const registry = createRecordRegistry([magma, semigroup]);

    const result = inlineExtension(semigroup, registry);

    expect(result.name).toBe('Semigroup');
    expect(result.fields.length).toBe(2); // op from Magma + assoc from Semigroup
    expect(result.fields[0].name).toBe('op'); // Inherited first
    expect(result.fields[1].name).toBe('assoc'); // Own field second
    expect(result.extends).toBeUndefined(); // Cleared after inlining
  });

  it('should inline grandparent fields for Monoid extending Semigroup extending Magma', () => {
    const magma = makeMagmaRecord();
    const semigroup = makeSemigroupRecord();
    const monoid = makeMonoidRecord();
    const registry = createRecordRegistry([magma, semigroup, monoid]);

    const result = inlineExtension(monoid, registry);

    expect(result.name).toBe('Monoid');
    expect(result.fields.length).toBe(3); // op, assoc, e
    expect(result.fields[0].name).toBe('op'); // From Magma
    expect(result.fields[1].name).toBe('assoc'); // From Semigroup
    expect(result.fields[2].name).toBe('e'); // Own field
  });

  it('should throw error for unknown parent', () => {
    const semigroup = makeSemigroupRecord(); // Extends Magma
    const registry = createRecordRegistry([]); // Empty - Magma not registered

    expect(() => inlineExtension(semigroup, registry)).toThrow(RecordExtensionError);
  });

  it('should throw error for field name clash', () => {
    const magma = makeMagmaRecord();
    // Create a record that extends Magma but has its own 'op' field
    const badRecord: RecordDef = {
      name: 'BadRecord',
      type: mkArrow(Type0, Type0),
      params: [{ name: 'A', type: Type0 }],
      extends: ['Magma'],
      fields: [
        {
          name: 'op', // Clash with Magma's op
          type: Prop,
        },
      ],
    };
    const registry = createRecordRegistry([magma, badRecord]);

    expect(() => inlineExtension(badRecord, registry)).toThrow(RecordExtensionError);
    expect(() => inlineExtension(badRecord, registry)).toThrow(/field name clash/);
  });
});

describe('elabRecordFull', () => {
  const mkArrow = (a: any, b: any) => mkPi(a, b, '_');

  it('should elaborate simple record to kernel', () => {
    const magma: RecordDef = {
      name: 'Magma',
      type: mkArrow(Type0, Type0),
      params: [{ name: 'A', type: Type0 }],
      fields: [
        {
          name: 'op',
          type: mkPi(mkVar(0), mkVar(1), '_'),  // A → A in param context
        },
      ],
    };
    const registry = createRecordRegistry([magma]);

    const result = elabRecordFull(magma, registry);

    expect(result.name).toBe('Magma');
    expect(result.fields.length).toBe(1);
    expect(result.fields[0].name).toBe('op');
    expect(result.type.tag).toBe('Binder');
    expect(result.params.length).toBe(1);
    expect(result.params[0].name).toBe('A');
  });

  it('should inline extensions and elaborate to kernel', () => {
    const magma: RecordDef = {
      name: 'Magma',
      type: mkArrow(Type0, Type0),
      params: [{ name: 'A', type: Type0 }],
      fields: [{ name: 'op', type: Prop }],
    };
    const semigroup: RecordDef = {
      name: 'Semigroup',
      type: mkArrow(Type0, Type0),
      params: [{ name: 'A', type: Type0 }],
      extends: ['Magma'],
      fields: [{ name: 'assoc', type: Prop }],
    };
    const registry = createRecordRegistry([magma, semigroup]);

    const result = elabRecordFull(semigroup, registry);

    expect(result.name).toBe('Semigroup');
    expect(result.fields.length).toBe(2);
    expect(result.fields[0].name).toBe('op'); // Inlined from Magma
    expect(result.fields[1].name).toBe('assoc');
    expect(result.params.length).toBe(1);
  });

  it('should throw if trying to elaborate record with extends not inlined', () => {
    const semigroup: RecordDef = {
      name: 'Semigroup',
      type: mkArrow(Type0, Type0),
      params: [{ name: 'A', type: Type0 }],
      extends: ['Magma'],
      fields: [{ name: 'assoc', type: Prop }],
    };

    // Directly call elabRecordToKernel without inlining - should fail
    expect(() => elabRecordToKernel(semigroup)).toThrow();
  });
});

