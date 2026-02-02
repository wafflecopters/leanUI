import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Elaboration printing', () => {
  test('Universe level variables should be printed correctly', () => {
    const source = `
inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a
`;

    const result = compileTTFromText(source);
    const equalDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'Equal');

    expect(equalDecl?.checkSuccess).toBe(true);

    // Get the elaborated type and constructor type as strings
    const elabTypeStr = equalDecl?.elabType || '';
    const reflCtor = equalDecl?.kernelConstructors?.find((c: any) => c.name === 'refl');
    const reflTypeStr = reflCtor?.type || '';

    console.log('\n=== ELABORATION PRINTING TEST ===');
    console.log('Type:', elabTypeStr);
    console.log('refl:', reflTypeStr);

    // The type should contain "Type u", not "Type #0"
    expect(elabTypeStr).toContain('Type u');
    expect(elabTypeStr).not.toContain('Type #0');

    // The constructor type should also contain "Type u", not "Type #0"
    expect(reflTypeStr).toContain('Type u');
    expect(reflTypeStr).not.toContain('Type #0');
  });

  test('Multiple universe level variables should be printed correctly', () => {
    const source = `
inductive DPair : {u : ULevel} -> {v : ULevel} -> {A : Type u} -> (A -> Type v) -> Type where
  MkDPair : {u : ULevel} -> {v : ULevel} -> {A : Type u} -> {B : A -> Type v} -> (a : A) -> (b : B a) -> DPair B
`;

    const result = compileTTFromText(source);
    const dpairDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'DPair');

    expect(dpairDecl?.checkSuccess).toBe(true);

    const elabTypeStr = dpairDecl?.elabType || '';
    const ctorTypeStr = dpairDecl?.kernelConstructors?.[0]?.type || '';

    console.log('\n=== MULTIPLE ULEVEL PRINTING TEST ===');
    console.log('Type:', elabTypeStr);
    console.log('MkDPair:', ctorTypeStr);

    // Should contain both "Type u" and "Type v", not "#0" or "#1"
    expect(elabTypeStr).toContain('Type u');
    expect(elabTypeStr).toContain('Type v');
    expect(elabTypeStr).not.toContain('Type #0');
    expect(elabTypeStr).not.toContain('Type #1');

    expect(ctorTypeStr).toContain('Type u');
    expect(ctorTypeStr).toContain('Type v');
    expect(ctorTypeStr).not.toContain('Type #0');
    expect(ctorTypeStr).not.toContain('Type #1');
  });
});
