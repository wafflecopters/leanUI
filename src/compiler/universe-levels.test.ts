import { describe, test, expect } from 'vitest';
import { compileSource } from '../test-utils';

describe('undefined identifier in type level', () => {
  test('Universe polymorphic Equal with {u : ULevel} should parse u as Var', () => {
    const source = `
inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a
`;
    const results = compileSource(source);
    // The key test: u should be parsed as Var (bound), not Const
    const surfaceType = results[0]?.declarations?.[0]?.surfaceType;
    const aBinderDomain = (surfaceType as any)?.body?.domain;
    expect(aBinderDomain?.tag).toBe('Sort');
    expect(aBinderDomain?.level?.arg?.tag).toBe('Var');
    expect(aBinderDomain?.level?.arg?.index).toBe(0);
  });
});
