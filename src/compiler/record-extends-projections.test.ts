import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Record extends projection types', () => {
  test('inherited field projections should have proper types (no unsolved metas)', () => {
    const source = `
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

record Semigroup (A : Type) where
  op : A -> A -> A
  assoc : (a b c : A) -> Equal (op (op a b) c) (op a (op b c))
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const semigroupDecl = allDecls.find((d: any) => d?.name === 'Semigroup');
    expect(semigroupDecl?.checkSuccess).toBe(true);

    // Check that projections don't have unsolved metas
    const projections = semigroupDecl?.prettyProjections || [];
    console.log('Semigroup projections:', projections);

    for (const proj of projections) {
      // Should not contain ?_implicit or similar unsolved metas
      expect(proj.prettyType).not.toMatch(/\?_implicit/);
      expect(proj.prettyType).not.toMatch(/\?_/);
      // Should not contain weird de Bruijn indices like #2, #3
      expect(proj.prettyType).not.toMatch(/#\d+/);
    }
  });

  test('record extends should have proper projection types', () => {
    const source = `
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

record Semigroup (A : Type) where
  op : A -> A -> A
  assoc : (a b c : A) -> Equal (op (op a b) c) (op a (op b c))

record Monoid (A : Type) extends Semigroup A where
  e : A
  identLeft : (a : A) -> Equal (op e a) a
  identRight : (a : A) -> Equal (op a e) a
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const monoidDecl = allDecls.find((d: any) => d?.name === 'Monoid');
    expect(monoidDecl?.checkSuccess).toBe(true);

    // Check that projections don't have unsolved metas
    const projections = monoidDecl?.prettyProjections || [];
    console.log('Monoid projections:', projections);

    for (const proj of projections) {
      // Should not contain ?_implicit or similar unsolved metas
      expect(proj.prettyType).not.toMatch(/\?_implicit/);
      expect(proj.prettyType).not.toMatch(/\?_/);
      // Should not contain weird de Bruijn indices like #2, #3
      expect(proj.prettyType).not.toMatch(/#\d+/);
    }
  });
});
