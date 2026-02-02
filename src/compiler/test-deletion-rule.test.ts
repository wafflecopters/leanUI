import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Deletion rule (axiom K) checking', () => {
  test('weakK should fail without axiom K', () => {
    const source = `
inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a

weakK : (A : Type) -> (a : A) -> (P : Equal (refl {A} {a}) (refl {A} {a}) -> Type) -> (p : P (refl {A:=Equal a a} {a:=refl {A} {a}})) -> (e : Equal (refl {A} {a}) (refl {A} {a})) -> P e
weakK A a P p refl = p
`;

    const result = compileTTFromText(source, { assumeK: false });
    const weakKDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'weakK');

    console.log('\n=== WEAKK WITHOUT K ===');
    console.log('checkSuccess:', weakKDecl?.checkSuccess);

    if (weakKDecl?.checkErrors) {
      console.log('Errors:', weakKDecl.checkErrors.map((e: any) => e.message));
    }

    // Should fail with deletion rule error
    expect(weakKDecl?.checkSuccess).toBe(false);
    const hasKError = weakKDecl?.checkErrors?.some((e: any) =>
      e.message.includes('axiom K') || e.message.includes('deletion rule')
    );
    expect(hasKError).toBe(true);
  });

  test('weakK should succeed with axiom K', () => {
    const source = `
inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a

weakK : (A : Type) -> (a : A) -> (P : Equal (refl {A} {a}) (refl {A} {a}) -> Type) -> (p : P (refl {A:=Equal a a} {a:=refl {A} {a}})) -> (e : Equal (refl {A} {a}) (refl {A} {a})) -> P e
weakK A a P p refl = p
`;

    const result = compileTTFromText(source, { assumeK: true });
    const weakKDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'weakK');

    expect(weakKDecl?.checkSuccess).toBe(true);
  });
});
