import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('WeakK with universe levels', () => {
  test('WeakK with universe-polymorphic refl (FAILS)', () => {
    const source = `
inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a

weakK : {A : Type} -> {a : A} -> (P : Equal {A:=Equal {A} a a} (refl {A} {a}) (refl {A} {a}) -> Type) -> (p : P (refl {A:=Equal {A} a a} {a:=refl {A} {a}})) -> (e : Equal {A:=Equal {A} a a} (refl {A} {a}) (refl {A} {a})) -> P e
weakK P p (refl {A:=x} {a:=y}) = p
`;

    const result = compileTTFromText(source, { assumeK: true });
    const weakKDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'weakK');

    console.log('\n=== WEAKK WITH ULEVEL ===');
    console.log('checkSuccess:', weakKDecl?.checkSuccess);

    if (!weakKDecl?.checkSuccess && weakKDecl?.checkErrors) {
      console.log('Error:', weakKDecl.checkErrors[0]?.message);
    }

    expect(weakKDecl?.checkSuccess).toBe(true);
  });

  test('WeakK with non-polymorphic refl (WORKS)', () => {
    const source = `
inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

weakK : {A : Type} -> {a : A} -> (P : Equal {A:=Equal {A} a a} (refl {A} {a}) (refl {A} {a}) -> Type) -> (p : P (refl {A:=Equal {A} a a} {a:=refl {A} {a}})) -> (e : Equal {A:=Equal {A} a a} (refl {A} {a}) (refl {A} {a})) -> P e
weakK P p (refl {A:=x} {a:=y}) = p
`;

    const result = compileTTFromText(source, { assumeK: true });
    const weakKDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'weakK');

    console.log('\n=== WEAKK WITHOUT ULEVEL ===');
    console.log('checkSuccess:', weakKDecl?.checkSuccess);

    if (!weakKDecl?.checkSuccess && weakKDecl?.checkErrors) {
      console.log('Error:', weakKDecl.checkErrors[0]?.message);
    }

    expect(weakKDecl?.checkSuccess).toBe(true);
  });

  test('WeakK WITH explicit universe params (zonk recheck)', () => {
    const source = `@assumeK=true

inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a

weakK : {u : ULevel} -> {A : Type u} -> {a : A} -> (P : Equal {A:=Equal {A} a a} (refl {A} {a}) (refl {A} {a}) -> Type) -> (p : P (refl {A:=Equal {A} a a} {a:=refl {A} {a}})) -> (e : Equal {A:=Equal {A} a a} (refl {A} {a}) (refl {A} {a})) -> P e
weakK P p (refl {A:=x} {a:=y}) = p
`;

    const result = compileTTFromText(source, { recheckZonkedTerms: true });
    const weakKDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'weakK');

    console.log('\n=== WEAKK WITH EXPLICIT U (ZONK RECHECK) ===');
    console.log('checkSuccess:', weakKDecl?.checkSuccess);

    if (!weakKDecl?.checkSuccess && weakKDecl?.checkErrors) {
      console.log('Errors:', weakKDecl.checkErrors.map((e: any) => e.message));
    }

    expect(weakKDecl?.checkSuccess).toBe(true);
  });
});
