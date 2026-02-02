import { describe, test } from 'vitest';
import { compileTTFromText } from './compile';

describe('WeakK debugging', () => {
  test('WeakK with K - debug the type error', () => {
    const source = `@assumeK=true

inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a

weakK : (A : Type) -> (a : A) -> (P : Equal (refl {A} {a}) (refl {A} {a}) -> Type) -> (p : P (refl {A:=Equal a a} {a:=refl {A} {a}})) -> (e : Equal (refl {A} {a}) (refl {A} {a})) -> P e
weakK A a P p refl = p
`;

    const result = compileTTFromText(source);
    const weakKDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'weakK');

    console.log('\n=== WEAKK WITH K - FULL DEBUG ===');
    console.log('checkSuccess:', weakKDecl?.checkSuccess);

    if (weakKDecl?.checkErrors) {
      console.log('\nErrors:');
      weakKDecl.checkErrors.forEach((e: any, i: number) => {
        console.log(`\nError ${i + 1}:`);
        console.log('  Message:', e.message);

        // Try to get more context
        if (e.env) {
          console.log('  Context length:', e.env.context?.length);
          console.log('  Context:', e.env.context?.slice(0, 10));
        }
      });
    }

    // Print the kernel clause if available
    if (weakKDecl?.kernelClauses) {
      console.log('\nKernel clauses:', weakKDecl.kernelClauses.length);
      console.log('First clause:', JSON.stringify(weakKDecl.kernelClauses[0], null, 2).slice(0, 500));
    }
  });

  test('Simpler test - just the pattern match structure', () => {
    const source = `
inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a

-- Simplest case: match refl against Equal (refl {A} {a}) (refl {A} {a})
test : (A : Type) -> (a : A) -> (e : Equal (refl {A} {a}) (refl {A} {a})) -> Equal (refl {A} {a}) (refl {A} {a})
test A a refl = refl
`;

    const result = compileTTFromText(source);
    const testDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'test');

    console.log('\n=== SIMPLE TEST ===');
    console.log('checkSuccess:', testDecl?.checkSuccess);

    if (!testDecl?.checkSuccess && testDecl?.checkErrors) {
      console.log('Error:', testDecl.checkErrors[0]?.message);
    }
  });
});
