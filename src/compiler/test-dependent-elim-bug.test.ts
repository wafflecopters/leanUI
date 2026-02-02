import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Dependent elimination with constructor implicits', () => {
  test('Simple dependent elimination - Equal (refl {A} {a}) (refl {A} {a})', () => {
    const source = `
inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a

-- Pattern: e : Equal (refl {A} {a}) (refl {A} {a})
-- Return type: Equal (refl {A} {a}) (refl {A} {a})
-- After matching 'refl', we substitute e with 'refl' (with implicits!)
-- Expected return type: Equal (refl {?u} {?A} {?a}) (refl {?u} {?A} {?a})

test : (A : Type) -> (a : A) -> (e : Equal (refl {A} {a}) (refl {A} {a})) -> Equal (refl {A} {a}) (refl {A} {a})
test A a refl = refl
`;

    const result = compileTTFromText(source);
    const testDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'test');

    console.log('\n=== DEPENDENT ELIM TEST ===');
    console.log('checkSuccess:', testDecl?.checkSuccess);

    if (!testDecl?.checkSuccess && testDecl?.checkErrors) {
      console.log('Error:', testDecl.checkErrors[0]?.message);
    }

    expect(testDecl?.checkSuccess).toBe(true);
  });

  test('WeakK - dependent elimination with dependent return type', () => {
    const source = `
inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a

-- Pattern: e : Equal (refl {A} {a}) (refl {A} {a})
-- Return type: P e
-- After matching 'refl', substitute e with 'refl' (with implicits!)
-- Expected return type: P (refl {?u} {?A} {?a})

weakK : (A : Type) -> (a : A) -> (P : Equal (refl {A} {a}) (refl {A} {a}) -> Type) -> (p : P (refl {A:=Equal a a} {a:=refl {A} {a}})) -> (e : Equal (refl {A} {a}) (refl {A} {a})) -> P e
weakK A a P p refl = p
`;

    const result = compileTTFromText(source);
    const weakKDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'weakK');

    console.log('\n=== WEAKK TEST ===');
    console.log('checkSuccess:', weakKDecl?.checkSuccess);

    if (!weakKDecl?.checkSuccess && weakKDecl?.checkErrors) {
      console.log('Error:', weakKDecl.checkErrors[0]?.message);
    }

    expect(weakKDecl?.checkSuccess).toBe(true);
  });
});
