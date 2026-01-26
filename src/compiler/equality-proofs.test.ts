import { describe, test, expect } from 'vitest';
import { compileSource } from '../test-utils';

describe('equality proofs', () => {
  const equalityPreamble = `
inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a
`;

  test('sym: Equal u v -> Equal v u', () => {
    const source = `
${equalityPreamble}

sym : {A : Type} -> {u v : A} -> Equal u v -> Equal v u
sym refl = refl
`;
    const results = compileSource(source);
    const symResult = results.find(r => r.name === 'sym');

    if (!symResult?.checkSuccess) {
      console.log('sym errors:', symResult?.checkErrors);
    }
    expect(symResult?.checkSuccess).toBe(true);
  });

  test('trans: Equal u v -> Equal v w -> Equal u w', () => {
    const source = `
${equalityPreamble}

trans : {A : Type} -> {u v w : A} -> Equal u v -> Equal v w -> Equal u w
trans refl refl = refl
`;
    const results = compileSource(source);
    const transResult = results.find(r => r.name === 'trans');

    if (!transResult?.checkSuccess) {
      console.log('trans errors:', transResult?.checkErrors);
    }
    expect(transResult?.checkSuccess).toBe(true);
  });

  test('cong: Equal u v -> Equal (f u) (f v)', () => {
    const source = `
${equalityPreamble}

cong : {A B : Type} -> {u v : A} -> {f : A -> B} -> Equal u v -> Equal (f u) (f v)
cong refl = refl
`;
    const results = compileSource(source);
    const congResult = results.find(r => r.name === 'cong');

    if (!congResult?.checkSuccess) {
      console.log('cong errors:', congResult?.checkErrors);
    }
    expect(congResult?.checkSuccess).toBe(true);
  });

  test('replace: Equal x y -> f x -> f y', () => {
    const source = `
${equalityPreamble}

replace : {x y : Type} -> {f : Type -> Type} -> Equal x y -> f x -> f y
replace refl fx = fx
`;
    const results = compileSource(source);
    const replaceResult = results.find(r => r.name === 'replace');

    if (!replaceResult?.checkSuccess) {
      console.log('replace errors:', replaceResult?.checkErrors);
    }
    expect(replaceResult?.checkSuccess).toBe(true);
  });
});
