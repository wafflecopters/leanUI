import { describe, test, expect } from 'vitest';
import { compileSource } from '../test-utils';

describe('unannotated lambda inference', () => {
  test('identity function applied to Zero', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

fox : Nat
fox = (\\x => x) Zero
`;
    const results = compileSource(source);
    const foxResult = results.find(r => r.name === 'fox');

    if (!foxResult?.checkSuccess) {
      console.log('fox errors:', foxResult?.checkErrors?.map(e => e.message));
    }
    expect(foxResult?.checkSuccess).toBe(true);
  });

  test('identity function applied to Bool', () => {
    const source = `
inductive Bool : Type where
  True : Bool
  False : Bool

bar : Bool
bar = (\\x => x) True
`;
    const results = compileSource(source);
    const barResult = results.find(r => r.name === 'bar');

    if (!barResult?.checkSuccess) {
      console.log('bar errors:', barResult?.checkErrors?.map(e => e.message));
    }
    expect(barResult?.checkSuccess).toBe(true);
  });

  test('const function with unannotated lambda', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

baz : Nat
baz = (\\x => \\y => x) Zero (Succ Zero)
`;
    const results = compileSource(source);
    const bazResult = results.find(r => r.name === 'baz');

    if (!bazResult?.checkSuccess) {
      console.log('baz errors:', bazResult?.checkErrors?.map(e => e.message));
    }
    expect(bazResult?.checkSuccess).toBe(true);
  });
});
