/**
 * Unit tests for context variable type lookup.
 *
 * These tests verify the correct behavior of looking up variable types
 * in contexts of varying lengths, which is critical for pattern matching
 * where contexts grow as patterns are processed.
 */
import { describe, test, expect } from 'vitest';
import { TCEnv } from './term';
import { mkVar, mkConst } from './kernel';
import type { TTKTerm } from '../types/tt-kernel';

// Helper to create an empty TCEnv for testing
function createEmptyEnv(): TCEnv<undefined> {
  return new TCEnv(
    [], // context
    new Map(), // definitions
    new Map(), // metaVars
    [], // constraints
    [], // indexPath
    [], // valueStack
    undefined, // value
    new Map(), // levelMetas
    { mode: 'infer' } // options
  );
}

describe('Context variable type lookup', () => {
  test('simple context: variable type does not need shifting', () => {
    // Context: [x : Nat]
    // Looking up x (index 0) should give type Nat (no shift needed)
    const env = createEmptyEnv()
      .extendTTKContext('x', mkConst('Nat'));

    const result = env.getTypeAtIndexInContextAssert(0);
    expect(result.value).toEqual(mkConst('Nat'));
  });

  test('two-level context: first variable type needs no shift', () => {
    // Context: [x : Nat, y : Bool]
    // Looking up y (index 0) should give type Bool (no shift)
    const env = createEmptyEnv()
      .extendTTKContext('x', mkConst('Nat'))
      .extendTTKContext('y', mkConst('Bool'));

    const result = env.getTypeAtIndexInContextAssert(0);
    expect(result.value).toEqual(mkConst('Bool'));
  });

  test('two-level context: second variable type needs no shift', () => {
    // Context: [x : Nat, y : Bool]
    // Looking up x (index 1) should give type Nat (no shift needed because Nat is a constant)
    const env = createEmptyEnv()
      .extendTTKContext('x', mkConst('Nat'))
      .extendTTKContext('y', mkConst('Bool'));

    const result = env.getTypeAtIndexInContextAssert(1);
    expect(result.value).toEqual(mkConst('Nat'));
  });

  test('dependent type: variable type with reference needs shifting', () => {
    // Context: [A : Type, x : A]
    // When x is added, its type is Var(0) (referring to A in context of length 1)
    // Later, looking up x (index 0) in context of length 2:
    //   - x is at position 1 in array [A, x]
    //   - x's stored type is Var(0)
    //   - We need to shift Var(0) to work in the current context
    //   - In current context, A is at index 1, so the type should be Var(1)
    const env = createEmptyEnv()
      .extendTTKContext('A', mkConst('Type'))
      .extendTTKContext('x', mkVar(0)); // Type references A

    const result = env.getTypeAtIndexInContextAssert(0);
    // The type Var(0) should be shifted to Var(1) because one binding (x) was added after A
    expect(result.value).toEqual(mkVar(1));
  });

  test('dependent type with three levels', () => {
    // Context: [A : Type, x : A, y : A]
    // When adding x to context [A], we use Var(0) to reference A
    // When adding y to context [A, x], we use Var(1) to reference A (because x is now at index 0)
    // Looking up x (index 1):
    //   - x is at position 1 in array [A, x, y]
    //   - x's stored type is Var(0) (referenced A when added to context [A])
    //   - Now A is at index 2, so type should be Var(2)
    const env = createEmptyEnv()
      .extendTTKContext('A', mkConst('Type'))
      .extendTTKContext('x', mkVar(0))  // In context [A], A is at index 0
      .extendTTKContext('y', mkVar(1)); // In context [A, x], A is at index 1

    const resultX = env.getTypeAtIndexInContextAssert(1);
    expect(resultX.value).toEqual(mkVar(2)); // x's type Var(0) shifted by 2

    const resultY = env.getTypeAtIndexInContextAssert(0);
    expect(resultY.value).toEqual(mkVar(2)); // y's type Var(1) shifted by 1
  });

  test('pattern matching scenario: record with implicit params', () => {
    // Simulating: record DPair (A : Type) (fn : A -> Type) where
    //              fst : A
    //              snd : fn fst
    // Context during pattern matching: [start, fn, _pad0, _pad1, count, fn0]
    // Where:
    //   - start : Nat
    //   - fn : Nat
    //   - _pad0 : Type (implicit param A)
    //   - _pad1 : _pad0 -> Type (implicit param fn, references _pad0)
    //   - count : _pad0 (explicit param fst, references _pad0)
    //   - fn0 : _pad1 count (explicit param snd, references _pad1 and count)

    let env = createEmptyEnv()
      .extendTTKContext('start', mkConst('Nat'))
      .extendTTKContext('fn', mkConst('Nat'));

    // Add _pad0 : Type
    env = env.extendTTKContext('_pad0', mkConst('Type'));

    // Add _pad1 : _pad0 -> Type
    // At this point, _pad0 is at index 0, so the type is Var(0) -> Type
    env = env.extendTTKContext('_pad1', {
      tag: 'Binder',
      name: '_',
      binderKind: { tag: 'BPi' },
      domain: mkVar(0), // _pad0
      body: mkConst('Type')
    });

    // Add count : _pad0
    // At this point, _pad0 is at index 1 (context: [start, fn, _pad0, _pad1])
    env = env.extendTTKContext('count', mkVar(1));

    // Now look up count (index 1) in the full context [start, fn, _pad0, _pad1, count, fn0]
    // We add fn0 first to match the failing test scenario
    env = env.extendTTKContext('fn0', mkConst('Nat')); // Simplified for now

    // Look up count's type (index 1)
    // count is at position 4 in [start, fn, _pad0, _pad1, count, fn0]
    // count's stored type is Var(1) (referenced _pad0 when count was added with context length 4)
    // Now _pad0 is at index 3 in the context of length 6
    // So the type should be shifted to Var(3)
    const resultCount = env.getTypeAtIndexInContextAssert(1);
    expect(resultCount.value).toEqual(mkVar(3));
  });
});
