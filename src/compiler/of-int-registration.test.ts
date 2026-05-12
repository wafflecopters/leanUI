/**
 * Tests for the @ofInt registry — the third leg of the literal coercion
 * protocol (NatLit/@ofNat, IntLit-shaped/@ofInt, RatLit/@ofRat). The
 * preset declares a function `T -> Int -> ...` as @ofInt and the
 * compiler records the return-type head → fn-name mapping in
 * `definitions.ofIntByTargetHead`.
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

const COMMON_PREAMBLE = `
@syntax @impl=nat
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

@syntax @impl=int
inductive Int : Type where
  IntOfNat   : Nat -> Int
  IntNegSucc : Nat -> Int

inductive Foo : Type where
  MkFoo : Foo
`;

describe('@ofInt registration', () => {
  test('records target-type head → coercion-fn name in ofIntByTargetHead', () => {
    const r = compileTTFromText(COMMON_PREAMBLE + `
@syntax @ofInt
fooOfInt : Int -> Foo
fooOfInt _ = MkFoo
`);
    expect(r.success).toBe(true);
    const defs = r.definitions;
    expect(defs.ofIntByTargetHead?.get('Foo')).toBe('fooOfInt');
  });

  test('Pi-parameterized @ofInt registers under the return-type head', () => {
    const r = compileTTFromText(COMMON_PREAMBLE + `
inductive Wrap : Type -> Type where
  MkWrap : (A : Type) -> Wrap A

@syntax @ofInt
wrapOfInt : (A : Type) -> Int -> Wrap A
wrapOfInt A _ = MkWrap A
`);
    expect(r.success).toBe(true);
    const defs = r.definitions;
    expect(defs.ofIntByTargetHead?.get('Wrap')).toBe('wrapOfInt');
  });

  test('rejects @ofInt when the literal-position argument is not an @impl=int type', () => {
    // PlainInt has no @impl=int annotation — registration should fail.
    const r = compileTTFromText(`
@syntax @impl=nat
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive PlainInt : Type where
  MkPlainInt : Nat -> PlainInt

inductive Foo : Type where
  MkFoo : Foo

@syntax @ofInt
fooOfInt : PlainInt -> Foo
fooOfInt _ = MkFoo
`);
    // Compilation still succeeds (the function type-checks fine), but
    // registration emits a warning and the registry stays unset.
    expect(r.success).toBe(true);
    expect(r.definitions.ofIntByTargetHead?.get('Foo')).toBeUndefined();
  });
});
