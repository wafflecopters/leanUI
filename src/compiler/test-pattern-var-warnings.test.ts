/**
 * Test warnings for pattern variables that unify to known values
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Pattern variable concrete value warnings', () => {
  test('warns when pattern var unifies to Zero', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {b : Nat} -> Leq Zero b
  LeqSucc : {a b : Nat} -> Leq a b -> Leq (Succ a) (Succ b)

-- Pattern variable 'a' unifies to Zero via LeqZero constructor
test1 : (a b : Nat) -> Leq a b -> Nat
test1 a b LeqZero = a
`;

    const result = compileTTFromText(source);
    const decl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'test1');

    expect(decl).toBeDefined();
    expect(decl!.checkErrors.length).toBeGreaterThan(0);

    const warning = decl!.checkErrors.find(e =>
      e.message.includes('Warning') &&
      e.message.includes("Pattern variable 'a'") &&
      e.message.includes('Zero')
    );

    expect(warning).toBeDefined();
    expect(warning!.message).toContain("Pattern variable 'a' is constrained to be 'Zero'");
    expect(warning!.message).toContain("Consider replacing 'a' with 'Zero'");
  });

  // Note: We don't warn when variables unify to each other (e.g., via refl : Equal a a)
  // because there's no concrete constructor to suggest. The variables just become aliases
  // for the same flexible parameter.

  test('warns when pattern var unifies to Succ', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {b : Nat} -> Leq Zero b
  LeqSucc : {a b : Nat} -> Leq a b -> Leq (Succ a) (Succ b)

-- Pattern variable 'a' unifies to Succ x via LeqSucc
test3 : (a b : Nat) -> Leq a b -> Nat
test3 a b (LeqSucc s) = a
`;

    const result = compileTTFromText(source);
    const decl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'test3');

    expect(decl).toBeDefined();

    const warning = decl!.checkErrors.find(e =>
      e.message.includes('Warning') &&
      e.message.includes("Pattern variable 'a'") &&
      e.message.includes('Succ')
    );

    expect(warning).toBeDefined();
  });

  test('no warning when pattern var remains flexible', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {b : Nat} -> Leq Zero b
  LeqSucc : {a b : Nat} -> Leq a b -> Leq (Succ a) (Succ b)

-- Pattern variable 'b' remains flexible (not constrained by LeqZero)
test4 : (a b : Nat) -> Leq a b -> Nat
test4 a b LeqZero = b
`;

    const result = compileTTFromText(source);
    const decl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'test4');

    expect(decl).toBeDefined();

    // Should have warning for 'a' but NOT for 'b'
    const warningForB = decl!.checkErrors.find(e =>
      e.message.includes('Warning') &&
      e.message.includes("Pattern variable 'b'")
    );

    expect(warningForB).toBeUndefined();
  });

  test('warns for Bool constructors', () => {
    const source = `
inductive Bool : Type where
  True : Bool
  False : Bool

inductive EqBool : Bool -> Type where
  IsTrue : EqBool True
  IsFalse : EqBool False

-- Pattern variable 'x' unifies to True
test5 : (x : Bool) -> EqBool x -> Bool
test5 x IsTrue = x
`;

    const result = compileTTFromText(source);
    const decl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'test5');

    expect(decl).toBeDefined();

    const warning = decl!.checkErrors.find(e =>
      e.message.includes('Warning') &&
      e.message.includes("Pattern variable 'x'") &&
      e.message.includes('True')
    );

    expect(warning).toBeDefined();
  });

  test('no warning when using concrete pattern already', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {b : Nat} -> Leq Zero b
  LeqSucc : {a b : Nat} -> Leq a b -> Leq (Succ a) (Succ b)

-- Already using concrete pattern Zero - no warning needed
test6 : (b : Nat) -> Leq Zero b -> Nat
test6 b LeqZero = Zero
`;

    const result = compileTTFromText(source);
    const decl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'test6');

    expect(decl).toBeDefined();

    // Should not have pattern variable warnings since we already used concrete pattern
    const varWarnings = decl!.checkErrors.filter(e =>
      e.message.includes('Warning') &&
      e.message.includes('Pattern variable')
    );

    expect(varWarnings.length).toBe(0);
  });

  test('warns for multiple clauses independently', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {b : Nat} -> Leq Zero b
  LeqSucc : {a b : Nat} -> Leq a b -> Leq (Succ a) (Succ b)

-- First clause: 'a' unifies to Zero
-- Second clause: 'a' unifies to Succ
test7 : (a b : Nat) -> Leq a b -> Nat
test7 a b LeqZero = a
test7 a b (LeqSucc s) = b
`;

    const result = compileTTFromText(source);
    const decl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'test7');

    expect(decl).toBeDefined();

    // Should have warnings for both clauses
    const warnings = decl!.checkErrors.filter(e =>
      e.message.includes('Warning') &&
      e.message.includes("Pattern variable 'a'")
    );

    // At least one warning (could be two, one per clause)
    expect(warnings.length).toBeGreaterThan(0);
  });

  test('warns with nested constructors', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Vec : Nat -> Type where
  VNil : Vec Zero
  VCons : {n : Nat} -> Nat -> Vec n -> Vec (Succ n)

-- Pattern variable 'n' unifies to Zero via VNil
test8 : (n : Nat) -> Vec n -> Nat
test8 n VNil = n
`;

    const result = compileTTFromText(source);
    const decl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'test8');

    expect(decl).toBeDefined();

    const warning = decl!.checkErrors.find(e =>
      e.message.includes('Warning') &&
      e.message.includes("Pattern variable 'n'") &&
      e.message.includes('Zero')
    );

    expect(warning).toBeDefined();
  });
});
