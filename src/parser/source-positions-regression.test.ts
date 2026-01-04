/**
 * Regression tests for source position tracking
 *
 * These tests ensure that error locations are precise and don't regress.
 */

import { checkSourceBlocks } from './block-checker';

function assert(condition: boolean, message: string): void {
  if (!condition) {
    throw new Error(`Assertion failed: ${message}`);
  }
}

function test(name: string, fn: () => void): void {
  try {
    fn();
    console.log(`✓ ${name}`);
  } catch (e) {
    console.error(`✗ ${name}`);
    throw e;
  }
}

// ============================================================================
// Arrow Type Position Tracking
// ============================================================================

test('Error on domain of arrow type points to domain, not body', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Na -> Nat`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(!results[0].nameResolutionSuccess, 'Should have name resolution error');
  assert(results[0].nameResolutionErrors.length === 1, 'Should have 1 error');

  const error = results[0].nameResolutionErrors[0];
  assert(error.error.symbolName === 'Na', 'Error should be for Na');
  assert(error.location !== null, 'Error should have location');

  if (error.location) {
    // Line 3 is "  Succ : Na -> Nat"
    // Col 10 is the start of "Na"
    assert(error.location.start.line === 3, `Expected line 3, got ${error.location.start.line}`);
    assert(error.location.start.col === 10, `Expected col 10, got ${error.location.start.col}`);
  }
});

test('Error on body of arrow type points to body, not domain', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Na`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(!results[0].nameResolutionSuccess, 'Should have name resolution error');
  assert(results[0].nameResolutionErrors.length === 1, 'Should have 1 error');

  const error = results[0].nameResolutionErrors[0];
  assert(error.error.symbolName === 'Na', 'Error should be for Na');
  assert(error.location !== null, 'Error should have location');

  if (error.location) {
    // Line 3 is "  Succ : Nat -> Na"
    // Col 17 is the start of "Na" (after "-> ")
    assert(error.location.start.line === 3, `Expected line 3, got ${error.location.start.line}`);
    assert(error.location.start.col === 17, `Expected col 17, got ${error.location.start.col}`);
  }
});

test('Error in nested arrow type points to correct position', () => {
  const source = `f : Na -> Nat -> Nat`;

  const results = checkSourceBlocks(source);

  assert(results.length === 1, 'Should have 1 block');
  assert(!results[0].nameResolutionSuccess, 'Should have name resolution error');

  const errors = results[0].nameResolutionErrors;
  const naError = errors.find(e => e.error.symbolName === 'Na');
  const natErrors = errors.filter(e => e.error.symbolName === 'Nat');

  assert(naError !== undefined, 'Should have error for Na');
  assert(natErrors.length === 2, 'Should have 2 errors for Nat');

  if (naError && naError.location) {
    // "f : Na -> Nat -> Nat"
    // Col 5 is the start of "Na"
    assert(naError.location.start.line === 1, `Expected line 1, got ${naError.location.start.line}`);
    assert(naError.location.start.col === 5, `Expected col 5, got ${naError.location.start.col}`);
  }
});

// ============================================================================
// Type Signature vs Pattern Clause Position Tracking
// ============================================================================

test('Error in type signature points to signature, not pattern clauses', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Na
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

  const results = checkSourceBlocks(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].nameResolutionSuccess === true, 'Nat block should succeed');
  assert(results[1].nameResolutionSuccess === false, 'plus block should fail');

  const error = results[1].nameResolutionErrors[0];
  assert(error.error.symbolName === 'Na', 'Error should be for Na');
  assert(error.location !== null, 'Error should have location');

  if (error.location) {
    // Line 5 is "plus : Nat -> Nat -> Na" (line 4 is blank)
    // Col 22 is the start of "Na"
    assert(error.location.start.line === 5, `Expected line 5, got ${error.location.start.line}`);
    assert(error.location.start.col === 22, `Expected col 22, got ${error.location.start.col}`);
  }
});

test('Error in first argument of type signature', () => {
  const source = `plus : Na -> Nat -> Nat`;

  const results = checkSourceBlocks(source);

  const error = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'Na');
  assert(error !== undefined, 'Should have error for Na');

  if (error && error.location) {
    // "plus : Na -> Nat -> Nat"
    // Col 8 is the start of "Na"
    assert(error.location.start.line === 1, `Expected line 1, got ${error.location.start.line}`);
    assert(error.location.start.col === 8, `Expected col 8, got ${error.location.start.col}`);
  }
});

test('Error in second argument of type signature', () => {
  const source = `plus : Nat -> Na -> Nat`;

  const results = checkSourceBlocks(source);

  const error = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'Na');
  assert(error !== undefined, 'Should have error for Na');

  if (error && error.location) {
    // "plus : Nat -> Na -> Nat"
    // Col 15 is the start of "Na"
    assert(error.location.start.line === 1, `Expected line 1, got ${error.location.start.line}`);
    assert(error.location.start.col === 15, `Expected col 15, got ${error.location.start.col}`);
  }
});

test('Error in return type of type signature', () => {
  const source = `plus : Nat -> Nat -> Na`;

  const results = checkSourceBlocks(source);

  const error = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'Na');
  assert(error !== undefined, 'Should have error for Na');

  if (error && error.location) {
    // "plus : Nat -> Nat -> Na"
    // Col 22 is the start of "Na"
    assert(error.location.start.line === 1, `Expected line 1, got ${error.location.start.line}`);
    assert(error.location.start.col === 22, `Expected col 22, got ${error.location.start.col}`);
  }
});

// ============================================================================
// Inductive Type Signature Position Tracking
// ============================================================================

test('Error in inductive type signature points to correct symbol', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Vec : Na -> Type where
  VNil : Vec Zero`;

  const results = checkSourceBlocks(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].nameResolutionSuccess === true, 'Nat block should succeed');
  assert(results[1].nameResolutionSuccess === false, 'Vec block should fail');

  const naError = results[1].nameResolutionErrors.find(e => e.error.symbolName === 'Na');
  assert(naError !== undefined, 'Should have error for Na');

  if (naError && naError.location) {
    // Line 5 is "inductive Vec : Na -> Type where"
    // Col 17 is the start of "Na"
    assert(naError.location.start.line === 5, `Expected line 5, got ${naError.location.start.line}`);
    assert(naError.location.start.col === 17, `Expected col 17, got ${naError.location.start.col}`);
  }
});

test('Error in nested inductive type signature', () => {
  const source = `inductive Vec : Nat -> Type -> Wrong where
  VNil : Vec Zero`;

  const results = checkSourceBlocks(source);

  const wrongError = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'Wrong');
  assert(wrongError !== undefined, 'Should have error for Wrong');

  if (wrongError && wrongError.location) {
    // Line 1 is "inductive Vec : Nat -> Type -> Wrong where"
    // Col 32 is the start of "Wrong"
    assert(wrongError.location.start.line === 1, `Expected line 1, got ${wrongError.location.start.line}`);
    assert(wrongError.location.start.col === 32, `Expected col 32, got ${wrongError.location.start.col}`);
  }
});

// ============================================================================
// Pattern Clause Body Position Tracking
// ============================================================================

test('Error in pattern clause body points to correct symbol', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plu a b)`;

  const results = checkSourceBlocks(source);

  assert(results.length === 2, 'Should have 2 blocks');
  assert(results[0].nameResolutionSuccess === true, 'Nat block should succeed');
  assert(results[1].nameResolutionSuccess === false, 'plus block should fail');

  const pluError = results[1].nameResolutionErrors.find(e => e.error.symbolName === 'plu');
  assert(pluError !== undefined, 'Should have error for plu');

  if (pluError && pluError.location) {
    assert(pluError.location !== null, 'Error should have location');
    // Line 7 is "plus (Succ a) b = Succ (plu a b)"
    // Col 25 is the start of "plu" (inside the application)
    assert(pluError.location.start.line === 7, `Expected line 7, got ${pluError.location.start.line}`);
    assert(pluError.location.start.col === 25, `Expected col 25, got ${pluError.location.start.col}`);
  }
});

test('Error in nested application within pattern clause', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a wrong)`;

  const results = checkSourceBlocks(source);

  assert(results.length === 2, 'Should have 2 blocks');
  const wrongError = results[1].nameResolutionErrors.find(e => e.error.symbolName === 'wrong');
  assert(wrongError !== undefined, 'Should have error for wrong');

  if (wrongError && wrongError.location) {
    // Line 7 is "plus (Succ a) b = Succ (plus a wrong)"
    // Col 32 is the start of "wrong"
    assert(wrongError.location.start.line === 7, `Expected line 7, got ${wrongError.location.start.line}`);
    assert(wrongError.location.start.col === 32, `Expected col 32, got ${wrongError.location.start.col}`);
  }
});

// ============================================================================
// Lambda and Binder Position Tracking
// ============================================================================

test('Error in lambda body points to correct location', () => {
  const source = `f : Nat -> Nat
f = fun x => wrongSymbol x`;

  const results = checkSourceBlocks(source);

  const error = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'wrongSymbol');
  assert(error !== undefined, 'Should have error for wrongSymbol');

  if (error && error.location) {
    // Line 2 is "f = fun x => wrongSymbol x"
    // Col 14 is the start of "wrongSymbol"
    assert(error.location.start.line === 2, `Expected line 2, got ${error.location.start.line}`);
    assert(error.location.start.col === 14, `Expected col 14, got ${error.location.start.col}`);
  }
});

test('Error in lambda domain type points to domain', () => {
  const source = `f = fun (x : Wrong) => x`;

  const results = checkSourceBlocks(source);

  const error = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'Wrong');
  assert(error !== undefined, 'Should have error for Wrong');

  if (error && error.location) {
    // Line 1 is "f = fun (x : Wrong) => x"
    // Col 14 is the start of "Wrong"
    assert(error.location.start.line === 1, `Expected line 1, got ${error.location.start.line}`);
    assert(error.location.start.col === 14, `Expected col 14, got ${error.location.start.col}`);
  }
});

test('Error in Pi type domain', () => {
  const source = `f : (x : Wrong) -> Nat`;

  const results = checkSourceBlocks(source);

  const error = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'Wrong');
  assert(error !== undefined, 'Should have error for Wrong');

  if (error && error.location) {
    // Line 1 is "f : (x : Wrong) -> Nat"
    // Col 10 is the start of "Wrong"
    assert(error.location.start.line === 1, `Expected line 1, got ${error.location.start.line}`);
    assert(error.location.start.col === 10, `Expected col 10, got ${error.location.start.col}`);
  }
});

test('Error in Pi type body', () => {
  const source = `f : (x : Nat) -> Wrong`;

  const results = checkSourceBlocks(source);

  const error = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'Wrong');
  assert(error !== undefined, 'Should have error for Wrong');

  if (error && error.location) {
    // Line 1 is "f : (x : Nat) -> Wrong"
    // Col 18 is the start of "Wrong"
    assert(error.location.start.line === 1, `Expected line 1, got ${error.location.start.line}`);
    assert(error.location.start.col === 18, `Expected col 18, got ${error.location.start.col}`);
  }
});

// ============================================================================
// Application Position Tracking
// ============================================================================

test('Error in function position of application', () => {
  const source = `x = wrongFn arg`;

  const results = checkSourceBlocks(source);

  const error = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'wrongFn');
  assert(error !== undefined, 'Should have error for wrongFn');

  if (error && error.location) {
    // Line 1 is "x = wrongFn arg"
    // Col 5 is the start of "wrongFn"
    assert(error.location.start.line === 1, `Expected line 1, got ${error.location.start.line}`);
    assert(error.location.start.col === 5, `Expected col 5, got ${error.location.start.col}`);
  }
});

test('Error in argument position of application', () => {
  const source = `inductive Nat : Type where
  Zero : Nat

x = Nat wrongArg`;

  const results = checkSourceBlocks(source);

  const error = results[1].nameResolutionErrors.find(e => e.error.symbolName === 'wrongArg');
  assert(error !== undefined, 'Should have error for wrongArg');

  if (error && error.location) {
    // Line 4 is "x = Nat wrongArg"
    // Col 9 is the start of "wrongArg"
    assert(error.location.start.line === 4, `Expected line 4, got ${error.location.start.line}`);
    assert(error.location.start.col === 9, `Expected col 9, got ${error.location.start.col}`);
  }
});

test('Error in nested application - multiple levels', () => {
  const source = `x = f (g (h wrong))`;

  const results = checkSourceBlocks(source);

  const error = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'wrong');
  assert(error !== undefined, 'Should have error for wrong');

  if (error && error.location) {
    // Line 1 is "x = f (g (h wrong))"
    // Col 13 is the start of "wrong"
    assert(error.location.start.line === 1, `Expected line 1, got ${error.location.start.line}`);
    assert(error.location.start.col === 13, `Expected col 13, got ${error.location.start.col}`);
  }
});

test('Error in chained application', () => {
  const source = `x = f g h wrong`;

  const results = checkSourceBlocks(source);

  const error = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'wrong');
  assert(error !== undefined, 'Should have error for wrong');

  if (error && error.location) {
    // Line 1 is "x = f g h wrong"
    // Col 11 is the start of "wrong"
    assert(error.location.start.line === 1, `Expected line 1, got ${error.location.start.line}`);
    assert(error.location.start.col === 11, `Expected col 11, got ${error.location.start.col}`);
  }
});

// ============================================================================
// Constructor Type Position Tracking
// ============================================================================

test('Error in first constructor type', () => {
  const source = `inductive List : Type where
  Nil : Wrong
  Cons : Nat -> List`;

  const results = checkSourceBlocks(source);

  const error = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'Wrong');
  assert(error !== undefined, 'Should have error for Wrong');

  if (error && error.location) {
    // Line 2 is "  Nil : Wrong"
    // Col 9 is the start of "Wrong"
    assert(error.location.start.line === 2, `Expected line 2, got ${error.location.start.line}`);
    assert(error.location.start.col === 9, `Expected col 9, got ${error.location.start.col}`);
  }
});

test('Error in second constructor type', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Wrong -> Nat`;

  const results = checkSourceBlocks(source);

  const error = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'Wrong');
  assert(error !== undefined, 'Should have error for Wrong');

  if (error && error.location) {
    // Line 3 is "  Succ : Wrong -> Nat"
    // Col 10 is the start of "Wrong"
    assert(error.location.start.line === 3, `Expected line 3, got ${error.location.start.line}`);
    assert(error.location.start.col === 10, `Expected col 10, got ${error.location.start.col}`);
  }
});

test('Error in constructor with complex type', () => {
  const source = `inductive Vec : Nat -> Type where
  VCons : (A : Type) -> (n : Nat) -> A -> Vec n -> Vec (Wrong n)`;

  const results = checkSourceBlocks(source);

  const error = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'Wrong');
  assert(error !== undefined, 'Should have error for Wrong');

  if (error && error.location) {
    // Line 2 is "  VCons : (A : Type) -> (n : Nat) -> A -> Vec n -> Vec (Wrong n)"
    // Col 60 is the start of "Wrong"
    assert(error.location.start.line === 2, `Expected line 2, got ${error.location.start.line}`);
    assert(error.location.start.col === 60, `Expected col 60, got ${error.location.start.col}`);
  }
});

// ============================================================================
// Multiple Pattern Clauses Position Tracking
// ============================================================================

test('Error in first pattern clause', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = wrong
plus (Succ a) b = Succ (plus a b)`;

  const results = checkSourceBlocks(source);

  const error = results[1].nameResolutionErrors.find(e => e.error.symbolName === 'wrong');
  assert(error !== undefined, 'Should have error for wrong');

  if (error && error.location) {
    // Line 6 is "plus Zero b = wrong"
    // Col 15 is the start of "wrong"
    assert(error.location.start.line === 6, `Expected line 6, got ${error.location.start.line}`);
    assert(error.location.start.col === 15, `Expected col 15, got ${error.location.start.col}`);
  }
});

test('Error in second pattern clause', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = wrong a b`;

  const results = checkSourceBlocks(source);

  const error = results[1].nameResolutionErrors.find(e => e.error.symbolName === 'wrong');
  assert(error !== undefined, 'Should have error for wrong');

  if (error && error.location) {
    // Line 7 is "plus (Succ a) b = wrong a b"
    // Col 19 is the start of "wrong"
    assert(error.location.start.line === 7, `Expected line 7, got ${error.location.start.line}`);
    assert(error.location.start.col === 19, `Expected col 19, got ${error.location.start.col}`);
  }
});

test('Error in third pattern clause', () => {
  const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

f : Nat -> Nat
f Zero = Zero
f (Succ Zero) = Zero
f (Succ (Succ n)) = wrong n`;

  const results = checkSourceBlocks(source);

  const error = results[1].nameResolutionErrors.find(e => e.error.symbolName === 'wrong');
  assert(error !== undefined, 'Should have error for wrong');

  if (error && error.location) {
    // Line 8 is "f (Succ (Succ n)) = wrong n"
    // Col 21 is the start of "wrong"
    assert(error.location.start.line === 8, `Expected line 8, got ${error.location.start.line}`);
    assert(error.location.start.col === 21, `Expected col 21, got ${error.location.start.col}`);
  }
});

// ============================================================================
// Parenthesized Expressions Position Tracking
// ============================================================================

test('Error inside parenthesized expression', () => {
  const source = `x = (wrong)`;

  const results = checkSourceBlocks(source);

  const error = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'wrong');
  assert(error !== undefined, 'Should have error for wrong');

  if (error && error.location) {
    // Line 1 is "x = (wrong)"
    // Col 6 is the start of "wrong"
    assert(error.location.start.line === 1, `Expected line 1, got ${error.location.start.line}`);
    assert(error.location.start.col === 6, `Expected col 6, got ${error.location.start.col}`);
  }
});

test('Error in nested parenthesized expressions', () => {
  const source = `x = ((wrong))`;

  const results = checkSourceBlocks(source);

  const error = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'wrong');
  assert(error !== undefined, 'Should have error for wrong');

  if (error && error.location) {
    // Line 1 is "x = ((wrong))"
    // Col 7 is the start of "wrong"
    assert(error.location.start.line === 1, `Expected line 1, got ${error.location.start.line}`);
    assert(error.location.start.col === 7, `Expected col 7, got ${error.location.start.col}`);
  }
});

test('Error in parenthesized arrow type', () => {
  const source = `f : (Wrong -> Nat) -> Nat`;

  const results = checkSourceBlocks(source);

  const error = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'Wrong');
  assert(error !== undefined, 'Should have error for Wrong');

  if (error && error.location) {
    // Line 1 is "f : (Wrong -> Nat) -> Nat"
    // Col 6 is the start of "Wrong"
    assert(error.location.start.line === 1, `Expected line 1, got ${error.location.start.line}`);
    assert(error.location.start.col === 6, `Expected col 6, got ${error.location.start.col}`);
  }
});

// ============================================================================
// Complex Nested Structures
// ============================================================================

test('Error in deeply nested lambda', () => {
  const source = `f = fun x => fun y => fun z => wrong x y z`;

  const results = checkSourceBlocks(source);

  const error = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'wrong');
  assert(error !== undefined, 'Should have error for wrong');

  if (error && error.location) {
    // Line 1 is "f = fun x => fun y => fun z => wrong x y z"
    // Col 32 is the start of "wrong"
    assert(error.location.start.line === 1, `Expected line 1, got ${error.location.start.line}`);
    assert(error.location.start.col === 32, `Expected col 32, got ${error.location.start.col}`);
  }
});

test('Error in lambda inside application', () => {
  const source = `inductive Nat : Type where
  Zero : Nat

x = Nat (fun y => wrong y)`;

  const results = checkSourceBlocks(source);

  const error = results[1].nameResolutionErrors.find(e => e.error.symbolName === 'wrong');
  assert(error !== undefined, 'Should have error for wrong');

  if (error && error.location) {
    // Line 4 is "x = Nat (fun y => wrong y)"
    // Col 19 is the start of "wrong"
    assert(error.location.start.line === 4, `Expected line 4, got ${error.location.start.line}`);
    assert(error.location.start.col === 19, `Expected col 19, got ${error.location.start.col}`);
  }
});

test('Error in application inside lambda', () => {
  const source = `f = fun x => wrong x`;

  const results = checkSourceBlocks(source);

  const error = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'wrong');
  assert(error !== undefined, 'Should have error for wrong');

  if (error && error.location) {
    // Line 1 is "f = fun x => wrong x"
    // Col 14 is the start of "wrong"
    assert(error.location.start.line === 1, `Expected line 1, got ${error.location.start.line}`);
    assert(error.location.start.col === 14, `Expected col 14, got ${error.location.start.col}`);
  }
});

test('Multiple errors in same expression point to different locations', () => {
  const source = `x = wrong1 wrong2 wrong3`;

  const results = checkSourceBlocks(source);

  const error1 = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'wrong1');
  const error2 = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'wrong2');
  const error3 = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'wrong3');

  assert(error1 !== undefined, 'Should have error for wrong1');
  assert(error2 !== undefined, 'Should have error for wrong2');
  assert(error3 !== undefined, 'Should have error for wrong3');

  if (error1 && error1.location) {
    assert(error1.location.start.col === 5, `wrong1 at col 5, got ${error1.location.start.col}`);
  }
  if (error2 && error2.location) {
    assert(error2.location.start.col === 12, `wrong2 at col 12, got ${error2.location.start.col}`);
  }
  if (error3 && error3.location) {
    assert(error3.location.start.col === 19, `wrong3 at col 19, got ${error3.location.start.col}`);
  }
});

// ============================================================================
// Edge Cases
// ============================================================================

test('Error in constructor with no arrow type', () => {
  const source = `inductive Unit : Type where
  MkUnit : Wrong`;

  const results = checkSourceBlocks(source);

  const error = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'Wrong');
  assert(error !== undefined, 'Should have error for Wrong');

  if (error && error.location) {
    // Line 2 is "  MkUnit : Wrong"
    // Col 12 is the start of "Wrong"
    assert(error.location.start.line === 2, `Expected line 2, got ${error.location.start.line}`);
    assert(error.location.start.col === 12, `Expected col 12, got ${error.location.start.col}`);
  }
});

test('Error in long chain of arrows', () => {
  const source = `f : A -> B -> C -> D -> Wrong -> F`;

  const results = checkSourceBlocks(source);

  const error = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'Wrong');
  assert(error !== undefined, 'Should have error for Wrong');

  if (error && error.location) {
    // Line 1 is "f : A -> B -> C -> D -> Wrong -> F"
    // Col 25 is the start of "Wrong"
    assert(error.location.start.line === 1, `Expected line 1, got ${error.location.start.line}`);
    assert(error.location.start.col === 25, `Expected col 25, got ${error.location.start.col}`);
  }
});

test('Error with multiline inductive definition', () => {
  const source = `inductive Vec :
  Nat ->
  Wrong ->
  Type where
  VNil : Vec`;

  const results = checkSourceBlocks(source);

  const error = results[0].nameResolutionErrors.find(e => e.error.symbolName === 'Wrong');
  assert(error !== undefined, 'Should have error for Wrong');

  if (error && error.location) {
    // Line 3 is "  Wrong -> "
    // Col 3 is the start of "Wrong"
    assert(error.location.start.line === 3, `Expected line 3, got ${error.location.start.line}`);
    assert(error.location.start.col === 3, `Expected col 3, got ${error.location.start.col}`);
  }
});

// ============================================================================
// Run all tests
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('ALL SOURCE POSITION REGRESSION TESTS PASSED! ✓');
console.log('='.repeat(80) + '\n');
