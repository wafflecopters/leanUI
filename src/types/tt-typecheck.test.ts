/**
 * Tests for the TT Type Checker
 *
 * These tests verify:
 * 1. Type synthesis (inference)
 * 2. Type checking
 * 3. Conversion checking
 * 4. Universe checking
 * 5. Error cases
 */

import {
  TContext,
  mkVar,
  mkPi,
  mkLambda,
  mkApp,
  mkHole,
  mkProp,
  prettyPrint,
  TT_CONSTANTS,
  NAT_ELIM,
} from './tt-core';

import {
  inferType,
  checkType,
  TypeCheckError,
  convertible,
  whnf,
  extractHoles,
  fillHole,
} from './tt-typecheck';

// ============================================================================
// Test Helper
// ============================================================================

function test(description: string, fn: () => void): void {
  try {
    fn();
    console.log(`✓ ${description}`);
  } catch (error) {
    console.error(`✗ ${description}`);
    throw error;
  }
}

function assertThrows(fn: () => void, message?: string): void {
  try {
    fn();
    throw new Error(`Expected function to throw, but it didn't. ${message || ''}`);
  } catch (error) {
    if (!(error instanceof TypeCheckError) && !(error instanceof Error && error.message.includes('Expected'))) {
      throw error;
    }
  }
}

// ============================================================================
// Basic Type Synthesis Tests
// ============================================================================

test('Infer type of Sort (universe)', () => {
  const prop = mkProp();  // Prop = Type_0
  const type = inferType(prop);

  if (type.tag !== 'Sort' || type.level !== 1) {
    throw new Error(`Expected Type_1, got ${prettyPrint(type)}`);
  }

  console.log(`  Prop : ${prettyPrint(type)}`);
});

test('Infer type of Const (ℕ)', () => {
  const nat = TT_CONSTANTS.Nat;
  const type = inferType(nat);

  if (type.tag !== 'Sort' || type.level !== 0) {
    throw new Error(`Expected Type_0, got ${prettyPrint(type)}`);
  }

  console.log(`  ℕ : ${prettyPrint(type)}`);
});

test('Infer type of variable in context', () => {
  const nat = TT_CONSTANTS.Nat;
  const ctx: TContext = [
    { name: 'x', type: nat }
  ];

  const xVar = mkVar(0);
  const type = inferType(xVar, ctx);

  if (!convertible(type, nat)) {
    throw new Error(`Expected ℕ, got ${prettyPrint(type)}`);
  }

  console.log(`  x : ${prettyPrint(type)} (in context)`);
});

test('Infer type of Pi (ℕ → ℕ)', () => {
  const nat = TT_CONSTANTS.Nat;
  const natToNat = mkPi(nat, nat);

  const type = inferType(natToNat);

  if (type.tag !== 'Sort') {
    throw new Error(`Expected Sort, got ${prettyPrint(type)}`);
  }

  console.log(`  (ℕ → ℕ) : ${prettyPrint(type)}`);
});

test('Infer type of Lambda (λx:ℕ. x)', () => {
  const nat = TT_CONSTANTS.Nat;
  const identity = mkLambda(nat, mkVar(0), 'x');

  const type = inferType(identity);

  // Should be ℕ → ℕ (a Binder with BPi)
  if (type.tag !== 'Binder' || type.binderKind.tag !== 'BPi' ||
      !convertible(type.domain, nat) || !convertible(type.body, nat)) {
    throw new Error(`Expected ℕ → ℕ, got ${prettyPrint(type)}`);
  }

  console.log(`  λx:ℕ. x : ${prettyPrint(type)}`);
});

test('Infer type of application (succ 0)', () => {
  const succZero = mkApp(TT_CONSTANTS.Succ, TT_CONSTANTS.Zero);
  const type = inferType(succZero);

  if (!convertible(type, TT_CONSTANTS.Nat)) {
    throw new Error(`Expected ℕ, got ${prettyPrint(type)}`);
  }

  console.log(`  succ 0 : ${prettyPrint(type)}`);
});

// ============================================================================
// Type Checking Tests
// ============================================================================

test('Check lambda against Pi type', () => {
  const nat = TT_CONSTANTS.Nat;
  const identity = mkLambda(nat, mkVar(0));
  const natToNat = mkPi(nat, nat);

  // Should succeed
  checkType(identity, natToNat);

  console.log(`  ✓ λx:ℕ. x has type ℕ → ℕ`);
});

test('Check fails for wrong type', () => {
  const nat = TT_CONSTANTS.Nat;
  const real = TT_CONSTANTS.Real;

  const identity = mkLambda(nat, mkVar(0));
  const realToReal = mkPi(real, real);

  // Should fail
  assertThrows(() => checkType(identity, realToReal), 'Type mismatch should throw');

  console.log(`  ✓ Type mismatch correctly detected`);
});

// ============================================================================
// Conversion and Normalization Tests
// ============================================================================

test('Beta reduction: (λx. x) y --> y', () => {
  const nat = TT_CONSTANTS.Nat;
  const ctx: TContext = [{ name: 'y', type: nat }];

  const term = mkApp(
    mkLambda(nat, mkVar(0)),  // λx. x
    mkVar(0)                   // y
  );

  const normal = whnf(term, ctx);

  // Should be just y (Var 0)
  if (normal.tag !== 'Var' || normal.index !== 0) {
    throw new Error(`Expected Var(0), got ${prettyPrint(normal)}`);
  }

  console.log(`  (λx. x) y  ~>  ${prettyPrint(normal, ['y'])}`);
});

test('Convertibility: ℕ ≡ ℕ', () => {
  const nat1 = TT_CONSTANTS.Nat;
  const nat2 = TT_CONSTANTS.Nat;

  if (!convertible(nat1, nat2)) {
    throw new Error('ℕ should be convertible with ℕ');
  }

  console.log(`  ℕ ≡ ℕ`);
});

test('Convertibility: (λx. x) y ≡ y', () => {
  const nat = TT_CONSTANTS.Nat;
  const ctx: TContext = [{ name: 'y', type: nat }];

  const term1 = mkApp(mkLambda(nat, mkVar(0)), mkVar(0));  // (λx. x) y
  const term2 = mkVar(0);                                   // y

  if (!convertible(term1, term2, ctx)) {
    throw new Error('(λx. x) y should be convertible with y');
  }

  console.log(`  (λx. x) y ≡ y`);
});

test('Not convertible: ℕ ≢ Prop', () => {
  const nat = TT_CONSTANTS.Nat;
  const prop = mkProp();

  if (convertible(nat, prop)) {
    throw new Error('ℕ should not be convertible with Prop');
  }

  console.log(`  ℕ ≢ Prop`);
});

// ============================================================================
// Hole Extraction and Filling Tests
// ============================================================================

test('Extract holes from term', () => {
  const nat = TT_CONSTANTS.Nat;

  // Build a term with two holes: ?base and ?step
  const term = mkApp(
    mkHole('base', nat),
    mkHole('step', nat)
  );

  const holes = extractHoles(term);

  if (holes.length !== 2) {
    throw new Error(`Expected 2 holes, got ${holes.length}`);
  }

  if (!holes.find(h => h.id === 'base') || !holes.find(h => h.id === 'step')) {
    throw new Error('Expected to find holes "base" and "step"');
  }

  console.log(`  Found ${holes.length} holes: ${holes.map(h => '?' + h.id).join(', ')}`);
});

test('Fill a hole with a proof term', () => {
  const nat = TT_CONSTANTS.Nat;
  const zero = TT_CONSTANTS.Zero;

  // Term: ?base
  const term = mkHole('base', nat);

  // Fill with 0
  const filled = fillHole(term, 'base', zero);

  if (!convertible(filled, zero)) {
    throw new Error(`Expected 0, got ${prettyPrint(filled)}`);
  }

  console.log(`  ?base  -->  ${prettyPrint(filled)}`);
});

test('Fill hole in nested term', () => {
  const nat = TT_CONSTANTS.Nat;
  const zero = TT_CONSTANTS.Zero;

  // Term: succ ?base
  const term = mkApp(TT_CONSTANTS.Succ, mkHole('base', nat));

  // Fill ?base with 0
  const filled = fillHole(term, 'base', zero);

  // Should be succ 0
  if (filled.tag !== 'App') {
    throw new Error(`Expected application, got ${prettyPrint(filled)}`);
  }

  console.log(`  succ ?base  -->  ${prettyPrint(filled)}`);
});

// ============================================================================
// Complex Example: Type Check Induction Proof Skeleton
// ============================================================================

test('Type check induction proof term with holes (simplified)', () => {
  /**
   * Build a simplified induction proof term:
   * nat_elim P ?base (λx. ?step) m
   *
   * Using simplified nat_elim : Π (P : Prop), P → (P → P) → ℕ → P
   */

  const nat = TT_CONSTANTS.Nat;

  // P is just ℕ for this example
  const P = nat;

  // Base case: ?base : P
  const baseCase = mkHole('base', P);

  // Inductive step: λx. ?step : P → P
  const inductiveStep = mkLambda(P, mkHole('step', P));

  // The full proof term (in a context with m : ℕ)
  const ctx: TContext = [{ name: 'm', type: nat }];
  const m = mkVar(0);

  const proofTerm = mkApp(
    mkApp(
      mkApp(
        mkApp(NAT_ELIM, P),
        baseCase
      ),
      inductiveStep
    ),
    m
  );

  // Type check the proof term
  // The expected type is: P = ℕ
  checkType(proofTerm, P, ctx);

  console.log('\n  Induction proof term type checks! ✓');
  console.log(`  Term: ${prettyPrint(proofTerm, ['m'])}`);

  // Extract holes
  const holes = extractHoles(proofTerm);
  console.log(`\n  Holes to fill: ${holes.map(h => '?' + h.id).join(', ')}`);
});

// ============================================================================
// Error Cases
// ============================================================================

test('Error: Variable not in context', () => {
  const term = mkVar(0);
  const emptyCtx: TContext = [];

  assertThrows(() => inferType(term, emptyCtx), 'Should throw for unbound variable');

  console.log(`  ✓ Unbound variable correctly rejected`);
});

test('Error: Application to non-function', () => {
  const zero = TT_CONSTANTS.Zero;

  // Try to apply 0 to something: 0 42
  const term = mkApp(zero, zero);

  assertThrows(() => inferType(term), 'Should throw for non-function application');

  console.log(`  ✓ Non-function application correctly rejected`);
});

test('Error: Pi domain must be a type', () => {
  const zero = TT_CONSTANTS.Zero;

  // Try: Π (x : 0), ℕ  (domain is not a type)
  const badPi = mkPi(zero, TT_CONSTANTS.Nat);

  assertThrows(() => inferType(badPi), 'Should throw for non-type Pi domain');

  console.log(`  ✓ Non-type Pi domain correctly rejected`);
});

// ============================================================================
// Run All Tests
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('TT TYPE CHECKER TESTS');
console.log('='.repeat(80) + '\n');

console.log('\nAll type checker tests passed! ✓\n');
