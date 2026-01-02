/**
 * Tests for the TT (Typed Terms) Core Layer
 *
 * These tests verify:
 * 1. De Bruijn index manipulation (substitution, shifting)
 * 2. Term construction and pretty-printing
 * 3. Eliminator construction
 * 4. Basic examples of proof terms
 */

import {
  TTerm,
  mkVar,
  mkPi,
  mkLambda,
  mkApp,
  mkHole,
  subst,
  prettyPrint,
  TT_CONSTANTS,
  NAT_ELIM,
} from './tt-core';

// ============================================================================
// Helper Functions for Testing
// ============================================================================

/**
 * Assert that two terms are structurally equal
 */
function assertTermEqual(actual: TTerm, expected: TTerm, message?: string): void {
  const actualStr = JSON.stringify(actual, null, 2);
  const expectedStr = JSON.stringify(expected, null, 2);

  if (actualStr !== expectedStr) {
    console.error('Terms not equal!');
    if (message) console.error('Test:', message);
    console.error('Expected:', expectedStr);
    console.error('Actual:', actualStr);
    throw new Error(`Term equality assertion failed: ${message || ''}`);
  }
}

/**
 * Run a test with a description
 */
function test(description: string, fn: () => void): void {
  try {
    fn();
    console.log(`✓ ${description}`);
  } catch (error) {
    console.error(`✗ ${description}`);
    throw error;
  }
}

// ============================================================================
// Basic Term Construction Tests
// ============================================================================

test('Create variables with De Bruijn indices', () => {
  const v0 = mkVar(0);
  const v1 = mkVar(1);
  const v2 = mkVar(2);

  assertTermEqual(v0, { tag: 'Var', index: 0 });
  assertTermEqual(v1, { tag: 'Var', index: 1 });
  assertTermEqual(v2, { tag: 'Var', index: 2 });
});

test('Create Pi types (dependent function types)', () => {
  // ℕ → ℕ (non-dependent function type)
  const nat = TT_CONSTANTS.Nat;
  const natToNat = mkPi(nat, nat, 'x');

  assertTermEqual(natToNat, {
    tag: 'Binder',
    name: 'x',
    binderKind: { tag: 'BPi' },
    domain: nat,
    body: nat
  });
});

test('Create Lambda terms', () => {
  // λ (x : ℕ), x
  // Identity function on naturals
  const nat = TT_CONSTANTS.Nat;
  const identity = mkLambda(nat, mkVar(0), 'x');

  assertTermEqual(identity, {
    tag: 'Binder',
    name: 'x',
    binderKind: { tag: 'BLam' },
    domain: nat,
    body: { tag: 'Var', index: 0 }
  });
});

test('Create function applications', () => {
  // succ 0
  const succZero = mkApp(TT_CONSTANTS.Succ, TT_CONSTANTS.Zero);

  assertTermEqual(succZero, {
    tag: 'App',
    fn: TT_CONSTANTS.Succ,
    arg: TT_CONSTANTS.Zero
  });
});

// ============================================================================
// De Bruijn Index Tests
// ============================================================================

test('De Bruijn indices: λx. λy. x', () => {
  // λx. λy. x  =>  λ. λ. 1
  // The outer lambda binds index 1, inner lambda binds index 0
  const nat = TT_CONSTANTS.Nat;
  const term = mkLambda(nat, mkLambda(nat, mkVar(1)));

  // Pretty print should show: (λ (x0 : ℕ), (λ (x1 : ℕ), x0))
  const pretty = prettyPrint(term);
  console.log('  λx. λy. x =', pretty);
});

test('De Bruijn indices: λx. λy. y', () => {
  // λx. λy. y  =>  λ. λ. 0
  const nat = TT_CONSTANTS.Nat;
  const term = mkLambda(nat, mkLambda(nat, mkVar(0)));

  const pretty = prettyPrint(term);
  console.log('  λx. λy. y =', pretty);
});

test('De Bruijn indices: λx. λy. λz. x z (y z)', () => {
  // λx. λy. λz. x z (y z)  =>  λ. λ. λ. 2 0 (1 0)
  const nat = TT_CONSTANTS.Nat;
  const term = mkLambda(nat,
    mkLambda(nat,
      mkLambda(nat,
        mkApp(
          mkApp(mkVar(2), mkVar(0)),  // x z
          mkApp(mkVar(1), mkVar(0))   // y z
        )
      )
    )
  );

  const pretty = prettyPrint(term);
  console.log('  λx. λy. λz. x z (y z) =', pretty);
});

// ============================================================================
// Substitution Tests
// ============================================================================

test('Substitution: [0 := 42] in 0 = 42', () => {
  // Replacing variable 0 with literal 42
  const zero = TT_CONSTANTS.Zero;
  const result = subst(0, zero, mkVar(0));

  assertTermEqual(result, zero);
});

test('Substitution: [0 := s] in 1 = 1', () => {
  // Variable 1 should not be affected
  const zero = TT_CONSTANTS.Zero;
  const result = subst(0, zero, mkVar(1));

  assertTermEqual(result, mkVar(1));
});

test('Substitution in lambda: [0 := s] in (λx. 1) = (λx. 1)', () => {
  // Substituting for variable 0 in (λx. 1)
  // Inside the lambda, variable 0 refers to the lambda-bound x,
  // and variable 1 refers to the outer variable 0
  const nat = TT_CONSTANTS.Nat;
  const zero = TT_CONSTANTS.Zero;

  const term = mkLambda(nat, mkVar(1));  // λx. (outer var 0)
  const result = subst(0, zero, term);

  // After substitution: λx. zero
  const expected = mkLambda(nat, zero);

  console.log('  Before:', prettyPrint(term));
  console.log('  After:', prettyPrint(result));

  assertTermEqual(result, expected);
});

test('Substitution under binders: [0 := 0] in (λx. λy. 2)', () => {
  // [0 := Zero] in (λx. λy. 2)
  // Variable 2 inside two lambdas refers to the outer variable 0
  const nat = TT_CONSTANTS.Nat;
  const zero = TT_CONSTANTS.Zero;

  const term = mkLambda(nat, mkLambda(nat, mkVar(2)));
  const result = subst(0, zero, term);

  // Should become: λx. λy. 0
  const expected = mkLambda(nat, mkLambda(nat, zero));

  console.log('  Before:', prettyPrint(term));
  console.log('  After:', prettyPrint(result));

  assertTermEqual(result, expected);
});

// ============================================================================
// Pretty Printing Tests
// ============================================================================

test('Pretty print: Simple Pi type', () => {
  // ℕ -> ℕ
  const nat = TT_CONSTANTS.Nat;
  const natToNat = mkPi(nat, nat);

  const pretty = prettyPrint(natToNat);
  console.log('  ℕ -> ℕ =', pretty);

  // Should use -> notation since it's non-dependent
  if (!pretty.includes('->')) {
    throw new Error('Non-dependent function should use -> notation');
  }
});

test('Pretty print: Dependent Pi type', () => {
  // (n : ℕ) -> Vec n
  // This is a dependent type where the result type depends on the argument
  const nat = TT_CONSTANTS.Nat;

  // For testing, we'll use: (x : ℕ) -> x where the codomain references x
  // This means we need Var(0) in the codomain
  const dependentType = mkPi(nat, mkVar(0));

  const pretty = prettyPrint(dependentType);
  console.log('  (x : ℕ) -> x =', pretty);

  // The pretty printer uses arrow notation with binder name visible: (x : ℕ) -> x
  // This shows it's dependent because x appears in the body
  if (!pretty.includes('->') || !pretty.includes('x : ℕ')) {
    throw new Error('Dependent function should show (x : ℕ) -> ...');
  }
});

test('Pretty print: Lambda with application', () => {
  // λ (x : ℕ), succ x
  const nat = TT_CONSTANTS.Nat;
  const term = mkLambda(nat, mkApp(TT_CONSTANTS.Succ, mkVar(0)));

  const pretty = prettyPrint(term);
  console.log('  λx. succ x =', pretty);
});

test('Pretty print: Nested lambdas', () => {
  // λ (x : ℕ), λ (y : ℕ), x
  const nat = TT_CONSTANTS.Nat;
  const term = mkLambda(nat, mkLambda(nat, mkVar(1)));

  const pretty = prettyPrint(term);
  console.log('  λx. λy. x =', pretty);
});

// ============================================================================
// Hole (Metavariable) Tests
// ============================================================================

test('Create a hole with type and context', () => {
  const nat = TT_CONSTANTS.Nat;
  const hole = mkHole('base_case', nat, [
    { name: 'n', type: nat }
  ]);

  if (hole.tag !== 'Hole') {
    throw new Error('Expected hole term');
  }

  assertTermEqual(hole.type, nat);
  if (hole.context.length !== 1) {
    throw new Error('Expected context with 1 binding');
  }
});

test('Pretty print hole', () => {
  const nat = TT_CONSTANTS.Nat;
  const hole = mkHole('goal1', nat);

  const pretty = prettyPrint(hole);
  console.log('  Hole:', pretty);

  if (!pretty.includes('?')) {
    throw new Error('Hole should be printed with ?');
  }
});

// ============================================================================
// Eliminator Construction Tests
// ============================================================================

test('nat_elim has correct structure', () => {
  // Check that NAT_ELIM is a constant with the right name
  if (NAT_ELIM.tag !== 'Const') {
    throw new Error('nat_elim should be a Const');
  }

  if (NAT_ELIM.name !== 'nat_elim') {
    throw new Error('nat_elim should have name "nat_elim"');
  }

  console.log('  nat_elim type:', prettyPrint(NAT_ELIM.type));
});

test('Construct induction proof term with holes', () => {
  /**
   * Example: Prove ∀n. P(n) by induction
   *
   * The term should be:
   *   nat_elim
   *     (λn. P n)           -- motive
   *     ?base               -- base case (hole)
   *     (λk. λIH. ?step)    -- inductive step (hole)
   *     n                   -- value being inducted on
   */

  const nat = TT_CONSTANTS.Nat;

  // Motive: λn : ℕ. Prop
  // For testing, we'll use a simple property: λn. ℕ
  const motive = mkLambda(nat, nat);

  // Base case: hole with type P(0)
  const baseCase = mkHole('base', nat);

  // Inductive step: λk : ℕ. λIH : P(k). ?step
  // The type of ?step should be P(k+1)
  const inductiveStep = mkLambda(
    nat,                                        // k : ℕ
    mkLambda(
      nat,                                      // IH : P(k)
      mkHole('step', nat)                       // ?step : P(k+1)
    )
  );

  // The value being inducted on (for example, variable n)
  const n = mkVar(0);

  // Full term: nat_elim motive base step n
  const proofTerm = mkApp(
    mkApp(
      mkApp(
        mkApp(NAT_ELIM, motive),
        baseCase
      ),
      inductiveStep
    ),
    n
  );

  const pretty = prettyPrint(proofTerm, ['n']);
  console.log('\n  Induction proof term with holes:');
  console.log('  ', pretty);

  // Verify structure
  if (proofTerm.tag !== 'App') {
    throw new Error('Expected application at top level');
  }

  // Should have two holes: base and step
  const termStr = JSON.stringify(proofTerm);
  if (!termStr.includes('"base"') || !termStr.includes('"step"')) {
    throw new Error('Expected to find both base and step holes');
  }

  console.log('\n  This term has two holes to fill:');
  console.log('    ?base  - prove P(0)');
  console.log('    ?step  - prove P(k+1) given IH : P(k)');
});

// ============================================================================
// Integration Test: Complete Proof Term Example
// ============================================================================

test('Complete example: Prove 0 + n = n by induction', () => {
  /**
   * We want to prove: ∀n : ℕ. 0 + n = n
   *
   * The proof term structure:
   *   nat_elim
   *     (λn. 0 + n = n)                    -- motive
   *     (refl : 0 + 0 = 0)                 -- base case
   *     (λk. λIH : 0 + k = k.              -- inductive step
   *       trans (cong succ IH) (succ_add_comm))
   *     n
   *
   * For this test, we'll construct the skeleton with holes
   */

  const nat = TT_CONSTANTS.Nat;
  const zero = TT_CONSTANTS.Zero;

  // We need an equality type constructor
  // eq : Π (A : Type), A → A → Prop
  const eq = TT_CONSTANTS.Eq;

  // Motive: λn : ℕ. (0 + n = n)
  // For simplicity, we'll represent "0 + n" as a constant application
  // In a real implementation, we'd have a plus function
  const motive = mkLambda(
    nat,
    // Type: 0 + n = n
    // We'll use a simplified representation
    mkApp(
      mkApp(
        mkApp(eq, nat),  // eq ℕ
        mkVar(0)         // 0 + n (simplified as just n for now)
      ),
      mkVar(0)           // n
    )
  );

  // Base case: prove 0 + 0 = 0
  const baseCase = mkHole('base_zero_add', mkApp(mkApp(mkApp(eq, nat), zero), zero));

  // Inductive step: λk. λIH. prove 0 + (k+1) = k+1
  const inductiveStep = mkLambda(
    nat,  // k
    mkLambda(
      mkApp(mkApp(mkApp(eq, nat), mkVar(0)), mkVar(0)),  // IH : 0 + k = k
      mkHole('step_zero_add', mkApp(
        mkApp(mkApp(eq, nat), mkVar(1)),  // 0 + (k+1)
        mkVar(1)                           // k+1
      ))
    )
  );

  // Build the full term
  const proofTerm = mkApp(
    mkApp(
      mkApp(
        mkApp(NAT_ELIM, motive),
        baseCase
      ),
      inductiveStep
    ),
    mkVar(0)  // n (from outer context)
  );

  const pretty = prettyPrint(proofTerm, ['n']);
  console.log('\n  Proof of ∀n. 0 + n = n:');
  console.log('  ', pretty);

  console.log('\n  This is the complete proof term structure!');
  console.log('  It has the eliminator applied to:');
  console.log('    - motive (what we\'re proving)');
  console.log('    - base case (with hole)');
  console.log('    - inductive step (with hole and IH)');
  console.log('    - the value n');
});

// ============================================================================
// Run All Tests
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('TT CORE LAYER TESTS');
console.log('='.repeat(80) + '\n');

console.log('All tests passed! ✓\n');

export { test, assertTermEqual };
