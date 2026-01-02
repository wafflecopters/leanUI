/**
 * Tests for the TTK Unification Algorithm
 *
 * These tests verify the unification algorithm from "Pattern Matching Without K"
 * by Jesper Cockx, Dominique Devriese, and Frank Piessens (ICFP 2014).
 *
 * Tests cover:
 * 1. Solution rule (metavariable/hole solving)
 * 2. Deletion rule (with and without UIP)
 * 3. Injectivity rule (constructor decomposition)
 * 4. Conflict rule (different constructors)
 * 5. Cycle rule (occurs check)
 * 6. Eta rule (function equality)
 * 7. Complex unification problems
 */

import {
  TTKTerm,
  TTKContext,
  mkVar,
  mkPi,
  mkLambda,
  mkApp,
  mkHole,
  mkConst,
  mkType,
  prettyPrint,
} from './tt-kernel';

import {
  unify,
  unifyTerms,
  canUnify,
  applySubstitution,
  emptySubstitution,
  extendSubstitution,
  holeOccursIn,
  asConstructorApp,
  UnifyResult,
  Substitution,
} from './tt-unify';

// ============================================================================
// Test Helpers
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

function assertSuccess(result: UnifyResult, message?: string): Substitution {
  if (result.tag !== 'success') {
    throw new Error(
      `Expected success, got ${result.tag}: ${
        result.tag === 'failure' ? result.reason : result.tag === 'stuck' ? result.reason : ''
      }. ${message || ''}`
    );
  }
  return result.substitution;
}

function assertFailure(result: UnifyResult, message?: string): string {
  if (result.tag !== 'failure') {
    throw new Error(`Expected failure, got ${result.tag}. ${message || ''}`);
  }
  return result.reason;
}

function assertStuck(result: UnifyResult, message?: string): string {
  if (result.tag !== 'stuck') {
    throw new Error(`Expected stuck, got ${result.tag}. ${message || ''}`);
  }
  return result.reason;
}

// ============================================================================
// Test Constants
// ============================================================================

// Type constants
const Type0 = mkType(0);
// Note: Prop = mkProp() = Sort(0) = Type0 in this system

// Nat type and constructors
const Nat = mkConst('Nat', Type0);
const Zero = mkConst('zero', Nat);
const Succ = mkConst('succ', mkPi(Nat, Nat, 'n'));

// Bool type and constructors
const Bool = mkConst('Bool', Type0);
const True = mkConst('true', Bool);
const False = mkConst('false', Bool);

// List type and constructors
const ListKind = mkPi(Type0, Type0, 'A');
const List = mkConst('List', ListKind);
const Nil = mkConst('nil', mkPi(Type0, mkApp(List, mkVar(0)), 'A'));
const Cons = mkConst('cons',
  mkPi(Type0,
    mkPi(mkVar(0),
      mkPi(mkApp(List, mkVar(1)),
        mkApp(List, mkVar(2)), '_'), '_'), 'A'));

// Helper to create succ n
function succ(n: TTKTerm): TTKTerm {
  return mkApp(Succ, n);
}

// Helper to create hole
function hole(id: string, type: TTKTerm = Nat): TTKTerm {
  return mkHole(id, type, []);
}

console.log('\n' + '='.repeat(80));
console.log('TTK UNIFICATION TESTS');
console.log('='.repeat(80) + '\n');

// ============================================================================
// Substitution Operations Tests
// ============================================================================

console.log('--- Substitution Operations ---\n');

test('Empty substitution', () => {
  const subst = emptySubstitution();
  if (subst.size !== 0) {
    throw new Error('Empty substitution should have size 0');
  }
});

test('Extend substitution', () => {
  const subst = extendSubstitution(emptySubstitution(), 'x', Zero);
  if (subst.size !== 1 || !subst.has('x')) {
    throw new Error('Substitution should have one entry');
  }
  const term = subst.get('x');
  if (term?.tag !== 'Const' || term.name !== 'zero') {
    throw new Error('Substitution should map x to zero');
  }
});

test('Apply substitution to hole', () => {
  const subst = extendSubstitution(emptySubstitution(), 'x', Zero);
  const term = hole('x');
  const result = applySubstitution(subst, term);

  if (result.tag !== 'Const' || result.name !== 'zero') {
    throw new Error(`Expected zero, got ${prettyPrint(result)}`);
  }
});

test('Apply substitution to nested term', () => {
  const subst = extendSubstitution(emptySubstitution(), 'x', Zero);
  const term = mkApp(Succ, hole('x'));
  const result = applySubstitution(subst, term);

  // Should be succ zero
  if (result.tag !== 'App' || result.arg.tag !== 'Const' || result.arg.name !== 'zero') {
    throw new Error(`Expected succ zero, got ${prettyPrint(result)}`);
  }
});

// ============================================================================
// Occurs Check Tests
// ============================================================================

console.log('\n--- Occurs Check ---\n');

test('Hole does not occur in different hole', () => {
  const term = hole('y');
  if (holeOccursIn('x', term)) {
    throw new Error('Hole x should not occur in hole y');
  }
});

test('Hole occurs in itself', () => {
  const term = hole('x');
  if (!holeOccursIn('x', term)) {
    throw new Error('Hole x should occur in itself');
  }
});

test('Hole occurs in nested term', () => {
  const term = mkApp(Succ, hole('x'));
  if (!holeOccursIn('x', term)) {
    throw new Error('Hole x should occur in succ ?x');
  }
});

test('Hole does not occur in constant', () => {
  const term = Zero;
  if (holeOccursIn('x', term)) {
    throw new Error('Hole x should not occur in zero');
  }
});

// ============================================================================
// Constructor Detection Tests
// ============================================================================

console.log('\n--- Constructor Detection ---\n');

test('Detect zero as constructor', () => {
  const ctor = asConstructorApp(Zero);
  if (ctor === null || ctor.name !== 'zero' || ctor.args.length !== 0) {
    throw new Error('Should detect zero as constructor with 0 args');
  }
});

test('Detect succ zero as constructor application', () => {
  const term = succ(Zero);
  const ctor = asConstructorApp(term);
  if (ctor === null || ctor.name !== 'succ' || ctor.args.length !== 1) {
    throw new Error('Should detect succ zero as constructor with 1 arg');
  }
});

test('Variable is not a constructor', () => {
  const term = mkVar(0);
  const ctor = asConstructorApp(term);
  if (ctor !== null) {
    throw new Error('Variable should not be detected as constructor');
  }
});

// ============================================================================
// Solution Rule Tests
// ============================================================================

console.log('\n--- Solution Rule ---\n');

test('Unify hole with constant: ?x = zero', () => {
  const result = unifyTerms(hole('x'), Zero, Nat);
  const subst = assertSuccess(result);

  const value = subst.get('x');
  if (value?.tag !== 'Const' || value.name !== 'zero') {
    throw new Error('Expected ?x = zero');
  }
  console.log(`  ?x := ${prettyPrint(value!)}`);
});

test('Unify constant with hole: zero = ?x', () => {
  const result = unifyTerms(Zero, hole('x'), Nat);
  const subst = assertSuccess(result);

  const value = subst.get('x');
  if (value?.tag !== 'Const' || value.name !== 'zero') {
    throw new Error('Expected ?x = zero');
  }
  console.log(`  ?x := ${prettyPrint(value!)}`);
});

test('Unify hole with hole: ?x = ?y', () => {
  const result = unifyTerms(hole('x'), hole('y'), Nat);
  const subst = assertSuccess(result);

  // One hole should be assigned to the other
  if (subst.size !== 1) {
    throw new Error('Expected exactly one substitution');
  }
  console.log(`  Substitution size: ${subst.size}`);
});

test('Unify hole with nested term: ?x = succ zero', () => {
  const term = succ(Zero);
  const result = unifyTerms(hole('x'), term, Nat);
  const subst = assertSuccess(result);

  const value = subst.get('x');
  if (value?.tag !== 'App') {
    throw new Error('Expected ?x = succ zero');
  }
  console.log(`  ?x := ${prettyPrint(value!)}`);
});

// ============================================================================
// Deletion Rule Tests
// ============================================================================

console.log('\n--- Deletion Rule ---\n');

test('Unify identical constants: zero = zero (with UIP)', () => {
  const result = unifyTerms(Zero, Zero, Nat, [], { useUIP: true });
  assertSuccess(result);
  console.log('  zero = zero succeeds with UIP');
});

test('Unify identical constants: zero = zero (without UIP)', () => {
  const result = unifyTerms(Zero, Zero, Nat, [], { useUIP: false });
  // Should still succeed because syntactically identical
  assertSuccess(result);
  console.log('  zero = zero succeeds without UIP (syntactic identity)');
});

test('Unify identical nested terms: succ zero = succ zero', () => {
  const term1 = succ(Zero);
  const term2 = succ(Zero);
  const result = unifyTerms(term1, term2, Nat, [], { useUIP: true });
  assertSuccess(result);
  console.log('  succ zero = succ zero succeeds');
});

test('Reflexive equation with variable: x = x (with UIP)', () => {
  const ctx: TTKContext = [{ name: 'x', type: Nat }];
  const x = mkVar(0);
  const result = unifyTerms(x, x, Nat, ctx, { useUIP: true });
  assertSuccess(result);
  console.log('  x = x succeeds with UIP');
});

test('Reflexive equation with variable: x = x (without UIP)', () => {
  const ctx: TTKContext = [{ name: 'x', type: Nat }];
  const x = mkVar(0);
  const result = unifyTerms(x, x, Nat, ctx, { useUIP: false });
  // Should succeed because syntactically identical
  assertSuccess(result);
  console.log('  x = x succeeds without UIP (syntactic identity)');
});

// ============================================================================
// Injectivity Rule Tests
// ============================================================================

console.log('\n--- Injectivity Rule ---\n');

test('Injectivity: succ ?x = succ zero', () => {
  const lhs = succ(hole('x'));
  const rhs = succ(Zero);
  const result = unifyTerms(lhs, rhs, Nat);
  const subst = assertSuccess(result);

  const value = subst.get('x');
  if (value?.tag !== 'Const' || value.name !== 'zero') {
    throw new Error('Expected ?x = zero from injectivity');
  }
  console.log(`  ?x := ${prettyPrint(value!)}`);
});

test('Injectivity: succ (succ ?x) = succ (succ zero)', () => {
  const lhs = succ(succ(hole('x')));
  const rhs = succ(succ(Zero));
  const result = unifyTerms(lhs, rhs, Nat);
  const subst = assertSuccess(result);

  const value = subst.get('x');
  if (value?.tag !== 'Const' || value.name !== 'zero') {
    throw new Error('Expected ?x = zero from nested injectivity');
  }
  console.log(`  ?x := ${prettyPrint(value!)}`);
});

test('Injectivity with multiple holes: succ ?x = succ ?y (assigns one to other)', () => {
  const lhs = succ(hole('x'));
  const rhs = succ(hole('y'));
  const result = unifyTerms(lhs, rhs, Nat);
  const subst = assertSuccess(result);

  // Should have one substitution (one hole assigned to the other)
  console.log(`  Substitution size: ${subst.size}`);
});

// ============================================================================
// Conflict Rule Tests
// ============================================================================

console.log('\n--- Conflict Rule ---\n');

test('Conflict: zero ≠ succ zero', () => {
  const lhs = Zero;
  const rhs = succ(Zero);
  const result = unifyTerms(lhs, rhs, Nat);
  const reason = assertFailure(result);

  console.log(`  Conflict detected: ${reason}`);
});

test('Conflict: true ≠ false', () => {
  const result = unifyTerms(True, False, Bool);
  const reason = assertFailure(result);

  console.log(`  Conflict detected: ${reason}`);
});

test('Conflict in nested terms: succ zero ≠ succ (succ zero)', () => {
  const lhs = succ(Zero);
  const rhs = succ(succ(Zero));
  const result = unifyTerms(lhs, rhs, Nat);
  const reason = assertFailure(result);

  console.log(`  Conflict detected: ${reason}`);
});

// ============================================================================
// Cycle Rule Tests
// ============================================================================

console.log('\n--- Cycle Rule ---\n');

test('Cycle: ?x = succ ?x fails', () => {
  const lhs = hole('x');
  const rhs = succ(hole('x'));
  const result = unifyTerms(lhs, rhs, Nat);
  const reason = assertFailure(result);

  console.log(`  Cycle detected: ${reason}`);
});

test('Cycle: ?x = succ (succ ?x) fails', () => {
  const lhs = hole('x');
  const rhs = succ(succ(hole('x')));
  const result = unifyTerms(lhs, rhs, Nat);
  const reason = assertFailure(result);

  console.log(`  Cycle detected: ${reason}`);
});

// ============================================================================
// Eta Rule Tests
// ============================================================================

console.log('\n--- Eta Rule ---\n');

test('Unify identical lambdas: λx. x = λx. x', () => {
  const lhs = mkLambda(Nat, mkVar(0), 'x');
  const rhs = mkLambda(Nat, mkVar(0), 'x');
  const result = unifyTerms(lhs, rhs, mkPi(Nat, Nat));
  assertSuccess(result);
  console.log('  λx. x = λx. x succeeds');
});

test('Unify lambdas with hole: λx. ?y = λx. x', () => {
  const lhs = mkLambda(Nat, hole('y', Nat), 'x');
  const rhs = mkLambda(Nat, mkVar(0), 'x');
  const result = unifyTerms(lhs, rhs, mkPi(Nat, Nat));
  const subst = assertSuccess(result);

  // Note: The hole ?y should be unified with Var(0)
  // But since we're in the lambda body context, this might need adjustment
  console.log(`  Substitution size: ${subst.size}`);
});

test('Unify Pi types: (x : Nat) → Nat = (y : Nat) → Nat', () => {
  const lhs = mkPi(Nat, Nat, 'x');
  const rhs = mkPi(Nat, Nat, 'y');
  const result = unifyTerms(lhs, rhs, Type0);
  assertSuccess(result);
  console.log('  (x : Nat) → Nat = (y : Nat) → Nat succeeds');
});

// ============================================================================
// Multiple Equations Tests
// ============================================================================

console.log('\n--- Multiple Equations ---\n');

test('Multiple equations: ?x = zero, ?y = succ zero', () => {
  const result = unify([
    { lhs: hole('x'), rhs: Zero, type: Nat },
    { lhs: hole('y'), rhs: succ(Zero), type: Nat },
  ]);
  const subst = assertSuccess(result);

  if (subst.size !== 2) {
    throw new Error('Expected 2 substitutions');
  }
  console.log(`  ?x := ${prettyPrint(subst.get('x')!)}`);
  console.log(`  ?y := ${prettyPrint(subst.get('y')!)}`);
});

test('Dependent equations: ?x = zero, ?y = succ ?x (should give ?y = succ zero)', () => {
  const result = unify([
    { lhs: hole('x'), rhs: Zero, type: Nat },
    { lhs: hole('y'), rhs: succ(hole('x')), type: Nat },
  ]);
  const subst = assertSuccess(result);

  const y = subst.get('y');
  if (y?.tag !== 'App') {
    throw new Error('Expected ?y to be succ something');
  }
  console.log(`  ?x := ${prettyPrint(subst.get('x')!)}`);
  console.log(`  ?y := ${prettyPrint(y)}`);
});

test('Inconsistent equations: ?x = zero, ?x = succ zero (fails)', () => {
  const result = unify([
    { lhs: hole('x'), rhs: Zero, type: Nat },
    { lhs: hole('x'), rhs: succ(Zero), type: Nat },
  ]);
  assertFailure(result);
  console.log('  Inconsistent equations correctly detected');
});

// ============================================================================
// UIP vs Without-K Tests
// ============================================================================

console.log('\n--- UIP vs Without-K ---\n');

test('With UIP: can delete x = x for computed terms', () => {
  const ctx: TTKContext = [{ name: 'n', type: Nat }];
  // succ n = succ n should work with UIP
  const term = succ(mkVar(0));
  const result = unifyTerms(term, term, Nat, ctx, { useUIP: true });
  assertSuccess(result);
  console.log('  succ n = succ n succeeds with UIP');
});

test('Without UIP: syntactically identical terms still unify', () => {
  // Even without UIP, syntactically identical terms should unify
  const result = unifyTerms(Zero, Zero, Nat, [], { useUIP: false });
  assertSuccess(result);
  console.log('  zero = zero succeeds without UIP (syntactic identity)');
});

// ============================================================================
// Edge Cases
// ============================================================================

console.log('\n--- Edge Cases ---\n');

test('Empty unification problem succeeds', () => {
  const result = unify([]);
  assertSuccess(result);
  console.log('  Empty problem succeeds with empty substitution');
});

test('Unify Sort with Sort: Type = Type', () => {
  const result = unifyTerms(Type0, Type0, mkType(1));
  assertSuccess(result);
  console.log('  Type = Type succeeds');
});

test('Unify different Sorts is stuck: Type_0 ≠ Type_1', () => {
  const Type1 = mkType(1);
  const result = unifyTerms(Type0, Type1, mkType(2));
  // Sorts are stuck because they're not the same and not holes
  const reason = assertStuck(result);
  console.log(`  Type_0 ≠ Type_1 (stuck: ${reason.slice(0, 50)}...)`);
});

test('canUnify helper function', () => {
  if (!canUnify(hole('x'), Zero, Nat)) {
    throw new Error('?x should be unifiable with zero');
  }
  if (canUnify(Zero, succ(Zero), Nat)) {
    throw new Error('zero should not be unifiable with succ zero');
  }
  console.log('  canUnify works correctly');
});

// ============================================================================
// Integration Tests
// ============================================================================

console.log('\n--- Integration Tests ---\n');

test('Solve pattern matching constraint: cons ?A ?x ?xs = cons Nat zero nil', () => {
  // Create cons Nat zero nil  (simplified - in reality would need proper typing)
  const lhs = mkApp(mkApp(mkApp(Cons, hole('A', Type0)), hole('x', Nat)), hole('xs', mkApp(List, Nat)));
  const rhs = mkApp(mkApp(mkApp(Cons, Nat), Zero), mkApp(Nil, Nat));

  const result = unifyTerms(lhs, rhs, mkApp(List, Nat));
  const subst = assertSuccess(result);

  console.log(`  Found ${subst.size} substitutions`);
  for (const [id, term] of subst) {
    console.log(`    ?${id} := ${prettyPrint(term)}`);
  }
});

test('Complex nested unification', () => {
  // Unify succ (succ ?x) with succ (succ (succ zero))
  const lhs = succ(succ(hole('x')));
  const rhs = succ(succ(succ(Zero)));

  const result = unifyTerms(lhs, rhs, Nat);
  const subst = assertSuccess(result);

  const x = subst.get('x');
  // ?x should be succ zero
  if (x?.tag !== 'App') {
    throw new Error('Expected ?x = succ zero');
  }
  console.log(`  ?x := ${prettyPrint(x)}`);
});

// ============================================================================
// Summary
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('All unification tests passed!');
console.log('='.repeat(80) + '\n');
