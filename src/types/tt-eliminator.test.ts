/**
 * Tests for Eliminator Generation
 *
 * Tests the generation of eliminator (induction principle) type signatures
 * for inductive type definitions.
 */

import { generateEliminator } from './tt-eliminator';
import { InductiveTypeDef } from './tt-examples';
import { TTerm, mkType, mkPi, mkConst, mkApp, mkVar, prettyPrint } from './tt-core';

// ============================================================================
// Test Helpers
// ============================================================================

const Type0 = mkType(0);

function mkInductiveRef(name: string, kind: TTerm): TTerm {
  return mkConst(name, kind);
}

function mkArrow(domain: TTerm, codomain: TTerm): TTerm {
  return mkPi(domain, codomain, '_');
}

/**
 * Run a test with description
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

/**
 * Pretty-print a term for debugging
 */
function debugPrint(term: TTerm): string {
  return prettyPrint(term, []);
}

// ============================================================================
// Example Type Definitions
// ============================================================================

/**
 * Bool : Type
 *
 * inductive Bool : Type where
 *   | true : Bool
 *   | false : Bool
 *
 * Expected eliminator:
 * Bool-elim : (P : Bool → Type) → P true → P false → (b : Bool) → P b
 */
function makeBool(): InductiveTypeDef {
  const Bool = mkInductiveRef('Bool', Type0);

  return {
    name: 'Bool',
    type: Type0,
    constructors: [
      {
        name: 'true',
        type: Bool,
      },
      {
        name: 'false',
        type: Bool,
      },
    ],
  };
}

/**
 * Nat : Type
 *
 * inductive Nat : Type where
 *   | zero : Nat
 *   | succ : Nat → Nat
 *
 * Expected eliminator:
 * Nat-elim : (P : Nat → Type) → P zero → ((n : Nat) → P n → P (succ n)) → (n : Nat) → P n
 */
function makeNat(): InductiveTypeDef {
  const Nat = mkInductiveRef('Nat', Type0);

  return {
    name: 'Nat',
    type: Type0,
    constructors: [
      {
        name: 'zero',
        type: Nat,
      },
      {
        name: 'succ',
        type: mkArrow(Nat, Nat),
      },
    ],
  };
}

/**
 * Unit : Type
 *
 * inductive Unit : Type where
 *   | unit : Unit
 *
 * Expected eliminator:
 * Unit-elim : (P : Unit → Type) → P unit → (u : Unit) → P u
 */
function makeUnit(): InductiveTypeDef {
  const Unit = mkInductiveRef('Unit', Type0);

  return {
    name: 'Unit',
    type: Type0,
    constructors: [
      {
        name: 'unit',
        type: Unit,
      },
    ],
  };
}

/**
 * Empty : Type
 *
 * inductive Empty : Type where
 *   (no constructors)
 *
 * Expected eliminator:
 * Empty-elim : (P : Empty → Type) → (e : Empty) → P e
 */
function makeEmpty(): InductiveTypeDef {
  return {
    name: 'Empty',
    type: Type0,
    constructors: [],
  };
}

// ============================================================================
// Test Utilities
// ============================================================================

/**
 * Check basic structure of an eliminator type.
 * Returns number of Pi binders in the type.
 */
function countPiBinders(type: TTerm): number {
  let count = 0;
  let current = type;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    count++;
    current = current.body;
  }

  return count;
}

/**
 * Extract the motive type (first argument) from an eliminator.
 */
function extractMotive(elimType: TTerm): TTerm | null {
  if (elimType.tag === 'Binder' && elimType.binderKind.tag === 'BPi') {
    return elimType.domain;
  }
  return null;
}

/**
 * Check if the motive has the expected form: D → Type
 */
function isValidMotiveType(motive: TTerm, inductiveName: string): boolean {
  if (motive.tag !== 'Binder' || motive.binderKind.tag !== 'BPi') {
    return false;
  }

  // Domain should be the inductive type
  if (motive.domain.tag !== 'Const' || motive.domain.name !== inductiveName) {
    return false;
  }

  // Codomain should be Type (or some sort)
  return motive.body.tag === 'Sort';
}

// ============================================================================
// Tests
// ============================================================================

function runTests(): void {
  console.log('Running Eliminator Generation Tests...\n');

  console.log('=== Simple Types ===');

  test('Bool eliminator has correct structure', () => {
    const bool = makeBool();
    const elim = generateEliminator(bool);

    console.log('  Bool-elim:', debugPrint(elim));

    // Should have 4 binders: P, case_true, case_false, b
    const numBinders = countPiBinders(elim);
    if (numBinders !== 4) {
      throw new Error(`Expected 4 binders, got ${numBinders}`);
    }

    // First binder should be the motive: Bool → Type
    const motive = extractMotive(elim);
    if (!motive || !isValidMotiveType(motive, 'Bool')) {
      throw new Error('Invalid motive type');
    }
  });

  test('Nat eliminator has correct structure', () => {
    const nat = makeNat();
    const elim = generateEliminator(nat);

    console.log('  Nat-elim:', debugPrint(elim));

    // Should have 4 binders: P, case_zero, case_succ, n
    const numBinders = countPiBinders(elim);
    if (numBinders !== 4) {
      throw new Error(`Expected 4 binders, got ${numBinders}`);
    }

    // First binder should be the motive: Nat → Type
    const motive = extractMotive(elim);
    if (!motive || !isValidMotiveType(motive, 'Nat')) {
      throw new Error('Invalid motive type');
    }
  });

  test('Unit eliminator has correct structure', () => {
    const unit = makeUnit();
    const elim = generateEliminator(unit);

    console.log('  Unit-elim:', debugPrint(elim));

    // Should have 3 binders: P, case_unit, u
    const numBinders = countPiBinders(elim);
    if (numBinders !== 3) {
      throw new Error(`Expected 3 binders, got ${numBinders}`);
    }

    // First binder should be the motive: Unit → Type
    const motive = extractMotive(elim);
    if (!motive || !isValidMotiveType(motive, 'Unit')) {
      throw new Error('Invalid motive type');
    }
  });

  test('Empty eliminator has correct structure', () => {
    const empty = makeEmpty();
    const elim = generateEliminator(empty);

    console.log('  Empty-elim:', debugPrint(elim));

    // Should have 2 binders: P, e (no constructor cases!)
    const numBinders = countPiBinders(elim);
    if (numBinders !== 2) {
      throw new Error(`Expected 2 binders, got ${numBinders}`);
    }

    // First binder should be the motive: Empty → Type
    const motive = extractMotive(elim);
    if (!motive || !isValidMotiveType(motive, 'Empty')) {
      throw new Error('Invalid motive type');
    }
  });

  console.log('\n=== Method Type Structure ===');

  test('Nat succ case has inductive hypothesis', () => {
    const nat = makeNat();
    const elim = generateEliminator(nat);

    // Navigate to the succ case (third binder)
    if (elim.tag !== 'Binder') throw new Error('Expected Pi type');
    const afterMotive = elim.body;
    if (afterMotive.tag !== 'Binder') throw new Error('Expected Pi type');
    const afterZeroCase = afterMotive.body;
    if (afterZeroCase.tag !== 'Binder') throw new Error('Expected Pi type');
    const succCase = afterZeroCase.domain;

    console.log('  Nat succ case:', debugPrint(succCase));

    // The succ case should be: (n : Nat) → P n → P (succ n)
    // It should have 2 binders: n and IH
    const succCaseBinders = countPiBinders(succCase);
    if (succCaseBinders !== 2) {
      throw new Error(`Expected 2 binders in succ case, got ${succCaseBinders}`);
    }
  });

  console.log('\n=== Detailed Structure Tests ===');

  test('Bool eliminator detailed check', () => {
    const bool = makeBool();
    const elim = generateEliminator(bool);

    // Manually check structure:
    // (P : Bool → Type) → P true → P false → (b : Bool) → P b

    // Top level should be Pi
    if (elim.tag !== 'Binder' || elim.binderKind.tag !== 'BPi') {
      throw new Error('Expected Pi type');
    }
    if (elim.name !== 'P') {
      throw new Error(`Expected motive named 'P', got ${elim.name}`);
    }

    // Second level (case_true)
    const level2 = elim.body;
    if (level2.tag !== 'Binder' || level2.binderKind.tag !== 'BPi') {
      throw new Error('Expected Pi type at level 2');
    }
    if (!level2.name.startsWith('case_')) {
      throw new Error(`Expected case name, got ${level2.name}`);
    }

    // Third level (case_false)
    const level3 = level2.body;
    if (level3.tag !== 'Binder' || level3.binderKind.tag !== 'BPi') {
      throw new Error('Expected Pi type at level 3');
    }

    // Fourth level (target)
    const level4 = level3.body;
    if (level4.tag !== 'Binder' || level4.binderKind.tag !== 'BPi') {
      throw new Error('Expected Pi type at level 4');
    }

    // Result should be an application
    const result = level4.body;
    if (result.tag !== 'App') {
      throw new Error('Expected application in result');
    }
  });

  test('Nat succ case has correct IH structure', () => {
    const nat = makeNat();
    const elim = generateEliminator(nat);

    // Navigate to succ case
    if (elim.tag !== 'Binder') throw new Error('Expected Pi');
    const afterMotive = elim.body;
    if (afterMotive.tag !== 'Binder') throw new Error('Expected Pi');
    const afterZeroCase = afterMotive.body;
    if (afterZeroCase.tag !== 'Binder') throw new Error('Expected Pi');
    const succCase = afterZeroCase.domain;

    // Succ case should be: (n : Nat) → (ih : P n) → P (succ n)
    if (succCase.tag !== 'Binder' || succCase.binderKind.tag !== 'BPi') {
      throw new Error('Expected Pi type for succ case');
    }

    // Check it has an IH argument
    const afterN = succCase.body;
    if (afterN.tag !== 'Binder' || afterN.binderKind.tag !== 'BPi') {
      throw new Error('Expected Pi type for IH');
    }

    // IH should be named ih_*
    if (!afterN.name.startsWith('ih_')) {
      throw new Error(`Expected IH name to start with 'ih_', got ${afterN.name}`);
    }
  });

  console.log('\n=== Pretty Print Tests ===');

  test('Nat eliminator pretty-prints without unresolved De Bruijn indices', () => {
    const nat = makeNat();
    const elim = generateEliminator(nat);
    const printed = debugPrint(elim);

    console.log('  Nat-elim printed:', printed);

    // The output should NOT contain #N patterns (unresolved De Bruijn indices)
    // It should use 'P' for the motive, not #3 or #4
    if (printed.includes('#')) {
      throw new Error(`Pretty-printed eliminator contains unresolved De Bruijn indices: ${printed}`);
    }

    // Should contain 'P' as the motive name applied to arguments
    if (!printed.includes('P zero') && !printed.includes('(P zero)')) {
      throw new Error(`Expected 'P zero' in zero case, got: ${printed}`);
    }
  });

  test('Bool eliminator pretty-prints without unresolved De Bruijn indices', () => {
    const bool = makeBool();
    const elim = generateEliminator(bool);
    const printed = debugPrint(elim);

    console.log('  Bool-elim printed:', printed);

    if (printed.includes('#')) {
      throw new Error(`Pretty-printed eliminator contains unresolved De Bruijn indices: ${printed}`);
    }
  });

  console.log('\n✅ All tests passed!');
}

// Run tests
runTests();
