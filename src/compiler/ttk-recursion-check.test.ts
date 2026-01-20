/**
 * Tests for structural recursion analysis (TTK layer)
 */

import { analyzeRecursionTTK, RecursionAnalysis } from './ttk-recursion-check';
import { TTKTerm, TTKClause, mkVar, mkConst, mkApp, mkPi, mkLambda, mkType } from './kernel';

function test(description: string, fn: () => void): void {
  try {
    fn();
    console.log(`✓ ${description}`);
  } catch (error) {
    console.error(`✗ ${description}`);
    throw error;
  }
}

function assert(condition: boolean, message?: string): void {
  if (!condition) {
    throw new Error(message || 'Assertion failed');
  }
}

console.log('\n' + '='.repeat(80));
console.log('STRUCTURAL RECURSION CHECK TESTS');
console.log('='.repeat(80) + '\n');

// ============================================================================
// Helper Functions
// ============================================================================

const nat = mkConst('Nat');

function mkMatch(scrutinee: TTKTerm, clauses: TTKClause[]): TTKTerm {
  return { tag: 'Match', scrutinee, clauses };
}

function mkHole(id: string): TTKTerm {
  return { tag: 'Hole', id };
}

// ============================================================================
// Non-recursive Functions
// ============================================================================

test('Non-recursive function: identity', () => {
  // id x = x
  const body = mkVar(0);
  const analysis = analyzeRecursionTTK('id', body);

  assert(analysis.safeRecursion.length === 0, 'Should have no safe recursion');
  assert(analysis.unsafeRecursion.length === 0, 'Should have no unsafe recursion');
});

test('Non-recursive function: constant', () => {
  // const x y = x
  const body = mkVar(1);
  const analysis = analyzeRecursionTTK('const', body);

  assert(analysis.safeRecursion.length === 0, 'Should have no safe recursion');
  assert(analysis.unsafeRecursion.length === 0, 'Should have no unsafe recursion');
});

// ============================================================================
// Safe Structural Recursion
// ============================================================================

test('Safe recursion: plus Zero b = b', () => {
  // plus : Nat -> Nat -> Nat
  // | Zero, b => b
  // | Succ a, b => Succ (plus a b)

  const plusBody: TTKTerm = mkMatch(mkHole('args'), [
    // Zero, b => b
    {
      patterns: [
        { tag: 'PCtor', name: 'Zero', args: [] },
        { tag: 'PVar', name: 'b' }
      ],
      rhs: mkVar(0) // b
    },
    // Succ a, b => Succ (plus a b)
    {
      patterns: [
        { tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'a' }] },
        { tag: 'PVar', name: 'b' }
      ],
      rhs: mkApp(mkConst('Succ'), mkApp(mkApp(mkConst('plus'), mkVar(1)), mkVar(0))) // Succ (plus a b)
    }
  ]);

  const analysis = analyzeRecursionTTK('plus', plusBody);

  assert(analysis.safeRecursion.length === 1, `Should have 1 safe recursive call, got ${analysis.safeRecursion.length}`);
  assert(analysis.unsafeRecursion.length === 0, `Should have no unsafe recursion, got ${analysis.unsafeRecursion.length}`);
});

test('Safe recursion: factorial', () => {
  // fact : Nat -> Nat
  // | Zero => Succ Zero
  // | Succ n => mult (Succ n) (fact n)

  const factBody: TTKTerm = mkMatch(mkHole('args'), [
    {
      patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }],
      rhs: mkApp(mkConst('Succ'), mkConst('Zero'))
    },
    {
      patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] }],
      rhs: mkApp(
        mkApp(mkConst('mult'), mkApp(mkConst('Succ'), mkVar(0))),
        mkApp(mkConst('fact'), mkVar(0)) // fact n
      )
    }
  ]);

  const analysis = analyzeRecursionTTK('fact', factBody);

  assert(analysis.safeRecursion.length === 1, 'Should have 1 safe recursive call');
  assert(analysis.unsafeRecursion.length === 0, 'Should have no unsafe recursion');
});

test('Safe recursion: multiple recursive calls in different branches', () => {
  // f : Nat -> Nat -> Nat
  // | Zero, b => b
  // | Succ a, Zero => f a Zero
  // | Succ a, Succ b => f a b

  const fBody: TTKTerm = mkMatch(mkHole('args'), [
    {
      patterns: [
        { tag: 'PCtor', name: 'Zero', args: [] },
        { tag: 'PVar', name: 'b' }
      ],
      rhs: mkVar(0)
    },
    {
      patterns: [
        { tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'a' }] },
        { tag: 'PCtor', name: 'Zero', args: [] }
      ],
      rhs: mkApp(mkApp(mkConst('f'), mkVar(0)), mkConst('Zero')) // f a Zero
    },
    {
      patterns: [
        { tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'a' }] },
        { tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'b' }] }
      ],
      rhs: mkApp(mkApp(mkConst('f'), mkVar(1)), mkVar(0)) // f a b
    }
  ]);

  const analysis = analyzeRecursionTTK('f', fBody);

  assert(analysis.safeRecursion.length === 2, `Should have 2 safe recursive calls, got ${analysis.safeRecursion.length}`);
  assert(analysis.unsafeRecursion.length === 0, 'Should have no unsafe recursion');
});

// ============================================================================
// Unsafe Recursion
// ============================================================================

test('Unsafe recursion: same argument', () => {
  // loop : Nat -> Nat
  // | n => loop n

  const loopBody: TTKTerm = mkMatch(mkHole('args'), [
    {
      patterns: [{ tag: 'PVar', name: 'n' }],
      rhs: mkApp(mkConst('loop'), mkVar(0)) // loop n
    }
  ]);

  const analysis = analyzeRecursionTTK('loop', loopBody);

  assert(analysis.safeRecursion.length === 0, 'Should have no safe recursion');
  assert(analysis.unsafeRecursion.length === 1, `Should have 1 unsafe recursive call, got ${analysis.unsafeRecursion.length}`);
});

test('Unsafe recursion: growing argument', () => {
  // grows : Nat -> Nat
  // | n => grows (Succ n)

  const growsBody: TTKTerm = mkMatch(mkHole('args'), [
    {
      patterns: [{ tag: 'PVar', name: 'n' }],
      rhs: mkApp(mkConst('grows'), mkApp(mkConst('Succ'), mkVar(0))) // grows (Succ n)
    }
  ]);

  const analysis = analyzeRecursionTTK('grows', growsBody);

  assert(analysis.safeRecursion.length === 0, 'Should have no safe recursion');
  assert(analysis.unsafeRecursion.length === 1, 'Should have 1 unsafe recursive call');
});

test('Unsafe recursion: complex expression instead of variable', () => {
  // bad : Nat -> Nat
  // | Succ a => bad (Succ a)  -- same size, not smaller

  const badBody: TTKTerm = mkMatch(mkHole('args'), [
    {
      patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }],
      rhs: mkConst('Zero')
    },
    {
      patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'a' }] }],
      rhs: mkApp(mkConst('bad'), mkApp(mkConst('Succ'), mkVar(0))) // bad (Succ a)
    }
  ]);

  const analysis = analyzeRecursionTTK('bad', badBody);

  assert(analysis.safeRecursion.length === 0, 'Should have no safe recursion');
  assert(analysis.unsafeRecursion.length === 1, 'Should have 1 unsafe recursive call');
});

test('Unsafe recursion: outside pattern matching context', () => {
  // noMatch : Nat -> Nat
  // noMatch x = noMatch x  -- no pattern match, just a definition

  const noMatchBody: TTKTerm = mkApp(mkConst('noMatch'), mkVar(0));

  const analysis = analyzeRecursionTTK('noMatch', noMatchBody);

  assert(analysis.safeRecursion.length === 0, 'Should have no safe recursion');
  assert(analysis.unsafeRecursion.length === 1, 'Should have 1 unsafe recursive call');
  assert(
    analysis.unsafeRecursion[0].error.includes('outside') ||
    analysis.unsafeRecursion[0].error.includes('no structurally smaller'),
    `Error should mention outside pattern matching, got: ${analysis.unsafeRecursion[0].error}`
  );
});

test('Unsafe recursion: unapplied self-reference', () => {
  // selfRef : Nat -> Nat
  // selfRef x = selfRef  -- just the name, not applied

  const selfRefBody: TTKTerm = mkConst('selfRef');

  const analysis = analyzeRecursionTTK('selfRef', selfRefBody);

  assert(analysis.safeRecursion.length === 0, 'Should have no safe recursion');
  assert(analysis.unsafeRecursion.length === 1, 'Should have 1 unsafe recursive call');
  assert(
    analysis.unsafeRecursion[0].error.includes('without application'),
    `Error should mention unapplied reference, got: ${analysis.unsafeRecursion[0].error}`
  );
});

// ============================================================================
// Mixed Safe and Unsafe
// ============================================================================

test('Mixed recursion: one safe, one unsafe branch', () => {
  // mixed : Nat -> Nat
  // | Zero => mixed Zero      -- unsafe: Zero is not pattern-bound
  // | Succ n => mixed n       -- safe: n is pattern-bound

  const mixedBody: TTKTerm = mkMatch(mkHole('args'), [
    {
      patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }],
      rhs: mkApp(mkConst('mixed'), mkConst('Zero'))
    },
    {
      patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] }],
      rhs: mkApp(mkConst('mixed'), mkVar(0))
    }
  ]);

  const analysis = analyzeRecursionTTK('mixed', mixedBody);

  assert(analysis.safeRecursion.length === 1, `Should have 1 safe recursive call, got ${analysis.safeRecursion.length}`);
  assert(analysis.unsafeRecursion.length === 1, `Should have 1 unsafe recursive call, got ${analysis.unsafeRecursion.length}`);
});

// ============================================================================
// Edge Cases
// ============================================================================

test('Edge case: empty match', () => {
  // empty : Void -> Nat
  // (no clauses - absurd pattern)

  const emptyBody: TTKTerm = mkMatch(mkHole('args'), []);

  const analysis = analyzeRecursionTTK('empty', emptyBody);

  assert(analysis.safeRecursion.length === 0, 'Should have no safe recursion');
  assert(analysis.unsafeRecursion.length === 0, 'Should have no unsafe recursion');
});

test('Edge case: deeply nested recursion in lambda', () => {
  // nested : Nat -> Nat -> Nat
  // | Succ a, b => (\x => nested a x) b

  const nestedBody: TTKTerm = mkMatch(mkHole('args'), [
    {
      patterns: [
        { tag: 'PCtor', name: 'Zero', args: [] },
        { tag: 'PVar', name: 'b' }
      ],
      rhs: mkVar(0)
    },
    {
      patterns: [
        { tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'a' }] },
        { tag: 'PVar', name: 'b' }
      ],
      rhs: mkApp(
        mkLambda(nat, mkApp(mkApp(mkConst('nested'), mkVar(2)), mkVar(0)), 'x'),
        mkVar(0)
      )
    }
  ]);

  const analysis = analyzeRecursionTTK('nested', nestedBody);

  // The recursive call uses `a` (shifted to index 2 under the lambda) which is structurally smaller
  assert(analysis.safeRecursion.length === 1, `Should have 1 safe recursive call, got ${analysis.safeRecursion.length}`);
  assert(analysis.unsafeRecursion.length === 0, 'Should have no unsafe recursion');
});

test('Edge case: recursion with wildcard patterns', () => {
  // withWild : Nat -> Nat -> Nat
  // | Succ a, _ => withWild a Zero
  // | _, b => b

  const withWildBody: TTKTerm = mkMatch(mkHole('args'), [
    {
      patterns: [
        { tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'a' }] },
        { tag: 'PWild', name: '_w0' }
      ],
      rhs: mkApp(mkApp(mkConst('withWild'), mkVar(1)), mkConst('Zero'))
    },
    {
      patterns: [
        { tag: 'PWild', name: '_w1' },
        { tag: 'PVar', name: 'b' }
      ],
      rhs: mkVar(0)
    }
  ]);

  const analysis = analyzeRecursionTTK('withWild', withWildBody);

  assert(analysis.safeRecursion.length === 1, `Should have 1 safe recursive call, got ${analysis.safeRecursion.length}`);
  assert(analysis.unsafeRecursion.length === 0, 'Should have no unsafe recursion');
});

// ============================================================================
// Summary
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('ALL STRUCTURAL RECURSION CHECK TESTS PASSED');
console.log('='.repeat(80) + '\n');
