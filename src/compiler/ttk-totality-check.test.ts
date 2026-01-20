/**
 * Tests for totality/exhaustiveness checking (TTK layer)
 */

import {
  analyzeTotality,
  checkFunctionTotality,
  formatMissingCase,
  prettyPrintSplitTree,
  TotalityAnalysis,
  resetTotalityWildcardCounter
} from './ttk-totality-check';
import { TTKTerm, TTKClause, TTKPattern, mkVar, mkConst, mkPi, mkType } from './kernel';
import { createDefinitionsMap, addInductiveDefinition, DefinitionsMap } from './term';

function test(description: string, fn: () => void): void {
  try {
    resetTotalityWildcardCounter();
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
console.log('TOTALITY/EXHAUSTIVENESS CHECK TESTS');
console.log('='.repeat(80) + '\n');

// ============================================================================
// Helper Functions
// ============================================================================

function makeNatDefinitions(): DefinitionsMap {
  let defs = createDefinitionsMap();
  const nat = mkConst('Nat');
  defs = addInductiveDefinition(defs, 'Nat', mkType(1), [
    { name: 'Zero', type: nat },
    { name: 'Succ', type: mkPi(nat, nat, 'n') }
  ], []);
  return defs;
}

function makeBoolDefinitions(): DefinitionsMap {
  let defs = createDefinitionsMap();
  const bool = mkConst('Bool');
  defs = addInductiveDefinition(defs, 'Bool', mkType(1), [
    { name: 'True', type: bool },
    { name: 'False', type: bool }
  ], []);
  return defs;
}

function makeNatAndBoolDefinitions(): DefinitionsMap {
  let defs = createDefinitionsMap();
  const nat = mkConst('Nat');
  const bool = mkConst('Bool');
  defs = addInductiveDefinition(defs, 'Nat', mkType(1), [
    { name: 'Zero', type: nat },
    { name: 'Succ', type: mkPi(nat, nat, 'n') }
  ], []);
  defs = addInductiveDefinition(defs, 'Bool', mkType(1), [
    { name: 'True', type: bool },
    { name: 'False', type: bool }
  ], []);
  return defs;
}

const nat = mkConst('Nat');
const bool = mkConst('Bool');

// Dummy RHS for clauses (we don't care about RHS for totality checking)
const dummyRhs: TTKTerm = mkVar(0);

// ============================================================================
// Exhaustive Patterns
// ============================================================================

test('Exhaustive: single wildcard pattern', () => {
  const clauses: TTKClause[] = [
    { patterns: [{ tag: 'PVar', name: 'x' }], rhs: dummyRhs }
  ];

  const analysis = analyzeTotality(clauses, [nat], makeNatDefinitions());

  assert(analysis.exhaustive, 'Single wildcard should be exhaustive');
  assert(analysis.missingCases.length === 0, 'Should have no missing cases');
});

test('Exhaustive: both Bool constructors', () => {
  const clauses: TTKClause[] = [
    { patterns: [{ tag: 'PCtor', name: 'True', args: [] }], rhs: dummyRhs },
    { patterns: [{ tag: 'PCtor', name: 'False', args: [] }], rhs: dummyRhs }
  ];

  const analysis = analyzeTotality(clauses, [bool], makeBoolDefinitions());

  assert(analysis.exhaustive, 'Both Bool constructors should be exhaustive');
  assert(analysis.missingCases.length === 0, 'Should have no missing cases');
});

test('Exhaustive: all Nat constructors', () => {
  const clauses: TTKClause[] = [
    { patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: dummyRhs },
    { patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] }], rhs: dummyRhs }
  ];

  const analysis = analyzeTotality(clauses, [nat], makeNatDefinitions());

  assert(analysis.exhaustive, 'Zero and Succ should be exhaustive');
  assert(analysis.missingCases.length === 0, 'Should have no missing cases');
});

test('Exhaustive: nested Nat patterns', () => {
  // f Zero = ...
  // f (Succ Zero) = ...
  // f (Succ (Succ n)) = ...
  const clauses: TTKClause[] = [
    { patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: dummyRhs },
    {
      patterns: [{
        tag: 'PCtor', name: 'Succ', args: [
          { tag: 'PCtor', name: 'Zero', args: [] }
        ]
      }],
      rhs: dummyRhs
    },
    {
      patterns: [{
        tag: 'PCtor', name: 'Succ', args: [
          { tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] }
        ]
      }],
      rhs: dummyRhs
    }
  ];

  const analysis = analyzeTotality(clauses, [nat], makeNatDefinitions());

  assert(analysis.exhaustive, 'Nested Nat patterns should be exhaustive');
  assert(analysis.missingCases.length === 0, 'Should have no missing cases');
});

test('Exhaustive: two-argument function', () => {
  // plus Zero b = b
  // plus (Succ a) b = ...
  const clauses: TTKClause[] = [
    {
      patterns: [
        { tag: 'PCtor', name: 'Zero', args: [] },
        { tag: 'PVar', name: 'b' }
      ],
      rhs: dummyRhs
    },
    {
      patterns: [
        { tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'a' }] },
        { tag: 'PVar', name: 'b' }
      ],
      rhs: dummyRhs
    }
  ];

  const analysis = analyzeTotality(clauses, [nat, nat], makeNatDefinitions());

  assert(analysis.exhaustive, 'Two-argument plus should be exhaustive');
  assert(analysis.missingCases.length === 0, 'Should have no missing cases');
});

test('Exhaustive: wildcard at the end', () => {
  // f Zero = ...
  // f _ = ...
  const clauses: TTKClause[] = [
    { patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: dummyRhs },
    { patterns: [{ tag: 'PVar', name: 'x' }], rhs: dummyRhs }
  ];

  const analysis = analyzeTotality(clauses, [nat], makeNatDefinitions());

  assert(analysis.exhaustive, 'Zero + wildcard should be exhaustive');
  assert(analysis.missingCases.length === 0, 'Should have no missing cases');
});

// ============================================================================
// Non-Exhaustive Patterns (Missing Cases)
// ============================================================================

test('Non-exhaustive: missing Zero case', () => {
  const clauses: TTKClause[] = [
    { patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] }], rhs: dummyRhs }
  ];

  const analysis = analyzeTotality(clauses, [nat], makeNatDefinitions());

  assert(!analysis.exhaustive, 'Should not be exhaustive without Zero');
  assert(analysis.missingCases.length === 1, `Should have 1 missing case, got ${analysis.missingCases.length}`);

  const formatted = formatMissingCase('f', analysis.missingCases[0]);
  assert(formatted.includes('Zero'), `Missing case should mention Zero, got: ${formatted}`);
});

test('Non-exhaustive: missing Succ case', () => {
  const clauses: TTKClause[] = [
    { patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: dummyRhs }
  ];

  const analysis = analyzeTotality(clauses, [nat], makeNatDefinitions());

  assert(!analysis.exhaustive, 'Should not be exhaustive without Succ');
  assert(analysis.missingCases.length === 1, `Should have 1 missing case, got ${analysis.missingCases.length}`);

  const formatted = formatMissingCase('f', analysis.missingCases[0]);
  assert(formatted.includes('Succ'), `Missing case should mention Succ, got: ${formatted}`);
});

test('Non-exhaustive: missing nested case', () => {
  // f Zero = ...
  // f (Succ (Succ n)) = ...
  // Missing: f (Succ Zero)
  const clauses: TTKClause[] = [
    { patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: dummyRhs },
    {
      patterns: [{
        tag: 'PCtor', name: 'Succ', args: [
          { tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] }
        ]
      }],
      rhs: dummyRhs
    }
  ];

  const analysis = analyzeTotality(clauses, [nat], makeNatDefinitions());

  assert(!analysis.exhaustive, 'Should not be exhaustive without Succ Zero');
  assert(analysis.missingCases.length === 1, `Should have 1 missing case, got ${analysis.missingCases.length}`);

  const formatted = formatMissingCase('f', analysis.missingCases[0]);
  assert(formatted.includes('Succ') && formatted.includes('Zero'),
    `Missing case should be (Succ Zero), got: ${formatted}`);
});

test('Non-exhaustive: multiple missing cases', () => {
  // f Zero Zero = ...
  // Missing cases (using wildcards for compact representation):
  //   f Zero (Succ _)
  //   f (Succ _) _
  const clauses: TTKClause[] = [
    {
      patterns: [
        { tag: 'PCtor', name: 'Zero', args: [] },
        { tag: 'PCtor', name: 'Zero', args: [] }
      ],
      rhs: dummyRhs
    }
  ];

  const analysis = analyzeTotality(clauses, [nat, nat], makeNatDefinitions());

  assert(!analysis.exhaustive, 'Should not be exhaustive');
  // The algorithm uses wildcards to compactly represent missing cases
  assert(analysis.missingCases.length >= 2, `Should have at least 2 missing cases, got ${analysis.missingCases.length}`);
});

test('Non-exhaustive: no clauses at all', () => {
  const clauses: TTKClause[] = [];

  const analysis = analyzeTotality(clauses, [nat], makeNatDefinitions());

  assert(!analysis.exhaustive, 'Empty clauses should not be exhaustive');
  assert(analysis.missingCases.length === 1, 'Should have 1 missing case (wildcard)');
});

// ============================================================================
// Inaccessible Clauses
// ============================================================================

test('Inaccessible: duplicate clause', () => {
  const clauses: TTKClause[] = [
    { patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: dummyRhs },
    { patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] }], rhs: dummyRhs },
    { patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: dummyRhs } // duplicate
  ];

  const analysis = analyzeTotality(clauses, [nat], makeNatDefinitions());

  assert(analysis.exhaustive, 'Should be exhaustive');
  assert(analysis.inaccessibleClauses.length === 1, `Should have 1 inaccessible clause, got ${analysis.inaccessibleClauses.length}`);
  assert(analysis.inaccessibleClauses[0] === 2, 'Third clause (index 2) should be inaccessible');
});

test('Inaccessible: shadowed by earlier wildcard', () => {
  const clauses: TTKClause[] = [
    { patterns: [{ tag: 'PVar', name: 'x' }], rhs: dummyRhs },
    { patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: dummyRhs } // shadowed
  ];

  const analysis = analyzeTotality(clauses, [nat], makeNatDefinitions());

  assert(analysis.exhaustive, 'Should be exhaustive');
  assert(analysis.inaccessibleClauses.length === 1, 'Should have 1 inaccessible clause');
  assert(analysis.inaccessibleClauses[0] === 1, 'Second clause should be inaccessible');
});

test('Inaccessible: multiple shadowed clauses', () => {
  const clauses: TTKClause[] = [
    { patterns: [{ tag: 'PVar', name: 'x' }], rhs: dummyRhs },
    { patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: dummyRhs },
    { patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] }], rhs: dummyRhs }
  ];

  const analysis = analyzeTotality(clauses, [nat], makeNatDefinitions());

  assert(analysis.exhaustive, 'Should be exhaustive');
  assert(analysis.inaccessibleClauses.length === 2, 'Should have 2 inaccessible clauses');
  assert(analysis.inaccessibleClauses.includes(1), 'Clause 1 should be inaccessible');
  assert(analysis.inaccessibleClauses.includes(2), 'Clause 2 should be inaccessible');
});

// ============================================================================
// Edge Cases
// ============================================================================

test('Edge case: no arguments (constant function)', () => {
  const clauses: TTKClause[] = [
    { patterns: [], rhs: dummyRhs }
  ];

  const analysis = analyzeTotality(clauses, [], makeNatDefinitions());

  assert(analysis.exhaustive, 'Constant function should be exhaustive');
  assert(analysis.missingCases.length === 0, 'Should have no missing cases');
});

test('Edge case: multiple constant clauses', () => {
  const clauses: TTKClause[] = [
    { patterns: [], rhs: dummyRhs },
    { patterns: [], rhs: mkVar(1) } // different RHS but same pattern
  ];

  const analysis = analyzeTotality(clauses, [], makeNatDefinitions());

  assert(analysis.exhaustive, 'Should be exhaustive');
  assert(analysis.inaccessibleClauses.length === 1, 'Second clause should be inaccessible');
});

test('Edge case: PWild patterns', () => {
  const clauses: TTKClause[] = [
    { patterns: [{ tag: 'PWild', name: '_w0' }], rhs: dummyRhs }
  ];

  const analysis = analyzeTotality(clauses, [nat], makeNatDefinitions());

  assert(analysis.exhaustive, 'PWild should be exhaustive like PVar');
  assert(analysis.missingCases.length === 0, 'Should have no missing cases');
});

test('Edge case: mixed PVar and PWild', () => {
  const clauses: TTKClause[] = [
    {
      patterns: [
        { tag: 'PCtor', name: 'Zero', args: [] },
        { tag: 'PWild', name: '_w0' }
      ],
      rhs: dummyRhs
    },
    {
      patterns: [
        { tag: 'PVar', name: 'x' },
        { tag: 'PVar', name: 'y' }
      ],
      rhs: dummyRhs
    }
  ];

  const analysis = analyzeTotality(clauses, [nat, nat], makeNatDefinitions());

  assert(analysis.exhaustive, 'Should be exhaustive');
  assert(analysis.missingCases.length === 0, 'Should have no missing cases');
});

// ============================================================================
// High-Level API: checkFunctionTotality
// ============================================================================

test('checkFunctionTotality: excludes function name from constructors', () => {
  // Create definitions with a function that returns Nat
  let defs = makeNatDefinitions();
  // (In a real scenario, the function would be in the definitions)
  // The key point is that the function name is excluded from constructor lookup

  const functionType = mkPi(nat, nat, 'n');
  const clauses: TTKClause[] = [
    { patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: mkConst('Zero') },
    { patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] }], rhs: mkVar(0) }
  ];

  const analysis = checkFunctionTotality('myFunc', functionType, clauses, defs);

  assert(analysis.exhaustive, 'Should be exhaustive');
});

// ============================================================================
// Formatting Tests
// ============================================================================

test('formatMissingCase: simple wildcard', () => {
  const missing = [{ tag: 'MWild' as const }];
  const formatted = formatMissingCase('f', missing);
  assert(formatted === 'f _', `Expected 'f _', got '${formatted}'`);
});

test('formatMissingCase: single constructor', () => {
  const missing = [{ tag: 'MCtor' as const, name: 'Zero', args: [] }];
  const formatted = formatMissingCase('f', missing);
  assert(formatted === 'f Zero', `Expected 'f Zero', got '${formatted}'`);
});

test('formatMissingCase: constructor with args', () => {
  const missing = [{
    tag: 'MCtor' as const, name: 'Succ', args: [
      { tag: 'MWild' as const }
    ]
  }];
  const formatted = formatMissingCase('f', missing);
  assert(formatted === 'f (Succ _)', `Expected 'f (Succ _)', got '${formatted}'`);
});

test('formatMissingCase: nested constructors', () => {
  const missing = [{
    tag: 'MCtor' as const, name: 'Succ', args: [
      { tag: 'MCtor' as const, name: 'Zero', args: [] }
    ]
  }];
  const formatted = formatMissingCase('f', missing);
  assert(formatted === 'f (Succ Zero)', `Expected 'f (Succ Zero)', got '${formatted}'`);
});

test('formatMissingCase: multiple arguments', () => {
  const missing = [
    { tag: 'MCtor' as const, name: 'Zero', args: [] },
    { tag: 'MCtor' as const, name: 'Succ', args: [{ tag: 'MWild' as const }] }
  ];
  const formatted = formatMissingCase('plus', missing);
  assert(formatted === 'plus Zero (Succ _)', `Expected 'plus Zero (Succ _)', got '${formatted}'`);
});

// ============================================================================
// prettyPrintSplitTree Tests
// ============================================================================

test('prettyPrintSplitTree: leaf node', () => {
  const analysis = analyzeTotality(
    [{ patterns: [{ tag: 'PVar', name: 'x' }], rhs: dummyRhs }],
    [nat],
    makeNatDefinitions()
  );

  const printed = prettyPrintSplitTree(analysis.splitTree);
  assert(printed.includes('Leaf'), 'Should include Leaf');
  assert(printed.includes('clause=0'), 'Should reference clause 0');
});

test('prettyPrintSplitTree: split node', () => {
  const analysis = analyzeTotality(
    [
      { patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: dummyRhs },
      { patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] }], rhs: dummyRhs }
    ],
    [nat],
    makeNatDefinitions()
  );

  const printed = prettyPrintSplitTree(analysis.splitTree);
  assert(printed.includes('Split'), 'Should include Split');
  assert(printed.includes('Zero'), 'Should include Zero branch');
  assert(printed.includes('Succ'), 'Should include Succ branch');
});

test('prettyPrintSplitTree: missing node', () => {
  const analysis = analyzeTotality(
    [{ patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: dummyRhs }],
    [nat],
    makeNatDefinitions()
  );

  const printed = prettyPrintSplitTree(analysis.splitTree);
  assert(printed.includes('MISSING'), 'Should include MISSING for non-exhaustive');
});

// ============================================================================
// Summary
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('ALL TOTALITY CHECK TESTS PASSED');
console.log('='.repeat(80) + '\n');
