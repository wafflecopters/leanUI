/**
 * Test the exact user scenario: mulZeroLeft proof
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';
import { getTypeAtCursor } from './type-info';

describe('mulZeroLeft exact scenario', () => {
  test('cursor on exact keyword should return tactic goals', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ n) m = Succ (plus n m)

mul : Nat -> Nat -> Nat
mul Zero m = Zero
mul (Succ n) m = plus m (mul n m)

mulZeroLeft : (n : Nat) -> Equal (mul Zero n) Zero := by
  intro n
  exact refl
`;

    const result = compileTTFromText(source);
    console.log('Compile success:', result.success);
    console.log('Num blocks:', result.blocks.length);

    expect(result.success).toBe(true);

    // Find mulZeroLeft declaration
    const decl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'mulZeroLeft');
    console.log('Found mulZeroLeft:', !!decl);
    console.log('Has tacticInfoTree:', !!decl?.tacticInfoTree);
    console.log('Has typeInfoMap:', !!decl?.typeInfoMap);

    expect(decl).toBeDefined();
    expect(decl!.tacticInfoTree).toBeDefined();

    // Line 19 is "  exact refl"
    // Calculate position of line 19, column 3 (start of "exact")
    const lines = source.split('\n');
    let offset = 0;
    for (let i = 0; i < 18; i++) {  // 18 lines before line 19 (0-indexed)
      offset += lines[i].length + 1; // +1 for newline
    }
    offset += 2; // Skip the two spaces to get to column 3

    console.log('Querying at offset:', offset, 'for line 19, col 3');
    console.log('Source Map size:', decl!.sourceMap?.size);
    console.log('TypeInfoMap size:', decl!.typeInfoMap?.size);

    // Query using the API
    const queryResult = getTypeAtCursor(
      offset,
      decl!.sourceMap ?? new Map(),
      decl!.elabMap ?? new Map(),
      decl!.typeInfoMap,
      decl!.tacticInfoTree,
      result.definitions,
      source  // Pass source for position conversion
    );

    console.log('Query result:', queryResult ? { kind: queryResult.kind } : 'undefined');

    if (queryResult?.kind === 'tactic') {
      console.log('  Goal states:', queryResult.goalStates.length);
      queryResult.goalStates.forEach((g, i) => {
        console.log(`  Goal ${i}:`, { hypotheses: g.hypotheses.length, target: g.target.tag });
      });
    }

    expect(queryResult).toBeDefined();
    expect(queryResult!.kind).toBe('tactic');

    if (queryResult && queryResult.kind === 'tactic') {
      expect(queryResult.goalStates.length).toBe(0); // After exact, proof is complete
    }
  });
});
