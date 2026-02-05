/**
 * Test that cursor ANYWHERE on a tactic line returns goal info
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Cursor anywhere on tactic line', () => {
  test('cursor on tactic argument should return goals', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

id : {A : Type} -> A -> A := by
  intro A
  intro a
  exact a
`;

    const result = compileTTFromText(source);
    expect(result.success).toBe(true);

    // Get the 'id' declaration (3rd declaration after Nat and Equal)
    const decl = result.blocks[2].declarations[0];
    expect(decl.name).toBe('id');
    expect(decl.tacticInfoTree).toBeDefined();

    const tree = decl.tacticInfoTree!;

    // Line 10 is "intro A", line 11 is "intro a", line 12 is "exact a"

    // Cursor on line 10 at column 8 (on the 'A' argument) - should return goals after intro A
    const goalsAtIntroA = tree.findGoalsAtPosition(10, 8);
    expect(goalsAtIntroA).not.toBeNull();
    expect(goalsAtIntroA!.length).toBe(1);
    expect(goalsAtIntroA![0].hypotheses.length).toBe(1);
    expect(goalsAtIntroA![0].hypotheses[0].name).toBe('A');

    // Cursor on line 12 at column 9 (on the 'a' in "exact a") - should return no goals (proof complete)
    const goalsAtExactArg = tree.findGoalsAtPosition(12, 9);
    expect(goalsAtExactArg).not.toBeNull();
    expect(goalsAtExactArg!.length).toBe(0); // Proof complete after exact

    // Cursor way past the tactic keyword on line 10 (at column 50) - should still return goals
    const goalsAtEndOfLine = tree.findGoalsAtPosition(10, 50);
    expect(goalsAtEndOfLine).not.toBeNull();
    expect(goalsAtEndOfLine!.length).toBe(1);
  });
});
