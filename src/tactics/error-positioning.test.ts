/**
 * Test that tactic errors are positioned correctly in the source code.
 */

import { describe, test, expect } from 'vitest';
import { compileTTFromText } from '../compiler/compile';
import { serializeIndexPath } from '../types/source-position';

describe('Tactic error positioning', () => {
  test('error on specific tactic line, not entire tactic block', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

-- This proof should fail on line 11 (the "exact Zero" tactic)
testProof : Equal (Succ Zero) (Succ Zero) := by
  exact Zero
`;

    const result = compileTTFromText(source);

    // Should have compilation errors
    expect(result.success).toBe(false);
    expect(result.totalCheckErrors).toBeGreaterThan(0);

    // Find the testProof declaration
    const testProofDecl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'testProof');

    expect(testProofDecl).toBeDefined();
    expect(testProofDecl!.checkSuccess).toBe(false);
    expect(testProofDecl!.checkErrors.length).toBeGreaterThan(0);

    // Check that the error has an indexPath pointing to the specific tactic
    const error = testProofDecl!.checkErrors[0];
    console.log('Error structure:', JSON.stringify(error, null, 2));
    console.log('Error type:', typeof error);
    console.log('Error.env:', error.env);
    console.log('Error.env.indexPath:', error.env?.indexPath);

    expect(error.env.indexPath).toBeDefined();
    expect(error.env.indexPath.length).toBeGreaterThan(0);

    // The indexPath should include 'tactics' and an array index
    const pathStr = serializeIndexPath(error.env.indexPath);
    console.log('Error indexPath:', pathStr);
    console.log('Error message:', error.message);

    // Should point to value.tactics[0], not just value
    expect(pathStr).toContain('tactics');
    expect(pathStr).not.toBe('value'); // Should be more specific than just 'value'

    // If we have a sourceMap, check that we can map to a source range
    if (testProofDecl!.sourceMap) {
      const range = testProofDecl!.sourceMap.get(pathStr);
      if (range) {
        console.log('Error range:', {
          start: { line: range.start.line, col: range.start.col },
          end: { line: range.end.line, col: range.end.col }
        });

        // The error should be on line 11 (or around there, depending on how we count)
        // In the source string above, "exact Zero" is on line 11
        expect(range.start.line).toBeGreaterThan(9); // Should be after the "by" line
      }
    }
  });

  test('error on nested branch tactic', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

testProof : (n : Nat) -> Equal n n := by
  intro n
  cases n with
  | Zero => exact refl
  | Succ m => exact Zero
`;

    const result = compileTTFromText(source);

    // Should have compilation errors
    expect(result.success).toBe(false);

    // Find the testProof declaration
    const testProofDecl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'testProof');

    expect(testProofDecl).toBeDefined();
    expect(testProofDecl!.checkSuccess).toBe(false);
    expect(testProofDecl!.checkErrors.length).toBeGreaterThan(0);

    // Check that the error has an indexPath pointing to the specific branch tactic
    const error = testProofDecl!.checkErrors[0];
    const pathStr = serializeIndexPath(error.env.indexPath);
    console.log('Branch error indexPath:', pathStr);
    console.log('Branch error message:', error.message);

    // Should point to a specific tactic within a branch
    expect(pathStr).toContain('tactics');
    expect(pathStr).toContain('caseBranches');
  });
});
