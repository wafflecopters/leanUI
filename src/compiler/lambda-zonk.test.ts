/**
 * Tests for lambda parameter type zonking.
 *
 * Unannotated lambda parameters (like `\x => ...`) get Holes created by
 * the parser for their types. These Holes should be solved during type
 * checking and the lambda should use the inferred type, not the Hole.
 */

import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Lambda type zonking', () => {
  test('unannotated lambda params should have zonked types', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

swap : {A B C : Type} -> (f : A -> B -> C) -> B -> A -> C
swap f = \\x y => f y x
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const swapDecl = allDecls.find((d: any) => d?.name === 'swap');

    console.log('swap checkSuccess:', swapDecl?.checkSuccess);
    console.log('swap prettyType:', swapDecl?.prettyType);
    console.log('swap prettyValue:', swapDecl?.prettyValue);

    expect(swapDecl?.checkSuccess).toBe(true);

    // The lambda types should be resolved, not showing ?x_type or ?y_type
    const prettyValue = swapDecl?.prettyValue || '';

    // Check for unresolved holes in lambda types
    const hasUnresolvedHoles = prettyValue.includes('?x_type') ||
                               prettyValue.includes('?y_type') ||
                               prettyValue.includes('?_type');

    if (hasUnresolvedHoles) {
      console.log('BUG: Lambda types not zonked:', prettyValue);
    }

    expect(hasUnresolvedHoles).toBe(false);
  });

  test('simple identity lambda should have zonked type', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

id : Nat -> Nat
id = \\x => x
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const idDecl = allDecls.find((d: any) => d?.name === 'id');

    console.log('id prettyValue:', idDecl?.prettyValue);

    expect(idDecl?.checkSuccess).toBe(true);

    const prettyValue = idDecl?.prettyValue || '';
    expect(prettyValue).not.toContain('?');
  });
});
