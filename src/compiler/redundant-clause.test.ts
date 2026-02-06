import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Redundant clause detection', () => {
  test('detects redundant clause after wildcard', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

boo : (a b : Nat) -> Nat
boo Zero Zero = Zero
boo a b = Succ Zero
boo a b = Succ (Succ Zero)
`;

    const result = compileTTFromText(source);
    
    const boo = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'boo');

    expect(boo?.checkSuccess).toBe(false);
    expect(boo?.checkErrors.some(e => e.message.includes('Redundant'))).toBe(true);
    expect(boo?.checkErrors.filter(e => e.message.includes('Redundant')).length).toBe(1);
  });

  test('does not mark valid overlapping patterns as redundant', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

foo : (a : Nat) -> Nat
foo Zero = Zero
foo (Succ n) = n
`;

    const result = compileTTFromText(source);
    
    const foo = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'foo');

    expect(foo?.checkSuccess).toBe(true);
  });

  test('detects multiple redundant clauses', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

bar : (a : Nat) -> Nat
bar Zero = Zero
bar a = Succ Zero
bar (Succ n) = n
bar a = Succ (Succ Zero)
`;

    const result = compileTTFromText(source);
    
    const bar = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'bar');

    expect(bar?.checkSuccess).toBe(false);
    const redundantErrors = bar?.checkErrors.filter(e => e.message.includes('Redundant')) || [];
    expect(redundantErrors.length).toBe(2); // Both clauses 2 and 3 are redundant
  });
});
