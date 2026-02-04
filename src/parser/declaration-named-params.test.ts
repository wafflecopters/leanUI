import { describe, test, expect } from 'vitest';
import { parseExpr } from './parser';
import { compileTTFromText } from '../compiler/compile';

describe('Named parameters in declarations', () => {
  test('expression parsing preserves named flag', () => {
    // This should work (from existing tests)
    const expr = parseExpr('{A : Type} -> A -> A');
    console.log('Expression type:', JSON.stringify(expr, null, 2));

    expect(expr.tag).toBe('Binder');
    if (expr.tag === 'Binder') {
      expect(expr.named).toBe(true);
    }
  });

  test('declaration parsing preserves named flag for Binder', () => {
    const source = `foo : {A : Type} -> A -> A`;
    const result = compileTTFromText(source);

    expect(result.blocks[0].parseSuccess).toBe(true);
    const type = result.blocks[0].declarations[0].surfaceType!;

    expect(type.tag).toBe('Binder');
    if (type.tag === 'Binder') {
      expect(type.named).toBe(true); // This works!
    }
  });

  test('declaration parsing preserves named flag for MultiBinder', () => {
    // THIS is where the bug is - MultiBinder with implicit params
    const source = `foo : {a b : Nat} -> a -> b`;
    const result = compileTTFromText(source);

    expect(result.blocks[0].parseSuccess).toBe(true);
    const type = result.blocks[0].declarations[0].surfaceType!;

    console.log('MultiBinder type:', JSON.stringify(type, null, 2));

    expect(type.tag).toBe('MultiBinder');
    if (type.tag === 'MultiBinder') {
      expect(type.named).toBe(true); // THIS IS THE BUG!
    }
  });
});
