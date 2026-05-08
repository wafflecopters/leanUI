import { describe, expect, test } from 'vitest';
import { mkConstTT, mkPiTT } from '../compiler/surface';
import { getFocusedExpressionType } from './focused-expression-type';
import type { ExpressionNode } from '../types/enhanced-focus';

function mkVariable(name: string): ExpressionNode {
  return {
    id: name,
    type: 'variable',
    value: name,
    children: [],
    raw: name
  };
}

describe('getFocusedExpressionType', () => {
  test('infers the focused subterm type with the real checker pipeline', () => {
    const expr: ExpressionNode = {
      id: 'root',
      type: 'application',
      raw: 'f n',
      children: [mkVariable('f'), mkVariable('n')]
    };

    const result = getFocusedExpressionType(
      expr,
      [1],
      [
        { name: 'f', type: mkPiTT(mkConstTT('Nat'), mkConstTT('Nat'), '_') },
        { name: 'n', type: mkConstTT('Nat') }
      ]
    );

    expect('type' in result).toBe(true);
    if (!('type' in result)) return;
    expect(result.type).toContain('Nat');
  });

  test('reports invalid focus paths', () => {
    const expr: ExpressionNode = {
      id: 'root',
      type: 'application',
      raw: 'f n',
      children: [mkVariable('f'), mkVariable('n')]
    };

    expect(getFocusedExpressionType(expr, [2], [])).toEqual({ error: 'Invalid focus path' });
  });
});
