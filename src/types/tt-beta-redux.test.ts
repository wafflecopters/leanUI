/**
 * Tests for beta-redux extraction functionality
 */

import { describe, it, expect } from 'bun:test';
import {
  TTerm,
  asLambdaByExtractingTermAtIndexPaths,
  prettyPrint,
  getSubtermAtPath,
  mkConst,
  mkApp,
  mkProp
} from './tt-core';
import { expressionPathToTTermPath, expressionNodeToTTerm } from './tt-bridge';
import { parseExpressionToAST } from './enhanced-focus';

describe('asLambdaByExtractingTermAtIndexPaths', () => {
  it('should extract a simple variable from a binary operation', () => {
    // Build: a + b  (which is App(App(+, a), b))
    const aVar: TTerm = { tag: 'Const', name: 'a', type: mkProp() };
    const bVar: TTerm = { tag: 'Const', name: 'b', type: mkProp() };
    const plusConst = mkConst('+', mkProp());

    const term = mkApp(mkApp(plusConst, aVar), bVar);

    console.log('Term structure:', JSON.stringify(term, null, 2));
    console.log('Pretty print:', prettyPrint(term));

    // Path to 'b' (the right argument): [1]
    const result = asLambdaByExtractingTermAtIndexPaths(term, [[1]]);

    if ('error' in result) {
      throw new Error(`Extraction failed: ${result.error}`);
    }

    console.log('Lambda:', prettyPrint(result.lambda));
    console.log('Extracted:', prettyPrint(result.extracted));

    expect('lambda' in result).toBe(true);
    expect(prettyPrint(result.extracted)).toBe('b');
    // Lambda should be: (λ (x : ?extracted-type), ((+ a) x))
    expect(prettyPrint(result.lambda)).toContain('(+ a) x');
  });

  it('should extract the left operand from a + a', () => {
    // Build: a + a  (which is App(App(+, a), a))
    const aVar: TTerm = { tag: 'Const', name: 'a', type: mkProp() };
    const plusConst = mkConst('+', mkProp());

    const term = mkApp(mkApp(plusConst, aVar), aVar);

    console.log('\n=== Testing a + a ===');
    console.log('Term structure:', JSON.stringify(term, null, 2));
    console.log('Pretty print:', prettyPrint(term));

    // Explore the structure
    console.log('Subterm at []: ', prettyPrint(getSubtermAtPath(term, [])!));
    console.log('Subterm at [0]:', prettyPrint(getSubtermAtPath(term, [0])!));
    console.log('Subterm at [1]:', prettyPrint(getSubtermAtPath(term, [1])!));
    console.log('Subterm at [0, 0]:', prettyPrint(getSubtermAtPath(term, [0, 0])!));
    console.log('Subterm at [0, 1]:', prettyPrint(getSubtermAtPath(term, [0, 1])!));

    // Path to left 'a': [0, 1]
    const result = asLambdaByExtractingTermAtIndexPaths(term, [[0, 1]]);

    if ('error' in result) {
      throw new Error(`Extraction failed: ${result.error}`);
    }

    console.log('Lambda:', prettyPrint(result.lambda));
    console.log('Extracted:', prettyPrint(result.extracted));

    expect('lambda' in result).toBe(true);
    expect(prettyPrint(result.extracted)).toBe('a');
    // Lambda should be: λx. x + a
  });

  it('should extract the right operand from a + a', () => {
    // Build: a + a  (which is App(App(+, a), a))
    const aVar: TTerm = { tag: 'Const', name: 'a', type: mkProp() };
    const plusConst = mkConst('+', mkProp());

    const term = mkApp(mkApp(plusConst, aVar), aVar);

    console.log('\n=== Testing a + a (right a) ===');

    // Path to right 'a': [1]
    const result = asLambdaByExtractingTermAtIndexPaths(term, [[1]]);

    if ('error' in result) {
      throw new Error(`Extraction failed: ${result.error}`);
    }

    console.log('Lambda:', prettyPrint(result.lambda));
    console.log('Extracted:', prettyPrint(result.extracted));

    expect('lambda' in result).toBe(true);
    expect(prettyPrint(result.extracted)).toBe('a');
    // Lambda should be: λx. a + x
  });
});

describe('expressionPathToTTermPath', () => {
  it('should convert path for left operand in a + b', () => {
    const expr = parseExpressionToAST('a + b');

    // ExpressionNode path [0] (left child) should map to TTerm path [0, 1]
    const ttermPath = expressionPathToTTermPath(expr, [0]);

    expect(ttermPath).toEqual([0, 1]);
  });

  it('should convert path for right operand in a + b', () => {
    const expr = parseExpressionToAST('a + b');

    // ExpressionNode path [1] (right child) should map to TTerm path [1]
    const ttermPath = expressionPathToTTermPath(expr, [1]);

    expect(ttermPath).toEqual([1]);
  });

  it('should convert path for left operand in a + a', () => {
    const expr = parseExpressionToAST('a + a');

    // ExpressionNode path [0] (left child) should map to TTerm path [0, 1]
    const ttermPath = expressionPathToTTermPath(expr, [0]);

    expect(ttermPath).toEqual([0, 1]);
  });
});

describe('End-to-end: ExpressionNode to TTerm with path conversion', () => {
  it('should extract left a from a + a using converted path', () => {
    const expr = parseExpressionToAST('a + a');
    const ttermExpr = expressionNodeToTTerm(expr);

    console.log('\n=== End-to-end test: a + a, focusing on left a ===');
    console.log('ExpressionNode:', JSON.stringify(expr, null, 2));
    console.log('TTerm:', prettyPrint(ttermExpr));

    // Convert ExpressionNode path [0] to TTerm path
    const ttermPath = expressionPathToTTermPath(expr, [0]);
    console.log('ExpressionNode path [0] converts to TTerm path:', ttermPath);

    // Extract using converted path
    const result = asLambdaByExtractingTermAtIndexPaths(ttermExpr, [ttermPath]);

    if ('error' in result) {
      throw new Error(`Extraction failed: ${result.error}`);
    }

    console.log('Lambda:', prettyPrint(result.lambda));
    console.log('Extracted:', prettyPrint(result.extracted));

    expect('lambda' in result).toBe(true);
    expect(prettyPrint(result.extracted)).toBe('a');
    // Should be: (λ (x : ?extracted-type), ((+ x) a))
    expect(prettyPrint(result.lambda)).toContain('(+ x) a');
  });

  it('should extract right a from a + a using converted path', () => {
    const expr = parseExpressionToAST('a + a');
    const ttermExpr = expressionNodeToTTerm(expr);

    console.log('\n=== End-to-end test: a + a, focusing on right a ===');

    // Convert ExpressionNode path [1] to TTerm path
    const ttermPath = expressionPathToTTermPath(expr, [1]);
    console.log('ExpressionNode path [1] converts to TTerm path:', ttermPath);

    // Extract using converted path
    const result = asLambdaByExtractingTermAtIndexPaths(ttermExpr, [ttermPath]);

    if ('error' in result) {
      throw new Error(`Extraction failed: ${result.error}`);
    }

    console.log('Lambda:', prettyPrint(result.lambda));
    console.log('Extracted:', prettyPrint(result.extracted));

    expect('lambda' in result).toBe(true);
    expect(prettyPrint(result.extracted)).toBe('a');
    // Should be: (λ (x : ?extracted-type), ((+ a) x))
    expect(prettyPrint(result.lambda)).toContain('(+ a) x');
  });
});

