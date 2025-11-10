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
    // Lambda should be: λx. a + x
    expect(prettyPrint(result.lambda)).toContain('λx');
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

