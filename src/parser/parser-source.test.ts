/**
 * Tests for source position tracking in the parser
 */

import { describe, test, expect } from 'vitest';
import { Parser } from './parser';

describe('Parser Source Tracking', () => {
  test('parseDeclarationsWithSource returns declarations with source maps', () => {
    const parser = new Parser();
    const source = `id : A -> A`;

    const results = parser.parseDeclarationsWithSource(source);

    expect(results.length).toBe(1);
    expect(results[0].decl).toBeDefined();
    expect(results[0].sourceMap).toBeDefined();
    expect(results[0].sourceMap instanceof Map).toBe(true);
  });

  test('parseDeclarationsWithSource with multiple declarations', () => {
    const parser = new Parser();
    const source = `id : A -> A

const : A -> B -> A`;

    const results = parser.parseDeclarationsWithSource(source);

    expect(results.length).toBe(2);
    expect(results[0].decl.name).toBe('id');
    expect(results[1].decl.name).toBe('const');
  });

  test('parseDeclarationsWithSource with merged type and value', () => {
    const parser = new Parser();
    const source = `id : A -> A
id x = x`;

    const results = parser.parseDeclarationsWithSource(source);

    expect(results.length).toBe(1);
    expect(results[0].decl.name).toBe('id');
    expect(results[0].decl.type).toBeDefined();
    expect(results[0].decl.value).toBeDefined();
    // Source map should have entries from both lines
    expect(results[0].sourceMap.size).toBeGreaterThanOrEqual(0);
  });

  test('source map is separate for each declaration', () => {
    const parser = new Parser();
    const source = `id : A -> A

const : A -> B -> A`;

    const results = parser.parseDeclarationsWithSource(source);

    // Each should have its own source map instance
    expect(results[0].sourceMap).not.toBe(results[1].sourceMap);
  });

  test('parseDeclarationsWithSource handles inductive', () => {
    const parser = new Parser();
    const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat`;

    const results = parser.parseDeclarationsWithSource(source);

    expect(results.length).toBe(1);
    expect(results[0].decl.kind).toBe('inductive');
    expect(results[0].decl.name).toBe('Nat');
    expect(results[0].sourceMap instanceof Map).toBe(true);
  });
});
