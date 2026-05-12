import { describe, expect, test } from 'vitest';

import { compileTTFromText } from './compile';
import { compileOneBlock } from './compile-block-processing';
import { parseTTSource } from './compile-parse';
import type { ElaborateTacticBlockFn } from './compile-term-simple-value';

const noTactics: ElaborateTacticBlockFn = () => {
  throw new Error('unexpected tactic block in compileOneBlock test');
};

const natBoolPrelude = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Bool : Type where
  True : Bool
  False : Bool
`;

describe('compileOneBlock', () => {
  test('preserves comment blocks without touching definitions', () => {
    const parseResult = parseTTSource('-- only a comment\n');
    const block = parseResult.blocks[0];
    const definitions = compileTTFromText('').definitions;

    const result = compileOneBlock(
      block,
      0,
      definitions,
      new Set(),
      new Map(),
      true,
      noTactics,
      () => undefined,
    );

    expect(result.compiled.isComment).toBe(true);
    expect(result.compiled.declarations).toHaveLength(0);
    expect(result.checkErrorCount).toBe(0);
    expect(result.nameErrorCount).toBe(0);
    expect(result.newDefinitions).toBe(definitions);
  });

  test('compiles with auxiliaries before the main declaration and marks them', () => {
    const definitions = compileTTFromText(natBoolPrelude).definitions;
    const parseResult = parseTTSource(`
isZero : Nat -> Bool
isZero n with n
  | Zero => True
  | Succ _ => False
`);
    const block = parseResult.blocks[0];

    const result = compileOneBlock(
      block,
      0,
      definitions,
      new Set(['Nat', 'Zero', 'Succ', 'Bool', 'True', 'False']),
      new Map(),
      true,
      noTactics,
      () => undefined,
    );

    expect(result.compiled.nameResolutionSuccess).toBe(true);
    expect(result.compiled.declarations).toHaveLength(2);
    expect(result.compiled.declarations[0]?.isWithAuxiliary).toBe(true);
    expect(result.compiled.declarations[0]?.name).toMatch(/^isZero-with-/);
    expect(result.compiled.declarations[0]?.checkSuccess).toBe(true);
    expect(result.compiled.declarations[1]?.name).toBe('isZero');
    expect(result.compiled.declarations[1]?.checkSuccess).toBe(true);
  });

  test('surfaces duplicate-name resolution errors while still compiling declarations', () => {
    const definitions = compileTTFromText(natBoolPrelude).definitions;
    const parseResult = parseTTSource(`
dup : Nat
dup = Zero
dup : Nat
dup = Zero
`);
    const block = parseResult.blocks[0];

    const result = compileOneBlock(
      block,
      0,
      definitions,
      new Set(['Nat', 'Zero', 'Succ', 'Bool', 'True', 'False']),
      new Map(),
      true,
      noTactics,
      () => undefined,
    );

    expect(result.compiled.nameResolutionSuccess).toBe(false);
    expect(result.compiled.nameResolutionErrors.length).toBeGreaterThan(0);
    expect(result.compiled.nameResolutionErrors.some(err => err.symbolName === 'dup')).toBe(true);
    expect(result.compiled.declarations).toHaveLength(2);
    expect(result.compiled.declarations[0]?.name).toBe('dup');
    expect(result.compiled.declarations[1]?.name).toBe('dup');
  });
});
