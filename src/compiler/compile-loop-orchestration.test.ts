import { describe, expect, test } from 'vitest';

import {
  collectChangedBlockIndices,
  compileParsedBlocksIncrementally,
  reuseLastIncrementalResult,
  type CompileLoopServices,
} from './compile-loop-orchestration';
import { createIncrementalCache } from './incremental';
import { parseTTSource } from './compile-parse';
import type { ElaborateTacticBlockFn } from './compile-term-simple-value';

const noTactics: ElaborateTacticBlockFn = () => {
  throw new Error('unexpected tactic block in compile loop orchestration test');
};

const noRecheck = () => undefined;

const defaultServices: CompileLoopServices = {
  assumeK: true,
  elaborateTacticBlock: noTactics,
  recheckZonkedTerm: noRecheck,
};

describe('compile loop orchestration', () => {
  test('reuseLastIncrementalResult skips recompilation when grouped block contents are unchanged', () => {
    const cache = createIncrementalCache();
    const source = `
@syntax @impl=nat
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

one : Nat
one = 1
`;

    const firstResult = compileParsedBlocksIncrementally(
      parseTTSource(source),
      cache,
      defaultServices,
    );

    expect(reuseLastIncrementalResult(source, cache)).toBe(firstResult);
  });

  test('changed-block detection only marks edited blocks before dependency expansion', () => {
    const cache = createIncrementalCache();
    const initialSource = `
foo : Type
foo = Type

bar : Type
bar = foo
`;
    compileParsedBlocksIncrementally(
      parseTTSource(initialSource),
      cache,
      defaultServices,
    );

    const updatedSource = `
foo : Type
foo = Type

bar : Type
bar = foo

baz : Type
baz = foo
`;
    const changed = collectChangedBlockIndices(parseTTSource(updatedSource), cache);

    expect([...changed]).toEqual([2]);
  });

  test('incremental replay restores cached @impl=nat registrations before compiling changed later blocks', () => {
    const cache = createIncrementalCache();
    const initialSource = `
@syntax @impl=nat
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

one : Nat
one = 1
`;
    const initialResult = compileParsedBlocksIncrementally(
      parseTTSource(initialSource),
      cache,
      defaultServices,
    );

    expect(initialResult.success).toBe(true);

    const updatedSource = `
@syntax @impl=nat
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

two : Nat
two = 2
`;
    const updatedResult = compileParsedBlocksIncrementally(
      parseTTSource(updatedSource),
      cache,
      defaultServices,
    );

    expect(updatedResult.success).toBe(true);
    expect(updatedResult.totalCheckErrors).toBe(0);
  });

  test('incremental recompilation eagerly registers @impl annotations from changed earlier blocks before dependents', () => {
    const cache = createIncrementalCache();
    const initialSource = `
@syntax @impl=nat
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

one : Nat
one = 1
`;
    const initialResult = compileParsedBlocksIncrementally(
      parseTTSource(initialSource),
      cache,
      defaultServices,
    );

    expect(initialResult.success).toBe(true);

    const rebuiltNatSource = `
@syntax @impl=nat
-- force the defining block itself to recompile
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

one : Nat
one = 1
`;
    const rebuiltResult = compileParsedBlocksIncrementally(
      parseTTSource(rebuiltNatSource),
      cache,
      defaultServices,
    );

    expect(rebuiltResult.success).toBe(true);
    expect(rebuiltResult.totalCheckErrors).toBe(0);
  });
});
