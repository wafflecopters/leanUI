import { describe, expect, test } from 'vitest';
import { parseTTSource } from './compile-parse';

describe('parseTTSource', () => {
  test('preserves comment blocks with correct offsets', () => {
    const source = `-- hello
-- world

x : Type`;

    const result = parseTTSource(source);
    expect(result.blocks[0]).toMatchObject({
      kind: 'comment',
      startLine: 1,
      posOffset: 0,
    });
    expect(result.blocks[1]).toMatchObject({
      kind: 'declarations',
      startLine: 4,
      posOffset: 19,
    });
  });

  test('propagates notation declarations to later blocks', () => {
    const source = `infixl 65 + := radd

test : Type
test = a + b`;

    const result = parseTTSource(source);
    expect(result.totalErrors).toBe(0);
    const declBlock = result.blocks[1];
    expect(declBlock.kind).toBe('declarations');
    if (declBlock.kind !== 'declarations') throw new Error('expected declarations block');
    const testDecl = declBlock.declarations.find(decl => decl.name === 'test');
    expect(testDecl?.value?.tag).toBe('App');
  });

  test('adjusts parse error lines to absolute source positions', () => {
    const source = `inductive Nat : Type where
  Zero : Nat

broken : Type
broken = (`;

    const result = parseTTSource(source);
    expect(result.totalErrors).toBe(1);
    const errorBlock = result.blocks.find(block => block.kind === 'error');
    expect(errorBlock).toBeDefined();
    if (!errorBlock || errorBlock.kind !== 'error') throw new Error('expected parse error block');
    expect(errorBlock.errors[0]?.line).toBe(5);
  });
});
