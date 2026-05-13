import { describe, expect, test } from 'vitest';
import { parseTTSource } from './compile-parse';
import { compileTTFromText } from './compile';
import { processTermDeclaration } from './compile-term-declaration';
import { TacticInfoTree } from '../tactics/info-tree';

function parseFirstDeclaration(source: string) {
  const parsed = parseTTSource(source);
  const declBlock = parsed.blocks.find(block => block.kind === 'declarations');
  expect(declBlock?.kind).toBe('declarations');
  if (!declBlock || declBlock.kind !== 'declarations') {
    throw new Error('expected declarations block');
  }
  return {
    declaration: declBlock.declarations[0],
    sourceMap: declBlock.sourceMaps[0],
  };
}

describe('compile-term-declaration', () => {
  test('processTermDeclaration returns a successful compiled declaration for a simple term', () => {
    const definitions = compileTTFromText(`
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat
`).definitions;
    const { declaration, sourceMap } = parseFirstDeclaration(`
idNat : Nat -> Nat
idNat = \\x => x
`);

    const result = processTermDeclaration(
      declaration,
      sourceMap,
      definitions,
      () => {
        throw new Error('tactics should not run for this definition');
      },
    );

    expect(result.success).toBe(true);
    expect(result.compiled.checkSuccess).toBe(true);
    expect(result.compiled.name).toBe('idNat');
    expect(result.newDefinitions.terms.has('idNat')).toBe(true);
  });

  test('processTermDeclaration turns signature failures into failed compiled declarations', () => {
    const { declaration, sourceMap } = parseFirstDeclaration(`
x : Nat
`);

    const result = processTermDeclaration(
      declaration,
      sourceMap,
      compileTTFromText('').definitions,
      () => {
        throw new Error('tactics should not run for bad signatures');
      },
    );

    expect(result.success).toBe(false);
    expect(result.compiled.checkSuccess).toBe(false);
    expect(result.compiled.checkErrors[0].message).toContain('Type definition not found: Nat');
  });

  test('processTermDeclaration rejects tactic elaboration output that fails kernel checking', () => {
    const definitions = compileTTFromText(`
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat
`).definitions;
    const { declaration, sourceMap } = parseFirstDeclaration(`
badBy : Nat
badBy := by
  exact Zero
`);

    const result = processTermDeclaration(
      declaration,
      sourceMap,
      definitions,
      () => ({
        term: {
          tag: 'Binder',
          name: 'x',
          binderKind: { tag: 'BLam' },
          domain: { tag: 'Const', name: 'Nat' },
          body: { tag: 'Var', index: 0 },
        },
        infoTree: new TacticInfoTree({
          position: { line: 1, col: 1, endLine: 1, endCol: 1 },
          goalsBefore: [],
          goalsAfter: [],
          tactic: { tag: 'Exact', term: { tag: 'Const', name: 'Zero' } },
          children: [],
        }),
      }),
    );

    expect(result.success).toBe(false);
    expect(result.compiled.checkSuccess).toBe(false);
    expect(result.compiled.checkErrors[0]?.fullMessage).toContain('Nat');
  });
});
