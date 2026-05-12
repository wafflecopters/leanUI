import { describe, expect, test } from 'vitest';
import { parseTTSource } from './compile-parse';
import { elaborateTermDeclaration } from './compile-term-elaboration';
import { checkTermDeclaration } from './compile-term-processing';
import { compileTTFromText } from './compile';

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

describe('compile-term-processing', () => {
  test('checkTermDeclaration succeeds for postulates and seeds the declaration in definitions', () => {
    const { declaration, sourceMap } = parseFirstDeclaration(`
postulate mystery : Type
`);

    const elaborated = elaborateTermDeclaration(declaration, sourceMap, compileTTFromText('').definitions);
    const result = checkTermDeclaration(elaborated.elabDecl, compileTTFromText('').definitions, () => {
      throw new Error('tactics should not run for postulates');
    });

    expect(result.success).toBe(true);
    if (!result.success) {
      throw new Error('expected postulate check to succeed');
    }
    expect(result.checkedValue).toEqual({ tag: 'Hole', id: '_postulate' });
    expect(result.definitions.terms.has('mystery')).toBe(true);
  });

  test('checkTermDeclaration checks a simple non-match definition end-to-end', () => {
    const definitions = compileTTFromText(`
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat
`).definitions;
    const { declaration, sourceMap } = parseFirstDeclaration(`
idNat : Nat -> Nat
idNat = \\x => x
`);

    const elaborated = elaborateTermDeclaration(declaration, sourceMap, definitions);
    const result = checkTermDeclaration(elaborated.elabDecl, definitions, () => {
      throw new Error('tactics should not run for simple term definitions');
    });

    expect(result.success).toBe(true);
    if (!result.success) {
      throw new Error(`expected simple definition to succeed: ${result.errors[0]?.message}`);
    }
    expect(result.definitions.terms.has('idNat')).toBe(true);
  });

  test('checkTermDeclaration returns regular declaration errors instead of throwing raw signature failures', () => {
    const { declaration, sourceMap } = parseFirstDeclaration(`
x : Nat
`);

    const elaborated = elaborateTermDeclaration(declaration, sourceMap, compileTTFromText('').definitions);
    const result = checkTermDeclaration(elaborated.elabDecl, compileTTFromText('').definitions, () => {
      throw new Error('tactics should not run for failed signatures');
    });

    expect(result.success).toBe(false);
    if (result.success) {
      throw new Error('expected missing type definition to fail');
    }
    expect(result.errors[0].message).toContain('Type definition not found: Nat');
  });
});
