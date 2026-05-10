import { describe, expect, test } from 'vitest';
import { parseTTSource } from './compile-parse';
import { createCompiledDeclaration, createElabErrorResult } from './compile-declaration-result';
import { NamedArgElabError } from './elab';
import { mkConst } from './kernel';
import { createDefinitionsMap } from './term';
import { serializeIndexPath } from '../types/source-position';

function getFirstDeclaration(source: string): any {
  const parseResult = parseTTSource(source);
  const declBlock = parseResult.blocks.find(block => block.kind === 'declarations');
  if (!declBlock || declBlock.kind !== 'declarations') {
    throw new Error('Expected declarations block');
  }
  return declBlock.declarations[0];
}

describe('compile-declaration-result', () => {
  test('createCompiledDeclaration preserves named arg metadata from the surface type', () => {
    const decl = getFirstDeclaration(`
inductive Wrap : {A : Type} -> Type where
  MkWrap : {A : Type} -> Wrap {A := A}
`);

    const compiled = createCompiledDeclaration(
      decl,
      mkConst('Wrap'),
      undefined,
      [{ name: 'MkWrap', type: mkConst('Wrap') }],
      new Map(),
      new Map(),
      true,
      [],
      createDefinitionsMap()
    );

    expect(compiled.namedArgMap).toEqual(new Map([['A', 0]]));
    expect(compiled.prettyConstructors).toEqual([{ name: 'MkWrap', prettyType: 'Wrap' }]);
  });

  test('createElabErrorResult maps named-arg elaboration errors back to the surface path', () => {
    const decl = getFirstDeclaration(`
inductive Wrap : {A : Type} -> Type where
  MkWrap : {A : Type} -> Wrap {A := A}
`);
    const surfacePath = [{ kind: 'field', name: 'type' }] as const;
    const result = createElabErrorResult(
      new NamedArgElabError('unknown named argument', [...surfacePath]),
      decl,
      new Map(),
      new Map(),
      createDefinitionsMap()
    );

    expect(result.success).toBe(false);
    expect(result.errorCount).toBe(1);
    expect(result.compiled.elabErrorPath).toBe(serializeIndexPath([...surfacePath]));
    expect(result.compiled.checkErrors[0]?.message).toContain('unknown named argument');
  });
});
