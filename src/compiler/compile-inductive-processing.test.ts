import { describe, expect, test } from 'vitest';
import { parseTTSource } from './compile-parse';
import { compileTTFromText } from './compile';
import { createCtorAppNamedArgLookup } from './compile-inductive-processing';
import { addInductiveDefinition, createDefinitionsMap } from './term';
import { mkPi, mkSort, mkULit } from './kernel';

function getFirstDeclaration(source: string): any {
  const parseResult = parseTTSource(source);
  const declBlock = parseResult.blocks.find(block => block.kind === 'declarations');
  if (!declBlock || declBlock.kind !== 'declarations') {
    throw new Error('Expected declarations block');
  }
  return declBlock.declarations[0];
}

describe('compile-inductive-processing', () => {
  test('current inductive named args are available during constructor elaboration', () => {
    const decl = getFirstDeclaration(`
inductive Wrap : {A : Type} -> Type where
  MkWrap : Wrap {A := A}
`);
    const lookup = createCtorAppNamedArgLookup(decl, createDefinitionsMap());

    expect(lookup('Wrap')).toEqual({
      namedArgMap: new Map([['A', 0]]),
      totalArity: 1,
      argNamedArgInfos: undefined,
    });
  });

  test('constructor elaboration still falls back to existing named-arg definitions', () => {
    let definitions = createDefinitionsMap();
    const Type0 = mkSort(mkULit(0));
    definitions = addInductiveDefinition(
      definitions,
      'Equal',
      mkPi(Type0, mkPi(Type0, mkPi(Type0, Type0, 'rhs'), 'lhs'), 'A'),
      [{ name: 'refl', type: mkPi(Type0, mkPi(Type0, { tag: 'Const', name: 'Equal' }, 'a'), 'A') }],
      [],
      new Map([['A', 0]]),
    );

    const decl = getFirstDeclaration(`
inductive Wrap : {A : Type} -> Type where
  MkWrap : Wrap {A := A}
`);
    const lookup = createCtorAppNamedArgLookup(decl, definitions);
    const equalInfo = lookup('Equal');

    expect(equalInfo?.namedArgMap).toEqual(new Map([['A', 0]]));
    expect(equalInfo?.totalArity).toBe(3);
  });

  test('constructors can use current inductive named args in return type', () => {
    const result = compileTTFromText(`
inductive Wrap : {A : Type} -> Type where
  MkWrap : {A : Type} -> Wrap {A := A}
`);
    const allDecls = result.blocks.flatMap(block => (block as any).declarations ?? []);
    const wrapDecl = allDecls.find((decl: any) => decl?.name === 'Wrap');

    expect(wrapDecl).toBeTruthy();
    expect(wrapDecl?.checkSuccess).toBe(true);
    expect(wrapDecl?.checkErrors ?? []).toHaveLength(0);
  });

  test('constructors can use current inductive named args out of order', () => {
    const result = compileTTFromText(`
inductive PairBox : {A : Type} -> {B : Type} -> Type where
  MkPairBox : {A : Type} -> {B : Type} -> PairBox {B := B} {A := A}
`);
    const allDecls = result.blocks.flatMap(block => (block as any).declarations ?? []);
    const pairBoxDecl = allDecls.find((decl: any) => decl?.name === 'PairBox');

    expect(pairBoxDecl).toBeTruthy();
    expect(pairBoxDecl?.checkSuccess).toBe(true);
    expect(pairBoxDecl?.checkErrors ?? []).toHaveLength(0);
  });
});
