import { describe, expect, test } from 'vitest';
import { compileTTFromText } from './compile';
import { parseTTSource } from './compile-parse';
import { prepareTermSignature } from './compile-term-signature';
import { checkSimpleTermValue, type ElaborateTacticBlockFn } from './compile-term-simple-value';
import { createNamedArgInfoLookup } from './term';
import { elabToKernelWithMap } from './elab';
import { prettyPrintFormatted } from './kernel';
import { TacticInfoTree } from '../tactics/info-tree';

function buildTermDeclaration(source: string, prelude: string) {
  const definitions = compileTTFromText(prelude).definitions;
  const parseResult = parseTTSource(source);
  const declBlock = parseResult.blocks.find(block => block.kind === 'declarations');
  expect(declBlock?.kind).toBe('declarations');
  if (!declBlock || declBlock.kind !== 'declarations') {
    throw new Error('expected declaration block');
  }
  const parsedDecl = declBlock.declarations[0];
  const elabMap = new Map();
  const typePath = [{ kind: 'field', name: 'type' }] as const;
  const kernelType = elabToKernelWithMap(
    parsedDecl.type!,
    elabMap,
    [...typePath],
    [...typePath],
    undefined,
    createNamedArgInfoLookup(definitions),
  );
  return {
    definitions,
    decl: {
      name: parsedDecl.name,
      kind: 'term' as const,
      surfaceType: parsedDecl.type,
      surfaceValue: parsedDecl.value,
      kernelType,
      elabMap,
      sourceMap: new Map(),
    },
  };
}

const NAT_PRELUDE = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat
`;

const neverElaborateTacticBlock: ElaborateTacticBlockFn = () => {
  throw new Error('unexpected tactic block elaboration');
};

describe('compile-term-simple-value', () => {
  test('checks a simple non-recursive value and stores the zonked term', () => {
    const { definitions, decl } = buildTermDeclaration(`
zeroId : Nat
zeroId = Zero
`, NAT_PRELUDE);
    const signatureResult = prepareTermSignature(decl, definitions);
    expect(signatureResult.success).toBe(true);
    if (!signatureResult.success) {
      throw new Error('expected signature preparation to succeed');
    }

    const result = checkSimpleTermValue(
      decl,
      'zeroId',
      signatureResult.prepared.termEnv,
      signatureResult.prepared.zonkedKernelType,
      signatureResult.prepared.namedArgMap,
      neverElaborateTacticBlock,
    );

    expect(result.success).toBe(true);
    if (!result.success) {
      throw new Error('expected simple value check to succeed');
    }
    expect(prettyPrintFormatted(result.checkedValue)).toBe('Zero');
  });

  test('rejects self-recursive simple definitions', () => {
    const { definitions, decl } = buildTermDeclaration(`
loop : Nat
loop = loop
`, NAT_PRELUDE);
    const signatureResult = prepareTermSignature(decl, definitions);
    expect(signatureResult.success).toBe(true);
    if (!signatureResult.success) {
      throw new Error('expected signature preparation to succeed');
    }

    const result = checkSimpleTermValue(
      decl,
      'loop',
      signatureResult.prepared.termEnv,
      signatureResult.prepared.zonkedKernelType,
      signatureResult.prepared.namedArgMap,
      neverElaborateTacticBlock,
    );

    expect(result.success).toBe(false);
    if (result.success) {
      throw new Error('expected simple recursion rejection');
    }
    expect(result.errors[0].message).toContain('simple definitions cannot be recursive');
  });

  test('uses tactic block elaboration output without re-checking through match inference', () => {
    const { definitions, decl } = buildTermDeclaration(`
proved : Nat
proved := by
  exact Zero
`, NAT_PRELUDE);
    const signatureResult = prepareTermSignature(decl, definitions);
    expect(signatureResult.success).toBe(true);
    if (!signatureResult.success) {
      throw new Error('expected signature preparation to succeed');
    }

    const result = checkSimpleTermValue(
      decl,
      'proved',
      signatureResult.prepared.termEnv,
      signatureResult.prepared.zonkedKernelType,
      signatureResult.prepared.namedArgMap,
      () => ({
        term: { tag: 'Const', name: 'Zero' },
        infoTree: new TacticInfoTree({
          position: { line: 1, col: 1, endLine: 1, endCol: 1 },
          goalsBefore: [],
          goalsAfter: [],
          tactic: { tag: 'Exact', term: { tag: 'Const', name: 'Zero' } },
          children: [],
        }),
      }),
    );

    expect(result.success).toBe(true);
    if (!result.success) {
      throw new Error('expected tactic block result to succeed');
    }
    expect(prettyPrintFormatted(result.checkedValue)).toBe('Zero');
    expect(result.tacticInfoTree).toBeInstanceOf(TacticInfoTree);
  });
});
