import { describe, expect, test } from 'vitest';

import { compileTTFromText } from './compile';
import { applyImplAnnotationsForBlock } from './compile-impl-annotations';
import type { CompiledBlock } from './compile-types';

const natOpsSource = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ n) m = Succ (plus n m)
`;

describe('applyImplAnnotationsForBlock', () => {
  test('registers nat implementations from syntax-tagged declarations', () => {
    const definitions = compileTTFromText(natOpsSource).definitions;
    const block: CompiledBlock = {
      blockIndex: 0,
      sourceLines: [],
      startLine: 1,
      codeStartLine: 1,
      parseSuccess: true,
      parseErrors: [],
      nameResolutionSuccess: true,
      nameResolutionErrors: [],
      declarations: [
        {
          name: 'Nat',
          kind: 'inductive',
          checkSuccess: true,
          checkErrors: [],
          syntax: '@impl=nat',
        } as any,
      ],
      isComment: false,
    };

    applyImplAnnotationsForBlock(block, definitions);

    expect(definitions.natImplByCtor?.get('Zero')?.inductiveName).toBe('Nat');
    expect(definitions.natImplByCtor?.get('Succ')?.inductiveName).toBe('Nat');
  });

  test('registers nat primitive operations once nat impls are available', () => {
    const definitions = compileTTFromText(natOpsSource).definitions;
    applyImplAnnotationsForBlock(
      {
        blockIndex: 0,
        sourceLines: [],
        startLine: 1,
        codeStartLine: 1,
        parseSuccess: true,
        parseErrors: [],
        nameResolutionSuccess: true,
        nameResolutionErrors: [],
        declarations: [
          { name: 'Nat', kind: 'inductive', checkSuccess: true, checkErrors: [], syntax: '@impl=nat' } as any,
        ],
        isComment: false,
      },
      definitions,
    );

    applyImplAnnotationsForBlock(
      {
        blockIndex: 1,
        sourceLines: [],
        startLine: 1,
        codeStartLine: 1,
        parseSuccess: true,
        parseErrors: [],
        nameResolutionSuccess: true,
        nameResolutionErrors: [],
        declarations: [
          { name: 'plus', kind: 'term', checkSuccess: true, checkErrors: [], syntax: '@natAdd' } as any,
        ],
        isComment: false,
      },
      definitions,
    );

    expect(definitions.natOpByFn?.get('plus')).toBe('add');
  });
});
