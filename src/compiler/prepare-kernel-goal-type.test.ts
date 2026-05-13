import { describe, expect, test } from 'vitest';

import { compileTTFromText } from './compile';
import { parseTTSource } from './compile-parse';
import { elabToKernelWithMap } from './elab';
import { prettyPrintFormatted } from './kernel';
import { createNamedArgInfoLookup } from './term';
import { prepareKernelGoalType } from './prepare-kernel-goal-type';

const NAT_EQUAL_PRELUDE = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a
`;

function elaborateStandaloneType(typeSource: string) {
  const definitions = compileTTFromText(NAT_EQUAL_PRELUDE).definitions;
  const parseResult = parseTTSource(`
helper : ${typeSource}
helper = Zero
`);
  const declBlock = parseResult.blocks.find(block => block.kind === 'declarations');
  if (!declBlock || declBlock.kind !== 'declarations') {
    throw new Error('expected declaration block');
  }
  const parsedDecl = declBlock.declarations[0];
  const kernelType = elabToKernelWithMap(
    parsedDecl.type!,
    new Map(),
    [{ kind: 'field', name: 'type' }],
    [{ kind: 'field', name: 'type' }],
    undefined,
    createNamedArgInfoLookup(definitions),
  );
  return { definitions, kernelType };
}

describe('prepareKernelGoalType', () => {
  test('solves implicit holes in theorem goal types before tactics start rewriting against them', () => {
    const { definitions, kernelType } = elaborateStandaloneType('(x : Nat) -> Equal x x');

    const prepared = prepareKernelGoalType(kernelType, [], definitions);

    expect(prettyPrintFormatted(prepared)).toBe('((x : Nat) -> (Equal Nat x x))');
  });

  test('leaves already-explicit goal types stable', () => {
    const definitions = compileTTFromText(NAT_EQUAL_PRELUDE).definitions;
    const explicitType = { tag: 'Const', name: 'Nat' } as const;

    const prepared = prepareKernelGoalType(explicitType, [], definitions);

    expect(prepared).toEqual(explicitType);
  });

  test('is idempotent on dependent theorem goal types', () => {
    const { definitions, kernelType } = elaborateStandaloneType(
      '{b c : Nat} -> Equal c c -> Equal c c',
    );

    const preparedOnce = prepareKernelGoalType(kernelType, [], definitions);
    const preparedTwice = prepareKernelGoalType(preparedOnce, [], definitions);

    expect(prettyPrintFormatted(preparedTwice)).toBe(prettyPrintFormatted(preparedOnce));
  });
});
