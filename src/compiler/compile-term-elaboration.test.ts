import { describe, expect, test } from 'vitest';
import { parseTTSource } from './compile-parse';
import { elaborateTermDeclaration } from './compile-term-elaboration';
import { compileTTFromText } from './compile';
import { prettyPrintFormatted } from './kernel';

describe('compile-term-elaboration', () => {
  test('elaborates a term declaration signature against existing definitions', () => {
    const definitions = compileTTFromText(`
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a
`).definitions;
    const parseResult = parseTTSource(`
foo : Equal Zero Zero
foo = refl
`);
    const declBlock = parseResult.blocks.find(block => block.kind === 'declarations');
    expect(declBlock?.kind).toBe('declarations');
    if (!declBlock || declBlock.kind !== 'declarations') {
      throw new Error('expected declaration block');
    }

    const result = elaborateTermDeclaration(
      declBlock.declarations[0],
      new Map(),
      definitions,
    );

    expect(result.elabDecl.kind).toBe('term');
    expect(result.kernelType).toBeDefined();
    expect(prettyPrintFormatted(result.kernelType!)).toContain('Equal');
  });

  test('preserves with-clause metadata on the elaborated declaration shell', () => {
    const definitions = compileTTFromText(`
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat
`).definitions;
    const parseResult = parseTTSource(`
helper : Nat -> Nat
helper n = n
`);
    const declBlock = parseResult.blocks.find(block => block.kind === 'declarations');
    expect(declBlock?.kind).toBe('declarations');
    if (!declBlock || declBlock.kind !== 'declarations') {
      throw new Error('expected declaration block');
    }

    const parsedDecl = {
      ...declBlock.declarations[0],
      withScrutineeCount: 2,
      newScrutineeCount: 1,
      withScrutineeExprs: [{ tag: 'Const', name: 'Zero' }] as any,
    };
    const result = elaborateTermDeclaration(parsedDecl, new Map(), definitions);

    expect(result.elabDecl.withScrutineeCount).toBe(2);
    expect(result.elabDecl.newScrutineeCount).toBe(1);
    expect(result.elabDecl.withScrutineeExprs).toHaveLength(1);
  });
});
