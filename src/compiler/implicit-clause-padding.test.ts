import { describe, expect, test } from 'vitest';

import { compileTTFromText } from './compile';

describe('omitted implicit clause binders remain in RHS scope', () => {
  test('RHS can reference omitted top-level implicit parameters by their binder names', () => {
    const source = `
inductive Either : Type -> Type -> Type where
  Left : {A B : Type} -> A -> Either A B
  Right : {A B : Type} -> B -> Either A B

foo : {A B : Type} -> Either A B -> Type
foo x = Either A B
`;

    const result = compileTTFromText(source);
    expect(result.success).toBe(true);
    expect(result.totalCheckErrors).toBe(0);
  });

  test('dependent eliminators can reference omitted implicit parameters from branch motives', () => {
    const source = `
inductive Either : Type -> Type -> Type where
  Left : {A B : Type} -> A -> Either A B
  Right : {A B : Type} -> B -> Either A B

eitherElimDep : {A B : Type} -> (C : Either A B -> Type) -> ((a : A) -> C (Left a)) -> ((b : B) -> C (Right b)) -> (e : Either A B) -> C e
eitherElimDep C f g (Left a) = f a
eitherElimDep C f g (Right b) = g b

rebuild : {A B : Type} -> Either A B -> Either A B
rebuild e = eitherElimDep (\\x => Either A B) (\\a => Left a) (\\b => Right b) e
`;

    const result = compileTTFromText(source);
    expect(result.success).toBe(true);
    expect(result.totalCheckErrors).toBe(0);
  });
});
