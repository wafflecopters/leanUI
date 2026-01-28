import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Record named arguments', () => {
  test('named argument for record type parameter', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record DPair {u v : ULevel} (A : Type u) (B : A -> Type v) : Type (UMax u v) where
  constructor MkDPair
  dfst: A
  dsnd: B dfst

-- Use named arguments to specify universe levels
SimplePair : Type
SimplePair = DPair {u:=UZero} {v:=UZero} Nat (\\_ => Nat)
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const dpairDecl = allDecls.find((d: any) => d?.name === 'DPair');
    expect(dpairDecl?.checkSuccess).toBe(true);

    const simplePairDecl = allDecls.find((d: any) => d?.name === 'SimplePair');
    expect(simplePairDecl?.checkSuccess).toBe(true);
  });

  test('named argument with USucc', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Box {u : ULevel} (A : Type u) : Type (USucc u) where
  unbox : A

-- Use named argument with USucc
TypeBox : Type 1
TypeBox = Box {u:=UZero} Nat
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const boxDecl = allDecls.find((d: any) => d?.name === 'Box');
    expect(boxDecl?.checkSuccess).toBe(true);

    const typeBoxDecl = allDecls.find((d: any) => d?.name === 'TypeBox');
    expect(typeBoxDecl?.checkSuccess).toBe(true);
  });
});
