import { describe, test, expect } from 'vitest';
import { compileTTFromText, compileBlocksTT } from './compile';
import { prettyPrint as prettyPrintTTK, prettyPrintPattern } from './kernel';

describe('Record pattern matching', () => {
  test('pattern match on simple record', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Point : Type where
  x : Nat
  y : Nat

getX : Point -> Nat
getX (MkPoint a b) = a
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const pointDecl = allDecls.find((d: any) => d?.name === 'Point');
    expect(pointDecl?.checkSuccess).toBe(true);

    // Debug: print the definitions to see what was registered
    const finalDefs = result.definitions;
    console.log('Definitions.terms keys:', Array.from(finalDefs.terms.keys()));
    console.log('Definitions.inductiveTypes keys:', Array.from(finalDefs.inductiveTypes.keys()));
    console.log('Definitions.inductiveNameOfConstructor entries:', Array.from(finalDefs.inductiveNameOfConstructor.entries()));

    const getXDecl = allDecls.find((d: any) => d?.name === 'getX');
    console.log('getX checkErrors:', getXDecl?.checkErrors?.map((e: any) => e?.message));
    expect(getXDecl?.checkSuccess).toBe(true);
  });

  test('pattern match on parameterized record', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Box {u : ULevel} (A : Type u) : Type (USucc u) where
  unbox : A

-- Pattern match on parameterized record
unboxNat : Box {u:=UZero} Nat -> Nat
unboxNat (MkBox x) = x
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const boxDecl = allDecls.find((d: any) => d?.name === 'Box');
    expect(boxDecl?.checkSuccess).toBe(true);

    const unboxNatDecl = allDecls.find((d: any) => d?.name === 'unboxNat');
    console.log('unboxNat checkErrors:', unboxNatDecl?.checkErrors?.map((e: any) => e?.message));
    console.log('unboxNat kernelType:', unboxNatDecl?.kernelType ? prettyPrintTTK(unboxNatDecl.kernelType) : 'undefined');
    // Debug: print the kernel clauses
    if (unboxNatDecl?.kernelClauses) {
      for (const clause of unboxNatDecl.kernelClauses) {
        console.log('Clause patterns:', clause.patterns.map((p: any) => prettyPrintPattern(p)));
        console.log('Clause rhs:', prettyPrintTTK(clause.rhs));
      }
    } else {
      console.log('No kernelClauses');
    }
    expect(unboxNatDecl?.checkSuccess).toBe(true);
  });

  test('pattern match on record with implicit type parameter', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Pair {u v : ULevel} (A : Type u) (B : Type v) : Type (UMax u v) where
  fst : A
  snd : B

-- Pattern match without specifying implicit args
swapPair : {A : Type} -> {B : Type} -> Pair A B -> Pair B A
swapPair (MkPair a b) = MkPair b a
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const pairDecl = allDecls.find((d: any) => d?.name === 'Pair');
    expect(pairDecl?.checkSuccess).toBe(true);

    // Debug: check both the TYPE's and constructor's namedArgMap
    const pairInductive = result.definitions.inductiveTypes.get('Pair');
    console.log('Pair TYPE namedArgMap:', pairInductive?.namedArgMap ? Array.from(pairInductive.namedArgMap.entries()) : undefined);
    const mkPairCtor = pairInductive?.constructors.find(c => c.name === 'MkPair');
    console.log('MkPair CTOR namedArgMap:', mkPairCtor?.namedArgMap ? Array.from(mkPairCtor.namedArgMap.entries()) : undefined);

    const swapPairDecl = allDecls.find((d: any) => d?.name === 'swapPair');
    console.log('swapPair checkErrors:', swapPairDecl?.checkErrors?.map((e: any) => e?.message));
    // Debug: print full error with cause chain
    if (swapPairDecl?.checkErrors?.length > 0) {
      const fullError = swapPairDecl.checkErrors[0];
      console.log('Full error:', JSON.stringify(fullError, (key, val) => {
        if (key === 'cause' && val) return { message: val.message, cause: val.cause };
        if (typeof val === 'function') return undefined;
        return val;
      }, 2));
    }
    // Debug: print kernel clauses
    if (swapPairDecl?.kernelClauses) {
      for (const clause of swapPairDecl.kernelClauses) {
        console.log('swapPair clause patterns:', clause.patterns.map((p: any) => prettyPrintPattern(p)));
        console.log('swapPair clause rhs:', prettyPrintTTK(clause.rhs));
      }
    }
    expect(swapPairDecl?.checkSuccess).toBe(true);
  });
});
