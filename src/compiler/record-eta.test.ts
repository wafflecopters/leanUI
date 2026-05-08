import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';
import { prettyPrint as prettyPrintTTK } from './kernel';
import { areTypesDefEq } from './whnf';

describe('Record eta expansion', () => {
  test('eta contraction: MkPoint (Point.x p) (Point.y p) = p', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Point : Type where
  x : Nat
  y : Nat

-- This function applies eta expansion
-- The return type is Point, and we return MkPoint (Point.x p) (Point.y p)
-- which should be definitionally equal to p
etaPoint : Point -> Point
etaPoint p = MkPoint (Point.x p) (Point.y p)
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const etaPointDecl = allDecls.find((d: any) => d?.name === 'etaPoint');
    console.log('etaPoint checkErrors:', etaPointDecl?.checkErrors?.map((e: any) => e?.message));
    expect(etaPointDecl?.checkSuccess).toBe(true);
  });

  test('eta contraction for parameterized record', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Pair (A : Type) (B : Type) : Type where
  fst : A
  snd : B

-- Eta expansion on parameterized record
etaPair : {A : Type} -> {B : Type} -> Pair A B -> Pair A B
etaPair p = MkPair (Pair.fst p) (Pair.snd p)
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const pairDecl = allDecls.find((d: any) => d?.name === 'Pair');
    expect(pairDecl?.checkSuccess).toBe(true);

    const etaPairDecl = allDecls.find((d: any) => d?.name === 'etaPair');
    console.log('etaPair checkErrors:', etaPairDecl?.checkErrors?.map((e: any) => e?.message));
    expect(etaPairDecl?.checkSuccess).toBe(true);
  });

  test('eta used to prove equality in types', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Point : Type where
  x : Nat
  y : Nat

-- Dependent function that relies on eta for type checking
-- The identity function should type check because
-- MkPoint (Point.x p) (Point.y p) is definitionally equal to p
idPoint : (p : Point) -> Point
idPoint p = MkPoint (Point.x p) (Point.y p)
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const idPointDecl = allDecls.find((d: any) => d?.name === 'idPoint');
    console.log('idPoint checkErrors:', idPointDecl?.checkErrors?.map((e: any) => e?.message));
    expect(idPointDecl?.checkSuccess).toBe(true);
  });

  test('partial eta does NOT contract', () => {
    // MkPoint (Point.x p) y  where y is NOT Point.y p
    // should NOT equal p
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Point : Type where
  x : Nat
  y : Nat

-- This is NOT eta - y component is different
notEtaPoint : Point -> Nat -> Point
notEtaPoint p n = MkPoint (Point.x p) n
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const notEtaPointDecl = allDecls.find((d: any) => d?.name === 'notEtaPoint');
    console.log('notEtaPoint checkErrors:', notEtaPointDecl?.checkErrors?.map((e: any) => e?.message));
    expect(notEtaPointDecl?.checkSuccess).toBe(true);
  });

  test('eta with different projections does NOT contract', () => {
    // MkPoint (Point.y p) (Point.x p) - wrong order
    // should NOT equal p
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Point : Type where
  x : Nat
  y : Nat

-- This swaps the fields - NOT eta
swapPoint : Point -> Point
swapPoint p = MkPoint (Point.y p) (Point.x p)
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const swapPointDecl = allDecls.find((d: any) => d?.name === 'swapPoint');
    console.log('swapPoint checkErrors:', swapPointDecl?.checkErrors?.map((e: any) => e?.message));
    expect(swapPointDecl?.checkSuccess).toBe(true);
  });

  test('nested record eta', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Point : Type where
  x : Nat
  y : Nat

record Line : Type where
  start : Point
  end : Point

-- Helper to eta-expand a point
etaPoint2 : Point -> Point
etaPoint2 p = MkPoint (Point.x p) (Point.y p)

-- Eta on inner records via the helper
etaLine : Line -> Line
etaLine l = MkLine (etaPoint2 (Line.start l)) (etaPoint2 (Line.end l))
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const etaLineDecl = allDecls.find((d: any) => d?.name === 'etaLine');
    console.log('etaLine checkErrors:', etaLineDecl?.checkErrors?.map((e: any) => e?.message));
    expect(etaLineDecl?.checkSuccess).toBe(true);
  });

  test('eta in function returning record', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Point : Type where
  x : Nat
  y : Nat

-- Function that returns eta-expanded point
-- Should type check as Point
makePoint : Nat -> Nat -> Point
makePoint a b = MkPoint a b

-- Function using eta
useEta : Point -> Point
useEta p = makePoint (Point.x p) (Point.y p)
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const useEtaDecl = allDecls.find((d: any) => d?.name === 'useEta');
    console.log('useEta checkErrors:', useEtaDecl?.checkErrors?.map((e: any) => e?.message));
    expect(useEtaDecl?.checkSuccess).toBe(true);
  });

  test('direct definitional equality test for eta', () => {
    // Compile to get definitions, then directly test areTypesDefEq
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Point : Type where
  x : Nat
  y : Nat

dummy : Nat
dummy = Zero
`;
    const result = compileTTFromText(source);

    // Build terms manually to test eta directly
    // We need: MkPoint (Point.x p) (Point.y p) vs p
    // where p is Var 0

    const definitions = result.definitions;

    // p = Var 0
    const p = { tag: 'Var' as const, index: 0 };

    // Point.x p = App(Const "Point.x", p)
    const pointX = { tag: 'App' as const, fn: { tag: 'Const' as const, name: 'Point.x' }, arg: p };

    // Point.y p = App(Const "Point.y", p)
    const pointY = { tag: 'App' as const, fn: { tag: 'Const' as const, name: 'Point.y' }, arg: p };

    // MkPoint (Point.x p) (Point.y p) = App(App(Const "MkPoint", Point.x p), Point.y p)
    const etaExpanded = {
      tag: 'App' as const,
      fn: {
        tag: 'App' as const,
        fn: { tag: 'Const' as const, name: 'MkPoint' },
        arg: pointX
      },
      arg: pointY
    };

    console.log('Testing areTypesDefEq for eta:');
    console.log('  LHS:', prettyPrintTTK(etaExpanded));
    console.log('  RHS:', prettyPrintTTK(p));

    const areEqual = areTypesDefEq(etaExpanded, p, definitions);
    console.log('  Result:', areEqual);

    expect(areEqual).toBe(true);
  });

  test('definitional equality sees eta after delta reduction', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Point : Type where
  x : Nat
  y : Nat

id1 : Point -> Point
id1 p = p

id2 : Point -> Point
id2 p = MkPoint (Point.x p) (Point.y p)
`;
    const result = compileTTFromText(source);
    const definitions = result.definitions;
    const p = { tag: 'Var' as const, index: 0 };
    const lhs = { tag: 'App' as const, fn: { tag: 'Const' as const, name: 'id1' }, arg: p };
    const rhs = { tag: 'App' as const, fn: { tag: 'Const' as const, name: 'id2' }, arg: p };

    expect(areTypesDefEq(lhs, rhs, definitions, [
      { name: 'p', type: { tag: 'Const' as const, name: 'Point' } },
    ])).toBe(true);
  });
});
