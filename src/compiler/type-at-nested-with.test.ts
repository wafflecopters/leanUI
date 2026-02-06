/**
 * Test type-at-cursor for nested with-clauses
 */
import { describe, test, expect } from 'vitest';
import { compileSource } from '../test-utils';
import {
  getTypeAtCursor as getTypeAtCursorNew,
  TypeInfoMap,
  TypeAtCursorResult,
} from './type-info';
import { SourceMap, ElabMap } from '../types/source-position';
import { DefinitionsMap } from './term';

// Backward-compatible wrapper
function getTypeAtCursor(
  pos: number,
  sourceMap: SourceMap,
  elabMap: ElabMap | undefined,
  typeInfoMap: TypeInfoMap | undefined,
  definitions?: DefinitionsMap,
): TypeAtCursorResult | undefined {
  const result = getTypeAtCursorNew(pos, sourceMap, elabMap, typeInfoMap, undefined, definitions);
  return result?.kind === 'term' ? result.info : undefined;
}

describe('type-at-cursor for nested with-clauses', () => {
  const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ n) m = Succ (plus n m)

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

record DPair (A : Type) (fn : A -> Type) where
  fst : A
  snd : fn fst

succCong : {u v : Nat} -> Equal u v -> Equal (Succ u) (Succ v)
succCong refl = refl

leqImpliesSum : (a b : Nat) -> Leq a b -> DPair Nat (\\n => Equal b (plus a n))
leqImpliesSum Zero b LeqZero = MkDPair b refl
leqImpliesSum (Succ a) (Succ b) (LeqSucc leq) with leqImpliesSum a b leq
  | MkDPair n pf => MkDPair n (succCong pf)

inductive Either : Type -> Type -> Type where
  inl : {L R : Type} -> L -> Either L R
  inr : {L R : Type} -> R -> Either L R

decGeq : (a b : Nat) -> Either (Leq a b) (Leq (Succ b) a)
decGeq Zero b = inl LeqZero
decGeq (Succ a) Zero = inr (LeqSucc (LeqZero {n:=a}))
decGeq (Succ a) (Succ b) with decGeq a b
  | inl aLeqB => inl (LeqSucc aLeqB)
  | inr bLeA => inr (LeqSucc bLeA)

sigmaSum : (start end : Nat) -> (fn : (index : Nat) -> Nat) -> Nat
sigmaSum start end fn with decGeq start end
  | inl startLeqEnd with leqImpliesSum start end startLeqEnd
    | MkDPair count _ => count
  | inr _ => Zero
`;

  function getSigmaSumDecl() {
    const results = compileSource(source);
    const block = results.find(r =>
      r.declarations.some(d => d.name === 'sigmaSum')
    );
    expect(block).toBeDefined();
    const decl = block!.declarations.find(d => d.name === 'sigmaSum');
    expect(decl).toBeDefined();
    expect(decl!.checkSuccess).toBe(true);
    expect(decl!.sourceMap).toBeDefined();
    expect(decl!.typeInfoMap).toBeDefined();
    return decl!;
  }

  test('type-at for nested with scrutinee expression', () => {
    const decl = getSigmaSumDecl();
    if (!decl.sourceMap || !decl.typeInfoMap) return;

    // Find the position of "leqImpliesSum" in the nested with-clause INSIDE sigmaSum
    // sigmaSum start end fn with decGeq start end
    //   | inl startLeqEnd with leqImpliesSum start end startLeqEnd
    //                          ^-- cursor here
    const sourceText = source;
    // Find "sigmaSum" first, then search for "with leqImpliesSum" after that
    const sigmaSumIndex = sourceText.indexOf('sigmaSum : (start end');
    expect(sigmaSumIndex).toBeGreaterThan(0);
    const searchStr = 'with leqImpliesSum';
    const matchIndex = sourceText.indexOf(searchStr, sigmaSumIndex);
    expect(matchIndex).toBeGreaterThan(0);

    // Position cursor at the 'l' in 'leqImpliesSum'
    const cursorPos = matchIndex + 'with '.length;

    console.log('\n=== DEBUGGING NESTED WITH ===');
    console.log('Cursor position:', cursorPos);

    // List all sourceMap entries containing 'withClauses'
    console.log('\nSourceMap entries with withClauses:');
    for (const [path, range] of decl.sourceMap) {
      if (path.includes('withClauses')) {
        console.log(`  ${path}: ${range.start.pos}-${range.end.pos}`);
      }
    }

    // List all typeInfoMap entries
    console.log('\nTypeInfoMap entries (first 20):');
    let count = 0;
    for (const [path, info] of decl.typeInfoMap) {
      if (count++ < 20) {
        console.log(`  ${path}`);
      }
    }
    console.log(`  ... (${decl.typeInfoMap.size} total entries)`);

    const result = getTypeAtCursor(
      cursorPos,
      decl.sourceMap,
      decl.elabMap,
      decl.typeInfoMap,
      decl.definitions
    );

    console.log('\nType-at result:', result);
    if (result) {
      console.log('Pretty type:', result.prettyType);
      console.log('Surface path:', result.surfacePath);
      console.log('Kernel path:', result.kernelPath);
    }

    // EXPECT: Should find type info for leqImpliesSum
    // Expected type: (a b : Nat) -> Leq a b -> DPair Nat (\n => Equal b (plus a n))
    expect(result).toBeDefined();
    expect(result?.prettyType).toContain('DPair');
  });

  test('type-at for pattern variable in nested with-clause', () => {
    const decl = getSigmaSumDecl();
    if (!decl.sourceMap || !decl.typeInfoMap) return;

    // Find the position of "count" in the nested pattern match
    // | MkDPair count _ => count
    //          ^-- cursor here (first occurrence)
    const sourceText = source;
    const searchStr = 'MkDPair count';
    const matchIndex = sourceText.lastIndexOf(searchStr); // Last occurrence is in sigmaSum
    expect(matchIndex).toBeGreaterThan(0);

    // Position cursor at the 'c' in 'count'
    const cursorPos = matchIndex + 'MkDPair '.length;

    const result = getTypeAtCursor(
      cursorPos,
      decl.sourceMap,
      decl.elabMap,
      decl.typeInfoMap,
      decl.definitions
    );

    console.log('Cursor position:', cursorPos);
    console.log('Type-at result:', result);
    if (result) {
      console.log('Pretty type:', result.prettyType);
      console.log('Surface path:', result.surfacePath);
      console.log('Kernel path:', result.kernelPath);
    }

    // EXPECT: Should find type info for count pattern variable
    // Expected type: Nat
    expect(result).toBeDefined();
    expect(result?.prettyType).toBe('Nat');
  });

  test('type-at for RHS expression in nested with-clause', () => {
    const decl = getSigmaSumDecl();
    if (!decl.sourceMap || !decl.typeInfoMap) return;

    // Find the position of "count" in the RHS (second occurrence in the line)
    // | MkDPair count _ => count
    //                      ^-- cursor here (RHS)
    const sourceText = source;
    const searchStr = '| MkDPair count _ => count';
    const matchIndex = sourceText.lastIndexOf(searchStr);
    expect(matchIndex).toBeGreaterThan(0);

    // Position cursor at the 'c' in the second 'count' (RHS)
    const cursorPos = matchIndex + '| MkDPair count _ => '.length;

    const result = getTypeAtCursor(
      cursorPos,
      decl.sourceMap,
      decl.elabMap,
      decl.typeInfoMap,
      decl.definitions
    );

    console.log('Cursor position:', cursorPos);
    console.log('Type-at result:', result);
    if (result) {
      console.log('Pretty type:', result.prettyType);
      console.log('Surface path:', result.surfacePath);
      console.log('Kernel path:', result.kernelPath);
    }

    // EXPECT: Should find type info for count variable in RHS
    // Expected type: Nat
    expect(result).toBeDefined();
    expect(result?.prettyType).toBe('Nat');
  });
});
