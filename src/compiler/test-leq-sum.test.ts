/**
 * Test leqImpliesSum with DPair and type-at-cursor for pattern variables
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';
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

describe('leqImpliesSum with DPair', () => {
  test('leqImpliesSum type checks with corrected signature', () => {
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
  LeqZero : {b : Nat} -> Leq Zero b
  LeqSucc : {a b : Nat} -> Leq a b -> Leq (Succ a) (Succ b)

record DPair (A : Type) (fn : A -> Type) where
  constructor MkDPair
  fst : A
  snd : fn fst

leqImpliesSum : (a b : Nat) -> Leq a b -> DPair Nat (\\n => Equal b (plus a n))
leqImpliesSum Zero b LeqZero = MkDPair {fn := \\n => Equal b (plus Zero n)} b refl
leqImpliesSum (Succ a) b (LeqSucc s) = ?hole
`;

    console.log('=== COMPILING ===');
    const result = compileTTFromText(source);
    console.log('Compile success:', result.success);

    if (!result.success) {
      console.log('\n=== ERRORS ===');
      console.log('Num blocks:', result.blocks.length);
      result.blocks.forEach((block, i) => {
        console.log(`Block ${i}: numDecls: ${block.declarations.length}`);
        block.declarations.forEach(decl => {
          console.log(`  Decl: ${decl.name}, checkSuccess: ${decl.checkSuccess}, numErrors: ${decl.checkErrors.length}`);
          if (decl.checkErrors.length > 0) {
            console.log(`    ${decl.name} errors:`);
            decl.checkErrors.forEach(e => console.log('      -', e.message));
          }
        });
      });
    }

    const decl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'leqImpliesSum');

    console.log('\n=== DECLARATION ===');
    console.log('Found leqImpliesSum:', !!decl);
    console.log('Check success:', decl?.checkSuccess);
    console.log('Pretty type:', decl?.prettyType);
    console.log('Pretty value:', decl?.prettyValue);

    expect(result.success).toBe(true);
    expect(decl?.checkSuccess).toBe(true);
  });
});

describe('Pattern variable types with implicit unification', () => {
  const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

-- Type that uses Leq in a pattern
leqPred : (a b : Nat) -> Leq (Succ a) (Succ b) -> Leq a b
leqPred a b (LeqSucc leq) = leq
`;

  test('pattern variable "leq" should have type mentioning a and b, not n and m', () => {
    const results = compileSource(source);
    const leqPredBlock = results.find(r => r.name === 'leqPred');
    expect(leqPredBlock).toBeDefined();
    expect(leqPredBlock!.checkSuccess).toBe(true);

    const decl = leqPredBlock!.declarations[0];
    expect(decl.sourceMap).toBeDefined();
    expect(decl.typeInfoMap).toBeDefined();

    if (decl.sourceMap && decl.typeInfoMap) {
      // Find the "leq" pattern variable inside (LeqSucc leq)
      // It should be at value.clauses[0].patterns[2].args[0] (surface syntax, since {n} {m} are implicit)

      // Let's first see what paths we have
      const patternPaths = [...decl.sourceMap.entries()]
        .filter(([path]) => path.includes('patterns[2]'))
        .map(([path, range]) => ({ path, range }));

      console.log('Pattern paths:', patternPaths.map(p => p.path));

      // Find the leq argument - it should be args[0] in surface syntax since {n} {m} are implicit
      const leqArgPath = 'value.clauses[0].patterns[2].args[0]';
      const leqArgRange = decl.sourceMap.get(leqArgPath);

      if (leqArgRange) {
        const result = getTypeAtCursor(
          leqArgRange.start.pos,
          decl.sourceMap,
          decl.elabMap,
          decl.typeInfoMap,
        );

        console.log('Type at leq:', result?.prettyType);
        console.log('Context:', result?.context);

        expect(result).toBeDefined();
        if (result) {
          // The type should be "Leq a b" not "Leq n m"
          // because unification should have determined that n=a and m=b
          expect(result.prettyType).toBe('(Leq a b)');

          // The context should NOT contain n and m
          const contextNames = result.context.map(c => c.name);
          expect(contextNames).not.toContain('n');
          expect(contextNames).not.toContain('m');
        }
      } else {
        // If args[0] doesn't exist, try finding where leq is
        const allArgs = patternPaths.filter(p => p.path.includes('.args['));
        console.log('All arg paths:', allArgs.map(p => p.path));
        throw new Error('Could not find leq argument path');
      }
    }
  });

  test('context for pattern var should not include unifiable implicit binders', () => {
    const results = compileSource(source);
    const leqPredBlock = results.find(r => r.name === 'leqPred');
    const decl = leqPredBlock!.declarations[0];

    if (decl.sourceMap && decl.typeInfoMap) {
      // The context at "leq" should be:
      // a : Nat, b : Nat
      // NOT: a : Nat, b : Nat, n : Nat, m : Nat

      const leqArgPath = 'value.clauses[0].patterns[2].args[0]';
      const leqArgRange = decl.sourceMap.get(leqArgPath);

      if (leqArgRange) {
        const result = getTypeAtCursor(
          leqArgRange.start.pos,
          decl.sourceMap,
          decl.elabMap,
          decl.typeInfoMap,
        );

        if (result) {
          // Context should only have a and b from the function signature
          // plus possibly leq itself (if it's in scope)
          const contextNames = result.context.map(c => c.name);
          console.log('Full context:', result.context);

          // Check that n and m are NOT in the context
          expect(contextNames).not.toContain('n');
          expect(contextNames).not.toContain('m');

          // a and b should be in the context
          expect(contextNames).toContain('a');
          expect(contextNames).toContain('b');
        }
      }
    }
  });
});
