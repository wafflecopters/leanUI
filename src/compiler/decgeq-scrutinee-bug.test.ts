import { describe, test, expect } from 'vitest';
import { compileSource } from '../test-utils';
import { getTypeAtCursor } from './type-info';

describe('decGeq scrutinee bug', () => {
  test('hole type should not contain ?_scrutinee', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

inductive LessThan : Nat -> Nat -> Type where
  LtSucc : {n : Nat} -> LessThan n (Succ n)
  LtStep : {n m : Nat} -> LessThan n m -> LessThan n (Succ m)

inductive Either : Type -> Type -> Type where
  inl : {A B : Type} -> A -> Either A B
  inr : {A B : Type} -> B -> Either A B

decGeq : (a b : Nat) -> Either (Leq a b) (LessThan b a)
decGeq Zero b = inl LeqZero
decGeq (Succ a) Zero = inr ?p
decGeq (Succ a) (Succ b) = ?C
`;

    const results = compileSource(source);
    const decGeqBlock = results.find(r => r.name === 'decGeq');
    expect(decGeqBlock).toBeDefined();

    const decl = decGeqBlock!.declarations[0];
    console.log('\nCheck success:', decl.checkSuccess);
    console.log('Pretty value:', decl.prettyValue);

    if (decl.sourceMap && decl.typeInfoMap) {
      console.log('\nSearching for hole ?p...');

      // Search through all paths for the hole
      for (const [path, range] of decl.sourceMap) {
        const sourceSubstr = source.substring(range.start.pos, range.end.pos);
        if (sourceSubstr === '?p' || path.includes('?p')) {
          console.log(`Found at path: ${path}, pos: ${range.start.pos}`);

          const typeInfo = getTypeAtCursor(
            range.start.pos,
            decl.sourceMap,
            decl.elabMap,
            decl.typeInfoMap,
            undefined,
            decl.definitions
          );

          if (typeInfo?.kind === 'term') {
            console.log('\nType info for ?p:');
            console.log('Type:', typeInfo.info.prettyType);
            console.log('Expected:', typeInfo.info.expectedType);
            console.log('Context:', typeInfo.info.context.map(c => `${c.name}: ${c.type}`).join(', '));

            // Check if the type contains _scrutinee
            const typeStr = JSON.stringify(typeInfo.info.type);
            const expectedStr = typeInfo.info.expectedType ? JSON.stringify(typeInfo.info.expectedType) : '';

            if (typeStr.includes('_scrutinee')) {
              console.log('\n!!! FOUND _scrutinee in type !!!');
              console.log('Type structure:', JSON.stringify(typeInfo.info.type, null, 2));
            }

            if (expectedStr.includes('_scrutinee')) {
              console.log('\n!!! FOUND _scrutinee in expectedType !!!');
            }

            // The bug: _scrutinee should NOT appear in types
            expect(typeStr).not.toContain('_scrutinee');
            expect(expectedStr).not.toContain('_scrutinee');
            expect(typeInfo.info.prettyType).not.toContain('_scrutinee');
            if (typeInfo.info.expectedType) {
              expect(typeInfo.info.expectedType).not.toContain('_scrutinee');
            }
          }
        }
      }
    }
  });
});
