/**
 * Test what record DPair elaborates to
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';
import { prettyPrint } from './kernel';

describe('Record DPair elaboration', () => {
  test('inspect what DPair record becomes', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record DPair (A : Type) (fn : A -> Type) where
  constructor MkDPair
  fst : A
  snd : fn fst
`;

    const result = compileTTFromText(source);

    const dpairDecl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'DPair');

    console.log('=== DPAIR RECORD ELABORATION ===');
    console.log('Found:', !!dpairDecl);
    console.log('Check success:', dpairDecl?.checkSuccess);

    if (dpairDecl?.kernelType) {
      console.log('\nInductive type:');
      console.log('  Type:', prettyPrint(dpairDecl.kernelType, [], new Map()));
      console.log('  Num constructors:', dpairDecl.kernelConstructors?.length);

      if (dpairDecl.kernelConstructors && dpairDecl.kernelConstructors.length > 0) {
        const ctor = dpairDecl.kernelConstructors[0];
        console.log('\nConstructor:');
        console.log('  Name:', ctor.name);
        console.log('  Type:', prettyPrint(ctor.type, [], new Map()));
      }
    }

    if (dpairDecl && !dpairDecl.checkSuccess) {
      console.log('\nErrors:');
      dpairDecl.checkErrors.forEach(e => console.log('  -', e.message));
    }

    expect(result.success).toBe(true);
    expect(dpairDecl?.checkSuccess).toBe(true);
  });
});
