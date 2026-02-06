/**
 * Minimal test to debug the DPair pattern variable issue.
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Minimal DPair test', () => {
  test('minimal failing case', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record DPair (A : Type) (fn : A -> Type) where
  constructor MkDPair
  fst : A
  snd : fn fst

threeArgs : Nat -> Nat -> Nat -> Nat
threeArgs a b c = a

makePair : Nat -> DPair Nat (\\_ => Nat)
makePair n = MkDPair n n

testFn : Nat -> Nat -> Nat
testFn start fn with makePair start
  | MkDPair count _ => threeArgs start count fn
`;

    const result = compileTTFromText(source);

    const auxDecl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name?.includes('with'));

    console.log('\nAuxiliary:', auxDecl?.name, 'success:', auxDecl?.checkSuccess);
    if (auxDecl && !auxDecl.checkSuccess) {
      console.log('Errors:');
      auxDecl.checkErrors.forEach(e => console.log('  -', e.message));
    }

    const decl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'testFn');

    expect(decl?.checkSuccess).toBe(true);
  });
});
