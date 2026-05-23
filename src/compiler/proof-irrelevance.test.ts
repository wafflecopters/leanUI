import { describe, test, expect } from 'vitest';
import {
  TTKTerm,
  mkProp,
  mkType,
  mkVar,
  mkApp,
  mkConst,
  mkPi,
} from './kernel';
import { areTypesDefEq } from './whnf';
import { compileTTFromText } from './compile';

/**
 * End-to-end proof-irrelevance tests via the real compiler.
 *
 * The kernel-level helper `isProofIrrelevantEq` is exercised indirectly:
 * we compile a `.tt`-style program and rely on `areTypesDefEq` (called
 * from the type checker) to apply the rule. Direct unit tests against
 * a fabricated TCEnv are brittle because TCEnv carries lots of state;
 * compileTTFromText is the canonical fixture.
 */
describe('Proof irrelevance — defeq behaviour', () => {
  test('Two distinct constructors of a Prop-valued inductive are defeq', () => {
    const source = `
inductive EqualProp : {P : Prop} -> P -> P -> Prop where
  reflProp : {P : Prop} -> {p : P} -> EqualProp p p

inductive P : Prop where
  pa : P
  pb : P

paEqPb : EqualProp pa pb
paEqPb = reflProp
`;
    const result = compileTTFromText(source);
    const decls = result.blocks.flatMap(b => b.declarations);
    expect(decls.every(d => d.checkSuccess !== false)).toBe(true);
  });

  test('Two distinct constructors of a Type-valued inductive are NOT defeq', () => {
    const source = `
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

inductive Bool : Type where
  TT : Bool
  FF : Bool

ttEqFf : Equal TT FF
ttEqFf = refl
`;
    const result = compileTTFromText(source);
    const decls = result.blocks.flatMap(b => b.declarations);
    const ttEqFf = decls.find(d => d.name === 'ttEqFf');
    expect(ttEqFf?.checkSuccess).toBe(false);
  });

  test('Hypothetical proofs of the same Prop are interchangeable', () => {
    const source = `
inductive EqualProp : {P : Prop} -> P -> P -> Prop where
  reflProp : {P : Prop} -> {p : P} -> EqualProp p p

inductive P : Prop where
  triv : P

swap : (h1 : P) -> (h2 : P) -> EqualProp h1 h2
swap h1 h2 = reflProp
`;
    const result = compileTTFromText(source);
    const decls = result.blocks.flatMap(b => b.declarations);
    const swap = decls.find(d => d.name === 'swap');
    expect(swap?.checkSuccess).toBe(true);
  });

  test('areTypesDefEq returns false for terms without a Prop type and no typing context', () => {
    // Without a typing context, proof irrelevance can't kick in — we fall
    // back to structural equality. mkConst("a") and mkConst("b") are
    // structurally distinct.
    const a = mkConst('a');
    const b = mkConst('b');
    expect(areTypesDefEq(a, b)).toBe(false);
  });

  test('areTypesDefEq leaves regular type comparisons intact', () => {
    // Nat vs Nat — defeq by structural identity, regardless of proof irrelevance.
    expect(areTypesDefEq(mkConst('Nat'), mkConst('Nat'))).toBe(true);
    // Nat vs Bool — structurally distinct, no proof irrelevance applies (types aren't proofs).
    expect(areTypesDefEq(mkConst('Nat'), mkConst('Bool'))).toBe(false);
  });

  test('areTypesDefEq leaves Sort comparisons intact', () => {
    expect(areTypesDefEq(mkProp(), mkProp())).toBe(true);
    expect(areTypesDefEq(mkType(0), mkType(0))).toBe(true);
    expect(areTypesDefEq(mkProp(), mkType(0))).toBe(false);
    expect(areTypesDefEq(mkType(0), mkType(1))).toBe(false);
  });

  test('areTypesDefEq leaves Pi comparisons intact', () => {
    // (Nat -> Nat) vs (Nat -> Nat) → equal
    const pi1 = mkPi(mkConst('Nat'), mkConst('Nat'), '_');
    const pi2 = mkPi(mkConst('Nat'), mkConst('Nat'), '_');
    expect(areTypesDefEq(pi1, pi2)).toBe(true);
    // (Nat -> Bool) vs (Nat -> Nat) → not equal
    const pi3 = mkPi(mkConst('Nat'), mkConst('Bool'), '_');
    expect(areTypesDefEq(pi1, pi3)).toBe(false);
  });
});
