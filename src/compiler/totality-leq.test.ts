import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';
import { arePatternsAbsurd } from './patterns';
import { TTKPattern } from './kernel';
import { createTCEnv } from './term';

describe('Totality: Leq incomplete match', () => {
  test('leqCanonical missing LeqSucc case is non-exhaustive', () => {
    const result = compileTTFromText(`
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

leqCanonical : {a b : Nat} -> (p q : Leq a b) -> Equal p q
leqCanonical LeqZero q = ?Foo
`);

    const leqDecl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'leqCanonical');

    expect(leqDecl).toBeDefined();

    // The function is missing the LeqSucc case — it should NOT be exhaustive
    expect(leqDecl!.totalityResult?.isExhaustive).toBe(false);
    expect(leqDecl!.totalityResult?.missingValidClauses.length).toBeGreaterThan(0);
  });

  test('arePatternsAbsurd correctly handles dependent indexed types', () => {
    const result = compileTTFromText(`
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

leqCanonical : {a b : Nat} -> (p q : Leq a b) -> Equal p q
leqCanonical LeqZero q = ?Foo
leqCanonical (LeqSucc p') q = ?Bar
`);

    const leqType = result.definitions.terms.get('leqCanonical')?.type;
    expect(leqType).toBeDefined();

    const env = createTCEnv({ definitions: result.definitions, options: { mode: 'check' } });

    const leqSuccPattern: TTKPattern = {
      tag: 'PCtor', name: 'LeqSucc',
      args: [
        { tag: 'PWild', name: '_' },
        { tag: 'PWild', name: '_' },
        { tag: 'PWild', name: '_' },
      ]
    };

    // [_, _, LeqSucc(_, _, _), _] is NOT absurd — it's a valid missing case
    const paddedPatterns: TTKPattern[] = [
      { tag: 'PWild', name: '_' },
      { tag: 'PWild', name: '_' },
      leqSuccPattern,
      { tag: 'PWild', name: '_' },
    ];
    expect(arePatternsAbsurd('leqCanonical', env.withValue(paddedPatterns), leqType!)).toBe(false);

    // [_, Succ(_), LeqSucc(_, _, _), _] is NOT absurd — b=Succ x is compatible with LeqSucc
    const splitPatterns: TTKPattern[] = [
      { tag: 'PWild', name: '_' },
      { tag: 'PCtor', name: 'Succ', args: [{ tag: 'PWild', name: '_' }] },
      leqSuccPattern,
      { tag: 'PWild', name: '_' },
    ];
    expect(arePatternsAbsurd('leqCanonical', env.withValue(splitPatterns), leqType!)).toBe(false);

    // [_, Zero, LeqSucc(_, _, _), _] IS absurd — b=Zero conflicts with LeqSucc (b=Succ m)
    const absurdPatterns: TTKPattern[] = [
      { tag: 'PWild', name: '_' },
      { tag: 'PCtor', name: 'Zero', args: [] },
      leqSuccPattern,
      { tag: 'PWild', name: '_' },
    ];
    expect(arePatternsAbsurd('leqCanonical', env.withValue(absurdPatterns), leqType!)).toBe(true);
  });
});
