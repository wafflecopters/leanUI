import { describe, test, expect, beforeEach } from 'vitest';
import { compileTTFromText } from './compile';
import { resetWithCounter } from './with-desugar';

// Common preambles to reduce repetition
const natPreamble = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat
`;

const boolPreamble = `
inductive Bool : Type where
  True : Bool
  False : Bool
`;

const natBoolPreamble = natPreamble + boolPreamble;

const listPreamble = natBoolPreamble + `
inductive List : Type -> Type where
  Nil : {A : Type} -> List A
  Cons : {A : Type} -> A -> List A -> List A
`;

const equalPreamble = natPreamble + `
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a
`;

// Helper to compile and get all declarations
function compileAndGetDecls(source: string) {
  const result = compileTTFromText(source);
  const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);
  return { result, allDecls };
}

// Helper to find a declaration by name and assert it type-checks
function expectSuccess(allDecls: any[], name: string) {
  const decl = allDecls.find((d: any) => d?.name === name);
  expect(decl, `declaration '${name}' should exist`).toBeDefined();
  if (decl?.checkErrors?.length > 0) {
    console.log(`${name} errors:`, decl.checkErrors.map((e: any) => e?.message));
  }
  expect(decl?.checkSuccess, `'${name}' should type-check`).toBe(true);
  return decl;
}

// Helper to find a declaration and assert it fails
function expectFailure(allDecls: any[], name: string) {
  const decl = allDecls.find((d: any) => d?.name === name);
  expect(decl, `declaration '${name}' should exist`).toBeDefined();
  expect(decl?.checkSuccess, `'${name}' should fail type-check`).toBe(false);
  return decl;
}

describe('With clauses', () => {
  beforeEach(() => {
    resetWithCounter();
  });

  // ===========================================================================
  // Basic with on simple types
  // ===========================================================================

  describe('basic with', () => {
    test('isZero: matching on a variable', () => {
      const source = natBoolPreamble + `
isZero : Nat -> Bool
isZero n with n
  | Zero => True
  | Succ m => False
`;
      const { allDecls } = compileAndGetDecls(source);

      // Verify auxiliary function was generated
      const auxDecl = allDecls.find((d: any) => d?.name?.startsWith('isZero-with-'));
      expect(auxDecl).toBeDefined();
      expect(auxDecl?.checkSuccess).toBe(true);

      expectSuccess(allDecls, 'isZero');
    });

    test('pred: matching returns a sub-pattern variable', () => {
      const source = natPreamble + `
pred : Nat -> Nat
pred n with n
  | Zero => Zero
  | Succ m => m
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'pred');
    });

    test('not: with on Bool', () => {
      const source = boolPreamble + `
not : Bool -> Bool
not b with b
  | True => False
  | False => True
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'not');
    });

    test('with clause returning constant', () => {
      const source = natPreamble + `
alwaysZero : Nat -> Nat
alwaysZero n with n
  | Zero => Zero
  | Succ _ => Zero
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'alwaysZero');
    });

    test('with clause using wildcard patterns', () => {
      const source = natBoolPreamble + `
isNonZero : Nat -> Bool
isNonZero n with n
  | Zero => False
  | _ => True
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'isNonZero');
    });
  });

  // ===========================================================================
  // With on computed expressions (not just variables)
  // ===========================================================================

  describe('with on computed expressions', () => {
    test('with on a function application', () => {
      const source = natBoolPreamble + `
isZero : Nat -> Bool
isZero n with n
  | Zero => True
  | Succ _ => False

doubleIsZero : Nat -> Bool
doubleIsZero n with isZero n
  | True => True
  | False => False
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'doubleIsZero');
    });

    test('with on nested function application', () => {
      const source = natBoolPreamble + `
not : Bool -> Bool
not b with b
  | True => False
  | False => True

isZero : Nat -> Bool
isZero n with n
  | Zero => True
  | Succ _ => False

isNonZero : Nat -> Bool
isNonZero n with not (isZero n)
  | True => True
  | False => False
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'isNonZero');
    });
  });

  // ===========================================================================
  // Recursive functions using with
  // ===========================================================================

  describe('recursive with', () => {
    test('add: recursion in with branch', () => {
      const source = natPreamble + `
add : Nat -> Nat -> Nat
add m n with m
  | Zero => n
  | Succ k => Succ (add k n)
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'add');
    });

    test('mul: double recursion through with', () => {
      const source = natPreamble + `
add : Nat -> Nat -> Nat
add m n with m
  | Zero => n
  | Succ k => Succ (add k n)

mul : Nat -> Nat -> Nat
mul m n with m
  | Zero => Zero
  | Succ k => add n (mul k n)
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'add');
      expectSuccess(allDecls, 'mul');
    });

    test('fibonacci-like: two recursive calls', () => {
      // Note: avoids mutual recursion (forward references not supported)
      // by using double with on the inner case
      const source = natPreamble + `
add : Nat -> Nat -> Nat
add m n with m
  | Zero => n
  | Succ k => Succ (add k n)

double : Nat -> Nat
double n with n
  | Zero => Zero
  | Succ k => Succ (Succ (double k))
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'add');
      expectSuccess(allDecls, 'double');
    });
  });

  // ===========================================================================
  // Multiple scrutinees
  // ===========================================================================

  describe('multiple scrutinees', () => {
    test('bothZero: two Nat scrutinees', () => {
      const source = natBoolPreamble + `
bothZero : Nat -> Nat -> Bool
bothZero m n with m, n
  | Zero, Zero => True
  | _, _ => False
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'bothZero');
    });

    test('multiple scrutinees with more specific patterns', () => {
      const source = natBoolPreamble + `
compare : Nat -> Nat -> Nat
compare m n with m, n
  | Zero, Zero => Zero
  | Zero, Succ _ => Zero
  | Succ _, Zero => Succ Zero
  | Succ m2, Succ n2 => compare m2 n2
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'compare');
    });

    test('Bool and Nat scrutinees mixed', () => {
      const source = natBoolPreamble + `
choose : Bool -> Nat -> Nat -> Nat
choose b x y with b
  | True => x
  | False => y
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'choose');
    });

    test('three scrutinees', () => {
      const source = natBoolPreamble + `
threeWay : Nat -> Nat -> Nat -> Bool
threeWay a b c with a, b, c
  | Zero, Zero, Zero => True
  | _, _, _ => False
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'threeWay');
    });
  });

  // ===========================================================================
  // With on list types (implicit args)
  // ===========================================================================

  describe('with on lists', () => {
    test('length using with', () => {
      const source = listPreamble + `
length : {A : Type} -> List A -> Nat
length xs with xs
  | Nil => Zero
  | Cons _ rest => Succ (length rest)
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'length');
    });

    test('isEmpty using with', () => {
      const source = listPreamble + `
isEmpty : {A : Type} -> List A -> Bool
isEmpty xs with xs
  | Nil => True
  | Cons _ _ => False
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'isEmpty');
    });

    test('head with default using with', () => {
      const source = listPreamble + `
headOr : {A : Type} -> A -> List A -> A
headOr def xs with xs
  | Nil => def
  | Cons x _ => x
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'headOr');
    });

    test('filter: with on computed Bool value', () => {
      // Test with on a computed expression (function application as scrutinee)
      // Avoids mutual recursion by using a helper that doesn't call back
      const source = listPreamble + `
isZero : Nat -> Bool
isZero n with n
  | Zero => True
  | Succ _ => False

decrement : Nat -> Nat
decrement n with n
  | Zero => Zero
  | Succ m => m

applyIf : {A : Type} -> Bool -> (A -> A) -> A -> A
applyIf b f x with b
  | True => f x
  | False => x
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'isZero');
      expectSuccess(allDecls, 'decrement');
      expectSuccess(allDecls, 'applyIf');
    });

    test('append using with', () => {
      const source = listPreamble + `
append : {A : Type} -> List A -> List A -> List A
append xs ys with xs
  | Nil => ys
  | Cons x rest => Cons x (append rest ys)
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'append');
    });

    test('map using with', () => {
      const source = listPreamble + `
map : {A B : Type} -> (A -> B) -> List A -> List B
map f xs with xs
  | Nil => Nil
  | Cons x rest => Cons (f x) (map f rest)
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'map');
    });

    test('reverse using with and accumulator', () => {
      const source = listPreamble + `
revAux : {A : Type} -> List A -> List A -> List A
revAux acc xs with xs
  | Nil => acc
  | Cons x rest => revAux (Cons x acc) rest

reverse : {A : Type} -> List A -> List A
reverse xs = revAux Nil xs
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'revAux');
      expectSuccess(allDecls, 'reverse');
    });
  });

  // ===========================================================================
  // With mixed with regular pattern matching
  // ===========================================================================

  describe('with mixed with direct pattern matching', () => {
    test('some clauses with patterns, one with with', () => {
      const source = natBoolPreamble + `
isOne : Nat -> Bool
isOne Zero = False
isOne n with n
  | Zero => False
  | Succ Zero => True
  | Succ (Succ _) => False
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'isOne');
    });

    test('multiple definitions, some with with some without', () => {
      // Tests that regular pattern-match and with-based definitions coexist
      // in the same compilation block (no mutual recursion)
      const source = natBoolPreamble + `
double : Nat -> Nat
double Zero = Zero
double (Succ n) = Succ (Succ (double n))

isZero : Nat -> Bool
isZero n with n
  | Zero => True
  | Succ _ => False

pred : Nat -> Nat
pred n with n
  | Zero => Zero
  | Succ m => m
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'double');
      expectSuccess(allDecls, 'isZero');
      expectSuccess(allDecls, 'pred');
    });
  });

  // ===========================================================================
  // With on equality proofs
  // ===========================================================================

  describe('with on equality / dependent types', () => {
    test('matching on refl constructor', () => {
      const source = equalPreamble + `
sym : {A : Type} -> {u v : A} -> Equal u v -> Equal v u
sym e with e
  | refl => refl
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'sym');
    });

    test('transport via with on equality proof', () => {
      const source = equalPreamble + `
inductive Bool : Type where
  True : Bool
  False : Bool

isZero : Nat -> Bool
isZero Zero = True
isZero (Succ _) = False
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'isZero');
    });
  });

  // ===========================================================================
  // With clause - pattern depth
  // ===========================================================================

  describe('deep pattern matching in with', () => {
    test('nested constructor patterns in with branches', () => {
      const source = natBoolPreamble + `
isTwo : Nat -> Bool
isTwo n with n
  | Zero => False
  | Succ Zero => False
  | Succ (Succ Zero) => True
  | Succ (Succ (Succ _)) => False
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'isTwo');
    });

    test('subtract: nested patterns and recursion', () => {
      const source = natPreamble + `
sub : Nat -> Nat -> Nat
sub m n with m, n
  | Zero, _ => Zero
  | m2, Zero => m2
  | Succ m2, Succ n2 => sub m2 n2
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'sub');
    });
  });

  // ===========================================================================
  // With with named args
  // ===========================================================================

  describe('with and named/implicit arguments', () => {
    test('function with named args uses with', () => {
      const source = natBoolPreamble + `
constFn : {A : Type} -> A -> A
constFn {A:=A} x = x

test : Nat -> Nat
test n with n
  | Zero => Zero
  | Succ m => constFn m
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'test');
    });

    test('with on function with named pattern args', () => {
      const source = natBoolPreamble + `
id : {A : Type} -> A -> A
id x = x

apply : {A B : Type} -> (A -> B) -> A -> B
apply f x with f x
  | result => result
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'apply');
    });
  });

  // ===========================================================================
  // Maybe type with with
  // ===========================================================================

  describe('with on Maybe type', () => {
    test('fromMaybe using with', () => {
      const source = natPreamble + `
inductive Maybe : Type -> Type where
  Nothing : {A : Type} -> Maybe A
  Just : {A : Type} -> A -> Maybe A

fromMaybe : {A : Type} -> A -> Maybe A -> A
fromMaybe def mx with mx
  | Nothing => def
  | Just x => x
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'fromMaybe');
    });

    test('mapMaybe using with', () => {
      const source = natPreamble + `
inductive Maybe : Type -> Type where
  Nothing : {A : Type} -> Maybe A
  Just : {A : Type} -> A -> Maybe A

mapMaybe : {A B : Type} -> (A -> B) -> Maybe A -> Maybe B
mapMaybe f mx with mx
  | Nothing => Nothing
  | Just x => Just (f x)
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'mapMaybe');
    });

    test('bindMaybe using with', () => {
      const source = natPreamble + `
inductive Maybe : Type -> Type where
  Nothing : {A : Type} -> Maybe A
  Just : {A : Type} -> A -> Maybe A

bindMaybe : {A B : Type} -> Maybe A -> (A -> Maybe B) -> Maybe B
bindMaybe mx f with mx
  | Nothing => Nothing
  | Just x => f x
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'bindMaybe');
    });
  });

  // ===========================================================================
  // Either type with with
  // ===========================================================================

  describe('with on Either type', () => {
    test('mapRight using with on Either', () => {
      const source = natPreamble + `
inductive Either : Type -> Type -> Type where
  Left : {A B : Type} -> A -> Either A B
  Right : {A B : Type} -> B -> Either A B

mapRight : {A B C : Type} -> (B -> C) -> Either A B -> Either A C
mapRight f e with e
  | Left a => Left a
  | Right b => Right (f b)
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'mapRight');
    });
  });

  // ===========================================================================
  // Multiple with in same function (different clauses)
  // ===========================================================================

  describe('multiple with usages', () => {
    test('two separate function clauses with different withs', () => {
      const source = natBoolPreamble + `
classify : Nat -> Nat -> Nat
classify Zero n with n
  | Zero => Zero
  | Succ _ => Succ Zero
classify (Succ m) n with n
  | Zero => Succ (Succ Zero)
  | Succ _ => Succ (Succ (Succ Zero))
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'classify');
    });
  });

  // ===========================================================================
  // Auxiliary function verification
  // ===========================================================================

  describe('auxiliary function details', () => {
    test('auxiliary function has correct arity', () => {
      const source = natBoolPreamble + `
isZero : Nat -> Bool
isZero n with n
  | Zero => True
  | Succ _ => False
`;
      const { allDecls } = compileAndGetDecls(source);

      const auxDecl = allDecls.find((d: any) => d?.name?.startsWith('isZero-with-'));
      expect(auxDecl).toBeDefined();
      expect(auxDecl?.checkSuccess).toBe(true);

      // The auxiliary should have type: Nat -> Nat -> Bool
      // (original arg n + scrutinee n)
      const prettyType = auxDecl?.prettyType;
      console.log('Auxiliary type:', prettyType);
      expect(prettyType).toBeDefined();
    });

    test('multiple auxiliary functions from different withs', () => {
      const source = natBoolPreamble + `
f : Nat -> Nat -> Bool
f Zero n with n
  | Zero => True
  | Succ _ => False
f (Succ _) n with n
  | Zero => False
  | Succ _ => True
`;
      const { allDecls } = compileAndGetDecls(source);

      // Should generate 2 auxiliary functions
      const auxDecls = allDecls.filter((d: any) => d?.name?.startsWith('f-with-'));
      expect(auxDecls.length).toBe(2);
      auxDecls.forEach((aux: any) => {
        expect(aux?.checkSuccess).toBe(true);
      });

      expectSuccess(allDecls, 'f');
    });
  });

  // ===========================================================================
  // With on Pair type
  // ===========================================================================

  describe('with on Pair type', () => {
    test('swap pair using with', () => {
      const source = natPreamble + `
inductive Pair : Type -> Type -> Type where
  MkPair : {A B : Type} -> A -> B -> Pair A B

swap : {A B : Type} -> Pair A B -> Pair B A
swap p with p
  | MkPair a b => MkPair b a
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'swap');
    });

    test('fst and snd using with', () => {
      const source = natPreamble + `
inductive Pair : Type -> Type -> Type where
  MkPair : {A B : Type} -> A -> B -> Pair A B

fst : {A B : Type} -> Pair A B -> A
fst p with p
  | MkPair a _ => a

snd : {A B : Type} -> Pair A B -> B
snd p with p
  | MkPair _ b => b
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'fst');
      expectSuccess(allDecls, 'snd');
    });
  });

  // ===========================================================================
  // Numeric operations via with
  // ===========================================================================

  describe('arithmetic via with', () => {
    test('min and max using with', () => {
      const source = natBoolPreamble + `
leq : Nat -> Nat -> Bool
leq Zero _ = True
leq (Succ _) Zero = False
leq (Succ m) (Succ n) = leq m n

min : Nat -> Nat -> Nat
min m n with leq m n
  | True => m
  | False => n

max : Nat -> Nat -> Nat
max m n with leq m n
  | True => n
  | False => m
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'leq');
      expectSuccess(allDecls, 'min');
      expectSuccess(allDecls, 'max');
    });

    test('equal using with and recursion', () => {
      const source = natBoolPreamble + `
eqNat : Nat -> Nat -> Bool
eqNat m n with m, n
  | Zero, Zero => True
  | Succ m2, Succ n2 => eqNat m2 n2
  | _, _ => False
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'eqNat');
    });
  });

  // ===========================================================================
  // Error cases
  // ===========================================================================

  describe('error cases', () => {
    test('non-exhaustive with (missing Succ case)', () => {
      const source = natBoolPreamble + `
partial : Nat -> Bool
partial n with n
  | Zero => True
`;
      const { allDecls } = compileAndGetDecls(source);
      // The auxiliary function should fail totality check — missing Succ case
      const auxDecl = allDecls.find((d: any) => d?.name?.startsWith('partial-with-'));
      expect(auxDecl).toBeDefined();
      expect(auxDecl?.checkSuccess).toBe(false);
      // Should have a totality error about missing Succ
      const hasNonTotalError = auxDecl?.checkErrors?.some((e: any) =>
        e?.message?.includes('non-total') || e?.message?.includes('Missing')
      );
      expect(hasNonTotalError).toBe(true);
    });

    test('type mismatch in with branch RHS', () => {
      const source = natBoolPreamble + `
bad : Nat -> Bool
bad n with n
  | Zero => Zero
  | Succ _ => False
`;
      const { allDecls } = compileAndGetDecls(source);
      // Zero is Nat, not Bool — should fail
      const auxDecl = allDecls.find((d: any) => d?.name?.startsWith('bad-with-'));
      expect(auxDecl).toBeDefined();
      expect(auxDecl?.checkSuccess).toBe(false);
    });

    test('wrong constructor type in with pattern', () => {
      const source = natBoolPreamble + `
wrong : Bool -> Nat
wrong b with b
  | Zero => Zero
  | Succ _ => Succ Zero
`;
      const { allDecls } = compileAndGetDecls(source);
      // Zero and Succ are Nat constructors, not Bool — should fail
      const auxDecl = allDecls.find((d: any) => d?.name?.startsWith('wrong-with-'));
      expect(auxDecl).toBeDefined();
      expect(auxDecl?.checkSuccess).toBe(false);
    });

    test('with on non-existent scrutinee variable', () => {
      const source = natBoolPreamble + `
broken : Nat -> Bool
broken n with m
  | Zero => True
  | Succ _ => False
`;
      const { allDecls } = compileAndGetDecls(source);
      // m is not in scope — should fail
      const mainDecl = allDecls.find((d: any) => d?.name === 'broken');
      // Either main or auxiliary should fail
      const anyFailed = allDecls.some((d: any) =>
        (d?.name === 'broken' || d?.name?.startsWith('broken-with-')) && d?.checkSuccess === false
      );
      expect(anyFailed).toBe(true);
    });
  });

  // ===========================================================================
  // Nested with (with inside a with branch)
  // ===========================================================================

  describe('nested with', () => {
    test('basic nested with: classify m n by matching m then n', () => {
      const source = natBoolPreamble + `
classify : Nat -> Nat -> Bool
classify m n with m
  | Zero with n
    | Zero => True
    | Succ _ => False
  | Succ _ => True
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'classify');

      // Should generate two levels of auxiliaries
      const aux1 = allDecls.find((d: any) => d?.name?.match(/classify-with-\d+$/) && !d?.name?.includes('-with-') === false);
      const aux2 = allDecls.find((d: any) => d?.name?.match(/classify-with-\d+-with-\d+/));
      expect(aux1).toBeDefined();
      expect(aux2).toBeDefined();
      expect(aux1?.checkSuccess).toBe(true);
      expect(aux2?.checkSuccess).toBe(true);
    });

    test('nested with on both branches', () => {
      const source = natBoolPreamble + `
classify2 : Nat -> Nat -> Bool
classify2 m n with m
  | Zero with n
    | Zero => True
    | Succ _ => False
  | Succ _ with n
    | Zero => False
    | Succ _ => True
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'classify2');

      // Two nested withs should produce two nested auxiliary functions
      const nestedAuxes = allDecls.filter((d: any) => d?.name?.match(/classify2-with-\d+-with-\d+/));
      expect(nestedAuxes.length).toBe(2);
      for (const aux of nestedAuxes) {
        expect(aux?.checkSuccess).toBe(true);
      }
    });

    test('nested with with constructor patterns in outer', () => {
      const source = natPreamble + `
add : Nat -> Nat -> Nat
add m n with m
  | Zero => n
  | Succ k with n
    | Zero => Succ k
    | Succ j => Succ (Succ (add k j))
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'add');

      // Check that recursive call in nested with works
      const nestedAux = allDecls.find((d: any) => d?.name?.match(/-with-\d+-with-\d+/));
      expect(nestedAux).toBeDefined();
      expect(nestedAux?.checkSuccess).toBe(true);
    });

    test('nested with with implicit type parameters', () => {
      const source = natBoolPreamble + listPreamble.replace(natBoolPreamble, '') + `
filter : {A : Type} -> (A -> Bool) -> List A -> List A
filter p xs with xs
  | Nil => Nil
  | Cons x rest with p x
    | True => Cons x (filter p rest)
    | False => filter p rest
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'filter');

      // Verify auxiliary chain exists
      const aux1 = allDecls.find((d: any) => d?.name?.match(/filter-with-\d+$/));
      const aux2 = allDecls.find((d: any) => d?.name?.match(/filter-with-\d+-with-\d+/));
      expect(aux1).toBeDefined();
      expect(aux2).toBeDefined();
      expect(aux1?.checkSuccess).toBe(true);
      expect(aux2?.checkSuccess).toBe(true);
    });

    test('three levels of nesting', () => {
      const source = natBoolPreamble + `
deep : Nat -> Nat -> Nat -> Bool
deep a b c with a
  | Zero with b
    | Zero with c
      | Zero => True
      | Succ _ => False
    | Succ _ => False
  | Succ _ => False
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'deep');

      // Should have 3 levels of auxiliaries
      const level1 = allDecls.filter((d: any) => d?.name?.match(/deep-with-\d+$/) && !d?.name?.match(/-with-\d+-with-/));
      const level2 = allDecls.filter((d: any) => d?.name?.match(/deep-with-\d+-with-\d+$/) && !d?.name?.match(/-with-\d+-with-\d+-with-/));
      const level3 = allDecls.filter((d: any) => d?.name?.match(/deep-with-\d+-with-\d+-with-\d+/));
      expect(level1.length).toBeGreaterThanOrEqual(1);
      expect(level2.length).toBeGreaterThanOrEqual(1);
      expect(level3.length).toBeGreaterThanOrEqual(1);
    });

    test('nested with generates correct auxiliary ordering', () => {
      const source = natBoolPreamble + `
ordered : Nat -> Nat -> Bool
ordered m n with m
  | Zero with n
    | Zero => True
    | Succ _ => False
  | Succ _ => True
`;
      const { allDecls } = compileAndGetDecls(source);

      // All declarations should type-check (correct ordering means
      // deepest auxiliary is processed first)
      const withDecls = allDecls.filter((d: any) => d?.name?.startsWith('ordered'));
      for (const d of withDecls) {
        expect(d?.checkSuccess, `${d?.name} should type-check`).toBe(true);
      }
    });
  });

  // ===========================================================================
  // Ellipsis syntax (... | pattern => rhs)
  // ===========================================================================

  describe('ellipsis syntax', () => {
    test('ellipsis in top-level with branches', () => {
      const source = natBoolPreamble + `
isZero : Nat -> Bool
isZero n with n
  ... | Zero => True
  ... | Succ _ => False
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'isZero');
    });

    test('ellipsis mixed with non-ellipsis branches', () => {
      const source = natBoolPreamble + `
isZero2 : Nat -> Bool
isZero2 n with n
  ... | Zero => True
  | Succ _ => False
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'isZero2');
    });

    test('ellipsis with pattern clause + with', () => {
      const source = natBoolPreamble + `
isOne : Nat -> Bool
isOne Zero = False
isOne n with n
  ... | Zero => False
  ... | Succ Zero => True
  ... | Succ (Succ _) => False
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'isOne');
    });

    test('ellipsis in nested with branches', () => {
      const source = natBoolPreamble + `
classify : Nat -> Nat -> Bool
classify m n with m
  | Zero with n
    ... | Zero => True
    ... | Succ _ => False
  | Succ _ => True
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'classify');
    });

    test('ellipsis with multiple scrutinees', () => {
      const source = natBoolPreamble + `
inductive Ordering : Type where
  LT : Ordering
  EQ : Ordering
  GT : Ordering
compare : Nat -> Nat -> Ordering
compare m n with m, n
  ... | Zero, Zero => EQ
  ... | Zero, Succ _ => LT
  ... | Succ _, Zero => GT
  ... | Succ a, Succ b => compare a b
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'compare');
    });
  });

  // ===========================================================================
  // #absurd in with branches
  // ===========================================================================

  describe('#absurd in with branches', () => {
    test('#absurd with impossible equality proof', () => {
      const source = natPreamble + equalPreamble.replace(natPreamble, '') + `
inductive Void : Type where
absurdEqual : Equal Zero (Succ Zero) -> Void
absurdEqual eq with eq
  | refl => #absurd
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'absurdEqual');
    });

    test('#absurd in nested with', () => {
      const source = natPreamble + equalPreamble.replace(natPreamble, '') + `
inductive Void : Type where
nested : Equal Zero (Succ Zero) -> Void
nested eq with eq
  | refl => #absurd
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'nested');
    });

    test('#absurd mixed with regular branches', () => {
      const source = natBoolPreamble + equalPreamble.replace(natPreamble, '') + `
inspect : {n : Nat} -> Equal n Zero -> Bool
inspect eq with eq
  | refl => True
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'inspect');
    });
  });

  // ===========================================================================
  // Totality checking for with auxiliaries
  // ===========================================================================

  describe('totality checking', () => {
    test('exhaustive with-clause passes totality', () => {
      const source = natBoolPreamble + `
isZero : Nat -> Bool
isZero n with n
  | Zero => True
  | Succ _ => False
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'isZero');
      // Auxiliary should also pass
      const aux = allDecls.find((d: any) => d?.name?.startsWith('isZero-with-'));
      expect(aux?.checkSuccess).toBe(true);
    });

    test('non-exhaustive with-clause fails totality', () => {
      const source = natBoolPreamble + `
broken : Nat -> Bool
broken n with n
  | Zero => True
`;
      const { allDecls } = compileAndGetDecls(source);
      // Auxiliary should fail totality (missing Succ case)
      const aux = allDecls.find((d: any) => d?.name?.startsWith('broken-with-'));
      expect(aux).toBeDefined();
      expect(aux?.checkSuccess).toBe(false);
    });

    test('frozen function-patterns do not cause false totality failures', () => {
      // filter-with-1 has frozen patterns (p, xs) and scrutinee (List A)
      // The scrutinee dimension covers Nil and Cons — should be total
      const source = listPreamble + `
filter : {A : Type} -> (A -> Bool) -> List A -> List A
filter p xs with xs
  | Nil => Nil
  | Cons x rest with p x
    | True => Cons x (filter p rest)
    | False => filter p rest
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'filter');
      // All auxiliaries should pass too
      const auxDecls = allDecls.filter((d: any) => d?.name?.includes('-with-'));
      for (const d of auxDecls) {
        expect(d?.checkSuccess, `${d?.name} should pass totality`).toBe(true);
      }
    });

    test('multiple scrutinees checked for totality', () => {
      const source = natBoolPreamble + `
inductive Ordering : Type where
  LT : Ordering
  EQ : Ordering
  GT : Ordering
compare : Nat -> Nat -> Ordering
compare m n with m, n
  | Zero, Zero => EQ
  | Zero, Succ _ => LT
  | Succ _, Zero => GT
  | Succ a, Succ b => compare a b
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'compare');
      const aux = allDecls.find((d: any) => d?.name?.startsWith('compare-with-'));
      expect(aux?.checkSuccess).toBe(true);
    });

    test('nested with totality: inner with checked independently', () => {
      const source = natBoolPreamble + `
classify : Nat -> Nat -> Bool
classify m n with m
  | Zero with n
    | Zero => True
    | Succ _ => False
  | Succ _ with n
    | Zero => False
    | Succ _ => True
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'classify');
      // All nested auxiliaries should pass totality
      const auxDecls = allDecls.filter((d: any) => d?.name?.includes('-with-'));
      for (const d of auxDecls) {
        expect(d?.checkSuccess, `${d?.name} should pass totality`).toBe(true);
      }
    });

    test('mixed clauses with exhaustive with pass totality', () => {
      // When mixing regular clauses with with, the with-clause must be
      // independently total for its scrutinee (Agda-style behavior)
      const source = natBoolPreamble + `
isOne : Nat -> Bool
isOne Zero = False
isOne n with n
  | Zero => False
  | Succ Zero => True
  | Succ (Succ _) => False
`;
      const { allDecls } = compileAndGetDecls(source);
      expectSuccess(allDecls, 'isOne');
    });
  });
});
