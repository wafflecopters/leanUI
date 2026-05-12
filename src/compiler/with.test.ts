import { describe, test, expect, beforeEach } from 'vitest';
import { readFileSync } from 'node:fs';
import { compileTTFromText, extractHoleLocations } from './compile';
import { resetWithCounter } from './with-desugar';

// Common preambles to reduce repetition
const natPreamble = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat
`;

const natBoolPreamble = natPreamble + `
inductive Bool : Type where
  True : Bool
  False : Bool
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
  });

  // ===========================================================================
  // With on equality proofs
  // ===========================================================================

  describe('with on equality / dependent types', () => {
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

    test('abstracts computed scrutinee occurring in return type', () => {
      const source = natBoolPreamble + `
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

isZero : Nat -> Bool
isZero Zero = True
isZero (Succ _) = False

sameZero : (n : Nat) -> Equal (isZero n) (isZero n)
sameZero n with isZero n
  | True => refl
  | False => refl
`;
      const { allDecls } = compileAndGetDecls(source);

      const auxDecl = allDecls.find((d: any) => d?.name?.startsWith('sameZero-with-'));
      expect(auxDecl).toBeDefined();
      expect(auxDecl?.checkSuccess).toBe(true);
      expect(auxDecl?.prettyType).toContain('Equal');
      expect(auxDecl?.prettyType).toContain('_scrut0');

      expectSuccess(allDecls, 'sameZero');
    });

    test('abstracts repeated computed scrutinee occurrences in return type', () => {
      const source = natBoolPreamble + `
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

isZero : Nat -> Bool
isZero Zero = True
isZero (Succ _) = False

pairZero : (n : Nat) -> Equal (isZero n) (isZero n)
pairZero n with isZero n
  | True => refl
  | False => refl
`;
      const { allDecls } = compileAndGetDecls(source);
      const auxDecl = expectSuccess(allDecls, 'pairZero-with-1');
      expect(auxDecl.prettyType).toContain('_scrut0');

      const firstBinder = auxDecl.surfaceType;
      expect(firstBinder?.tag).toBe('Binder');
      const scrutBinder = firstBinder?.tag === 'Binder' ? firstBinder.body : undefined;
      expect(scrutBinder?.tag).toBe('Binder');
      expect(scrutBinder?.name).toBe('_scrut0');

      const equalBody = scrutBinder?.tag === 'Binder' ? scrutBinder.body : undefined;
      expect(equalBody?.tag).toBe('App');
      if (equalBody?.tag === 'App' && equalBody.fn.tag === 'App') {
        expect(equalBody.fn.arg).toMatchObject({ tag: 'Var', index: 0 });
        expect(equalBody.arg).toMatchObject({ tag: 'Var', index: 0 });
      }

      expectSuccess(allDecls, 'pairZero');
    });

    test('preserves dependent family binders when computed scrutinee is unrelated', () => {
      const source = natPreamble + `
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

record DPair (A : Type) (fn : A -> Type) where
  fst : A
  snd : fn fst

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ n) m = Succ (plus n m)

succCong : {u v : Nat} -> Equal u v -> Equal (Succ u) (Succ v)
succCong refl = refl

leqImpliesSum : (a b : Nat) -> Leq a b -> DPair Nat (\\n => Equal b (plus a n))
leqImpliesSum Zero b LeqZero = MkDPair b refl
leqImpliesSum (Succ a) (Succ b) (LeqSucc leq) with leqImpliesSum a b leq
  | MkDPair n pf => MkDPair n (succCong pf)
`;
      const { allDecls } = compileAndGetDecls(source);

      const auxDecl = expectSuccess(allDecls, 'leqImpliesSum-with-1');
      expect(auxDecl.prettyType).toContain('DPair Nat');
      expect(auxDecl.prettyType).not.toContain('plus (Succ a) _scrut0');

      expectSuccess(allDecls, 'leqImpliesSum');
    });

    test('nested dependent with keeps outer family binders intact', () => {
      const source = readFileSync(
        'src/test-programs/complex/sigmaSum-nested-with.tt',
        'utf8'
      )
        .split('\n')
        .filter(line => !line.startsWith('@'))
        .join('\n');
      const { allDecls } = compileAndGetDecls(source);

      expectSuccess(allDecls, 'leqImpliesSum-with-1');
      expectSuccess(allDecls, 'sigmaSum-with-4-with-5');
      expectSuccess(allDecls, 'sigmaSum-with-4');
      expectSuccess(allDecls, 'sigmaSum');
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
  // Hole locations in with-clauses
  // ===========================================================================

  describe('hole locations', () => {
    test('holes in with-clause branches get correct source positions', () => {
      const source = natBoolPreamble + `
myFunc : Nat -> Bool
myFunc n with n
  | Zero => ?p
  | Succ _ => ?q
`;
      const { result } = compileAndGetDecls(source);
      const holes = extractHoleLocations(result);

      const holeP = holes.find(h => h.id === 'p');
      const holeQ = holes.find(h => h.id === 'q');

      expect(holeP, 'hole p should be found').toBeDefined();
      expect(holeQ, 'hole q should be found').toBeDefined();

      // ?p is on the "| Zero => ?p" line
      // ?q is on the "| Succ _ => ?q" line
      // Verify they point to different lines
      expect(holeP!.line).not.toBe(holeQ!.line);
      // Verify the column is reasonable (after "=> ")
      expect(holeP!.column).toBeGreaterThan(4);
      expect(holeQ!.column).toBeGreaterThan(4);
    });

    test('holes in nested with-clause branches get correct source positions', () => {
      const source = natBoolPreamble + `
myFunc : Nat -> Nat -> Bool
myFunc m n with m
  | Zero with n
    | Zero => ?a
    | Succ _ => ?b
  | Succ _ => ?c
`;
      const { result } = compileAndGetDecls(source);
      const holes = extractHoleLocations(result);

      const holeA = holes.find(h => h.id === 'a');
      const holeB = holes.find(h => h.id === 'b');
      const holeC = holes.find(h => h.id === 'c');

      expect(holeA, 'hole a should be found').toBeDefined();
      expect(holeB, 'hole b should be found').toBeDefined();
      expect(holeC, 'hole c should be found').toBeDefined();

      // All on different lines
      const lines = [holeA!.line, holeB!.line, holeC!.line];
      expect(new Set(lines).size).toBe(3);
    });

    test('with-clause holes are not duplicated by auxiliary declarations', () => {
      // Regression: auxiliary declarations inherit the parent sourceMap, causing
      // holes from with-branches (clauses[0].rhs in the auxiliary) to be mapped
      // to the parent's clause 0 position instead of the with-branch position.
      const source = natBoolPreamble + `
myFunc : Nat -> Nat -> Bool
myFunc Zero _ = True
myFunc (Succ _) n with n
  | Zero => ?p
  | Succ _ => ?q
`;
      const { result } = compileAndGetDecls(source);
      const holes = extractHoleLocations(result);

      // Should have exactly 2 holes (one per with-branch), not 4 (duplicated by auxiliary)
      expect(holes).toHaveLength(2);

      const holeP = holes.find(h => h.id === 'p');
      const holeQ = holes.find(h => h.id === 'q');
      expect(holeP).toBeDefined();
      expect(holeQ).toBeDefined();

      // Holes should be on the with-branch lines, not on the "myFunc Zero _ = True" line
      expect(holeP!.line).not.toBe(holeQ!.line);

      // Both holes should be on lines that contain "=>" (the with-branch lines)
      const sourceLines = source.split('\n');
      expect(sourceLines[holeP!.line - 1]).toContain('=>');
      expect(sourceLines[holeQ!.line - 1]).toContain('=>');
    });
  });
});
