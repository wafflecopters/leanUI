import { describe, test, expect } from 'vitest';
import { compileSource } from '../test-utils';
import {
  findPathAtCursor,
  findPathForSelection,
  buildReverseElabMap,
  findKernelPathForSurface,
  getTypeAtCursor,
  getTypeAtSelection,
  TypeInfoMap,
} from './type-info';
import { SourceMap, ElabMap } from '../types/source-position';
import { prettyPrint } from './kernel';

// ============================================================================
// Layer 1: TypeInfoMap collection during type checking
// ============================================================================

describe('TypeInfoMap collection', () => {
  test('simple term definition collects type info entries', () => {
    const source = `
id : {A : Type} -> A -> A
id a = a
`;
    const results = compileSource(source);
    const idBlock = results.find(r => r.name === 'id');
    expect(idBlock).toBeDefined();
    expect(idBlock!.checkSuccess).toBe(true);

    const decl = idBlock!.declarations[0];
    expect(decl.typeInfoMap).toBeDefined();
    expect(decl.typeInfoMap!.size).toBeGreaterThan(0);
  });

  test('inductive type definition collects type info entries', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat
`;
    const results = compileSource(source);
    const natBlock = results.find(r => r.name === 'Nat');
    expect(natBlock).toBeDefined();
    expect(natBlock!.checkSuccess).toBe(true);

    const decl = natBlock!.declarations[0];
    expect(decl.typeInfoMap).toBeDefined();
    expect(decl.typeInfoMap!.size).toBeGreaterThan(0);
  });

  test('type info entries have correct structure', () => {
    const source = `
id : {A : Type} -> A -> A
id a = a
`;
    const results = compileSource(source);
    const decl = results.find(r => r.name === 'id')!.declarations[0];
    const typeInfoMap = decl.typeInfoMap!;

    for (const [key, entry] of typeInfoMap) {
      // Every entry should have type, context, and kernelPath
      expect(entry.type).toBeDefined();
      expect(entry.context).toBeDefined();
      expect(Array.isArray(entry.context)).toBe(true);
      expect(entry.kernelPath).toBe(key);
    }
  });

  test('type info captures context (variables in scope)', () => {
    const source = `
const : {A B : Type} -> A -> B -> A
const a b = a
`;
    const results = compileSource(source);
    const decl = results.find(r => r.name === 'const')!.declarations[0];
    const typeInfoMap = decl.typeInfoMap!;

    // Find an entry with non-empty context (i.e., inside the function body)
    const entriesWithContext = [...typeInfoMap.values()].filter(e => e.context.length > 0);
    expect(entriesWithContext.length).toBeGreaterThan(0);
  });

  test('checking mode records expectedType', () => {
    const source = `
id : {A : Type} -> A -> A
id a = a
`;
    const results = compileSource(source);
    const decl = results.find(r => r.name === 'id')!.declarations[0];
    const typeInfoMap = decl.typeInfoMap!;

    // Some entries should have expectedType set (those checked against an expected type)
    const entriesWithExpected = [...typeInfoMap.values()].filter(e => e.expectedType !== undefined);
    expect(entriesWithExpected.length).toBeGreaterThan(0);
  });
});

// ============================================================================
// Layer 2: Cursor-to-path functions (unit tests with synthetic data)
// ============================================================================

describe('findPathAtCursor', () => {
  test('finds the smallest span containing cursor', () => {
    const sourceMap: SourceMap = new Map([
      ['root', { start: { pos: 0, line: 1, col: 0 }, end: { pos: 20, line: 1, col: 20 } }],
      ['root.body', { start: { pos: 5, line: 1, col: 5 }, end: { pos: 15, line: 1, col: 15 } }],
      ['root.body.inner', { start: { pos: 8, line: 1, col: 8 }, end: { pos: 12, line: 1, col: 12 } }],
    ]);

    // Cursor at position 10 — inside all three, but root.body.inner is smallest
    expect(findPathAtCursor(10, sourceMap)).toBe('root.body.inner');
  });

  test('returns undefined for cursor outside all ranges', () => {
    const sourceMap: SourceMap = new Map([
      ['a', { start: { pos: 0, line: 1, col: 0 }, end: { pos: 5, line: 1, col: 5 } }],
    ]);

    expect(findPathAtCursor(10, sourceMap)).toBeUndefined();
  });

  test('cursor at start of range is included', () => {
    const sourceMap: SourceMap = new Map([
      ['a', { start: { pos: 5, line: 1, col: 5 }, end: { pos: 10, line: 1, col: 10 } }],
    ]);

    expect(findPathAtCursor(5, sourceMap)).toBe('a');
  });

  test('cursor at end of range is excluded', () => {
    const sourceMap: SourceMap = new Map([
      ['a', { start: { pos: 5, line: 1, col: 5 }, end: { pos: 10, line: 1, col: 10 } }],
    ]);

    expect(findPathAtCursor(10, sourceMap)).toBeUndefined();
  });
});

describe('findPathForSelection', () => {
  test('finds smallest range fully containing the selection', () => {
    const sourceMap: SourceMap = new Map([
      ['root', { start: { pos: 0, line: 1, col: 0 }, end: { pos: 20, line: 1, col: 20 } }],
      ['root.body', { start: { pos: 5, line: 1, col: 5 }, end: { pos: 15, line: 1, col: 15 } }],
    ]);

    // Selection [6, 14] — fits inside root.body (5-15) but not a smaller range
    expect(findPathForSelection(6, 14, sourceMap)).toBe('root.body');
  });

  test('selection containing an entry matches the closest-span entry', () => {
    const sourceMap: SourceMap = new Map([
      ['inner', { start: { pos: 5, line: 1, col: 5 }, end: { pos: 10, line: 1, col: 10 } }],
    ]);

    // Selection [4, 11] includes extra chars (e.g. parens) around inner [5, 10]
    // inner's span (5) is closest to selection span (7), so it matches
    expect(findPathForSelection(4, 11, sourceMap)).toBe('inner');
  });

  test('selection picks entry with span closest to selection span', () => {
    const sourceMap: SourceMap = new Map([
      ['outer', { start: { pos: 0, line: 1, col: 0 }, end: { pos: 20, line: 1, col: 20 } }],
      ['inner', { start: { pos: 5, line: 1, col: 5 }, end: { pos: 12, line: 1, col: 12 } }],
    ]);

    // Selection [4, 13] wraps inner [5, 12] with extra chars (e.g. parens)
    // inner span=7 vs selection span=9: distance=2
    // outer span=20 vs selection span=9: distance=11
    // inner wins
    expect(findPathForSelection(4, 13, sourceMap)).toBe('inner');
  });

  test('no match when selection does not overlap any entry', () => {
    const sourceMap: SourceMap = new Map([
      ['a', { start: { pos: 0, line: 1, col: 0 }, end: { pos: 5, line: 1, col: 5 } }],
    ]);

    // Selection is entirely outside the entry
    expect(findPathForSelection(10, 15, sourceMap)).toBeUndefined();
  });

  test('partial-token selection snaps to containing expression', () => {
    // Simulates: "plus a b" where user selects "s a" (mid-token in "plus" to "a")
    // plus: [0, 4], a: [5, 6], plus_a: [0, 6], plus_a_b: [0, 8], b: [7, 8]
    const sourceMap: SourceMap = new Map([
      ['app',     { start: { pos: 0, line: 1, col: 1 }, end: { pos: 8, line: 1, col: 9 } }],  // plus a b
      ['app.fn',  { start: { pos: 0, line: 1, col: 1 }, end: { pos: 6, line: 1, col: 7 } }],  // plus a
      ['app.fn.fn', { start: { pos: 0, line: 1, col: 1 }, end: { pos: 4, line: 1, col: 5 } }], // plus
      ['app.fn.arg', { start: { pos: 5, line: 1, col: 6 }, end: { pos: 6, line: 1, col: 7 } }], // a
      ['app.arg', { start: { pos: 7, line: 1, col: 8 }, end: { pos: 8, line: 1, col: 9 } }],  // b
    ]);

    // Selection "s a" = [3, 6]: starts mid-token in "plus", ends at end of "a"
    // "app.fn" [0,6] contains the selection and is smallest containing → wins
    expect(findPathForSelection(3, 6, sourceMap)).toBe('app.fn');
  });

  test('cross-subexpression selection resolves to containing expression', () => {
    // Simulates: "plus a b" where user selects "a b"
    const sourceMap: SourceMap = new Map([
      ['app',     { start: { pos: 0, line: 1, col: 1 }, end: { pos: 8, line: 1, col: 9 } }],  // plus a b
      ['app.fn',  { start: { pos: 0, line: 1, col: 1 }, end: { pos: 6, line: 1, col: 7 } }],  // plus a
      ['app.fn.fn', { start: { pos: 0, line: 1, col: 1 }, end: { pos: 4, line: 1, col: 5 } }], // plus
      ['app.fn.arg', { start: { pos: 5, line: 1, col: 6 }, end: { pos: 6, line: 1, col: 7 } }], // a
      ['app.arg', { start: { pos: 7, line: 1, col: 8 }, end: { pos: 8, line: 1, col: 9 } }],  // b
    ]);

    // Selection "a b" = [5, 8]: spans across two sub-expressions
    // Only "app" [0,8] fully contains the selection
    expect(findPathForSelection(5, 8, sourceMap)).toBe('app');
  });

  test('small fragment in selection does not win over containing entry', () => {
    // Simulates: selecting "a b" but "a" (span 1) is much smaller than selection (span 3)
    const sourceMap: SourceMap = new Map([
      ['whole',  { start: { pos: 0, line: 1, col: 1 }, end: { pos: 10, line: 1, col: 11 } }],
      ['small',  { start: { pos: 5, line: 1, col: 6 }, end: { pos: 6, line: 1, col: 7 } }],
    ]);

    // Selection [4, 8]: "small" [5,6] is contained by selection but covers only 25%
    // "whole" [0,10] contains the selection
    // "whole" should win because "small" is too small a fragment
    expect(findPathForSelection(4, 8, sourceMap)).toBe('whole');
  });
});

// ============================================================================
// Reverse ElabMap
// ============================================================================

describe('buildReverseElabMap', () => {
  test('reverses kernel→surface to surface→kernel', () => {
    const elabMap: ElabMap = new Map([
      ['body.domain', 'type.body.domain'],
      ['body.body', 'type.body.body'],
    ]);

    const reverse = buildReverseElabMap(elabMap);
    expect(reverse.get('type.body.domain')).toBe('body.domain');
    expect(reverse.get('type.body.body')).toBe('body.body');
  });
});

describe('findKernelPathForSurface', () => {
  test('exact match returns kernel path', () => {
    const reverse = new Map([
      ['type.body', 'body'],
    ]);
    expect(findKernelPathForSurface('type.body', reverse)).toBe('body');
  });

  test('walks up path hierarchy when no exact match, appending suffix', () => {
    const reverse = new Map([
      ['type', 'root'],
    ]);
    // No exact match for 'type.body.domain', but 'type' matches with suffix '.body.domain'
    expect(findKernelPathForSurface('type.body.domain', reverse)).toBe('root.body.domain');
  });

  test('returns root mapping as fallback', () => {
    const reverse = new Map([
      ['', 'root'],
    ]);
    expect(findKernelPathForSurface('something.deep', reverse)).toBe('root');
  });
});

// ============================================================================
// Integration: Full type-at-cursor flow
// ============================================================================

describe('getTypeAtCursor integration', () => {
  test('returns type info for a compiled declaration', () => {
    const source = `
id : {A : Type} -> A -> A
id a = a
`;
    const results = compileSource(source);
    const decl = results.find(r => r.name === 'id')!.declarations[0];

    // We need sourceMap and typeInfoMap to query
    expect(decl.sourceMap).toBeDefined();
    expect(decl.typeInfoMap).toBeDefined();

    if (decl.sourceMap && decl.typeInfoMap) {
      // Try to get type info at each position in the sourceMap
      let found = false;
      for (const [, range] of decl.sourceMap) {
        const result = getTypeAtCursor(
          range.start.pos,
          decl.sourceMap,
          decl.elabMap,
          decl.typeInfoMap,
        );
        if (result) {
          found = true;
          expect(result.prettyType).toBeDefined();
          expect(typeof result.prettyType).toBe('string');
          expect(result.context).toBeDefined();
          expect(Array.isArray(result.context)).toBe(true);
          break;
        }
      }
      expect(found).toBe(true);
    }
  });
});

// ============================================================================
// Pattern type info collection
// ============================================================================

describe('Pattern type info', () => {
  test('pattern variables have type info entries', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)
`;
    const results = compileSource(source);
    const plusBlock = results.find(r => r.name === 'plus');
    expect(plusBlock).toBeDefined();
    expect(plusBlock!.checkSuccess).toBe(true);

    const decl = plusBlock!.declarations[0];
    expect(decl.typeInfoMap).toBeDefined();
    expect(decl.sourceMap).toBeDefined();

    if (decl.sourceMap && decl.typeInfoMap) {
      // Find source positions for pattern variables
      // The source map should have entries for pattern elements
      // Look for entries that have type info (pattern vars and constructor patterns)
      let foundPatternTypeInfo = false;
      for (const [surfacePath, range] of decl.sourceMap) {
        // Look for paths that are in a clause's patterns section
        if (surfacePath.includes('patterns')) {
          const result = getTypeAtCursor(
            range.start.pos,
            decl.sourceMap,
            decl.elabMap,
            decl.typeInfoMap,
          );
          if (result) {
            foundPatternTypeInfo = true;
            expect(result.prettyType).toBeDefined();
            expect(typeof result.prettyType).toBe('string');
            break;
          }
        }
      }
      expect(foundPatternTypeInfo).toBe(true);
    }
  });

  test('constructor pattern Succ has type info (constructor type at name, matched type at pattern)', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)
`;
    const results = compileSource(source);
    const plusBlock = results.find(r => r.name === 'plus');
    const decl = plusBlock!.declarations[0];

    if (decl.sourceMap && decl.typeInfoMap) {
      // Cursor at start of "Succ a" lands on the constructor name (narrowest match),
      // which now shows the constructor's full type (Nat -> Nat)
      const succNameRange = decl.sourceMap.get('value.clauses[1].patterns[0].name');
      if (succNameRange) {
        const nameResult = getTypeAtCursor(
          succNameRange.start.pos,
          decl.sourceMap,
          decl.elabMap,
          decl.typeInfoMap,
        );
        expect(nameResult).toBeDefined();
        if (nameResult) {
          expect(nameResult.prettyType).toBe('(Nat -> Nat)');
        }
      }

      // Selecting the whole "(Succ a)" pattern shows the matched type Nat
      const patRange = decl.sourceMap.get('value.clauses[1].patterns[0]');
      if (patRange) {
        const selResult = getTypeAtSelection(
          patRange.start.pos,
          patRange.end.pos,
          decl.sourceMap,
          decl.elabMap,
          decl.typeInfoMap,
        );
        expect(selResult).toBeDefined();
        if (selResult) {
          expect(selResult.prettyType).toBe('Nat');
        }
      }
    }
  });

  test('pattern variable a in (Succ a) has type Nat', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)
`;
    const results = compileSource(source);
    const plusBlock = results.find(r => r.name === 'plus');
    const decl = plusBlock!.declarations[0];

    if (decl.sourceMap && decl.typeInfoMap) {
      // Look for the variable "a" in clause 1, pattern 0, args[0]
      for (const [surfacePath, range] of decl.sourceMap) {
        if (surfacePath.includes('clauses[1].patterns[0]') &&
            surfacePath.includes('args[0]') &&
            !surfacePath.includes('.name')) {
          const result = getTypeAtCursor(
            range.start.pos,
            decl.sourceMap,
            decl.elabMap,
            decl.typeInfoMap,
          );
          if (result) {
            // a : Nat (Succ takes Nat -> Nat, so the argument is Nat)
            expect(result.prettyType).toBe('Nat');
            break;
          }
        }
      }
    }
  });
});

// ============================================================================
// Selection type info for application domains in arrow types
// ============================================================================

describe('Application domain sourceMap entries', () => {
  test('selecting "Vec A n" in constructor type returns correct type', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Vec : Type -> Nat -> Type where
  VNil : {A: Type} -> Vec A Zero
  VCons : {A : Type} -> {n : Nat} -> A -> Vec A n -> Vec A (Succ n)
`;
    const results = compileSource(source);
    const vecBlock = results.find(r => r.name === 'Vec');
    expect(vecBlock).toBeDefined();
    expect(vecBlock!.checkSuccess).toBe(true);

    const decl = vecBlock!.declarations[0];
    expect(decl.sourceMap).toBeDefined();
    expect(decl.typeInfoMap).toBeDefined();

    if (decl.sourceMap && decl.typeInfoMap) {
      // The application "Vec A n" is broken into sub-paths in the sourceMap:
      //   .domain.fn.fn (Vec), .domain.fn.arg (A), .domain.arg (n), .domain.fn (Vec A)
      // Test the "Vec A" application which should have type (Nat -> Type)
      const domainFnPath = 'constructors[1].type.body.body.body.domain.fn';
      const domainFnRange = decl.sourceMap.get(domainFnPath);
      expect(domainFnRange).toBeDefined();

      if (domainFnRange) {
        const result = getTypeAtSelection(
          domainFnRange.start.pos,
          domainFnRange.end.pos,
          decl.sourceMap,
          decl.elabMap,
          decl.typeInfoMap,
        );
        expect(result).toBeDefined();
        expect(result!.prettyType).toBe('(Nat -> Type)');
        expect(result!.surfacePath).toBe(domainFnPath);
      }
    }
  });

  test('selecting "(Equal x y -> Void)" parenthesized arrow type returns Type', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

inductive Void : Type where

inductive DecEq : {A : Type} -> A -> A -> Type where
  Yes : {A : Type} -> {x y : A} -> Equal x y -> DecEq x y
  No : {A : Type} -> {x y : A} -> (Equal x y -> Void) -> DecEq x y
`;
    const results = compileSource(source);
    const decEqBlock = results.find(r => r.name === 'DecEq');
    expect(decEqBlock).toBeDefined();
    expect(decEqBlock!.checkSuccess).toBe(true);

    const decl = decEqBlock!.declarations[0];
    expect(decl.sourceMap).toBeDefined();
    expect(decl.typeInfoMap).toBeDefined();

    if (decl.sourceMap && decl.typeInfoMap) {
      // The sourceMap should have an entry for "(Equal x y -> Void)" including parens
      const domainPath = 'constructors[1].type.body.body.domain';
      const domainRange = decl.sourceMap.get(domainPath);
      expect(domainRange).toBeDefined();

      if (domainRange) {
        const result = getTypeAtSelection(
          domainRange.start.pos,
          domainRange.end.pos,
          decl.sourceMap,
          decl.elabMap,
          decl.typeInfoMap,
        );
        expect(result).toBeDefined();
        expect(result!.prettyType).toBe('Type');
      }
    }
  });
});

// ============================================================================
// With-clause type info
// ============================================================================

describe('With-clause type info', () => {
  const withSource = `
inductive Bool : Type where
  True : Bool
  False : Bool

inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive List : Type -> Type where
  Nil : {A : Type} -> List A
  Cons : {A : Type} -> A -> List A -> List A

filter : {A : Type} -> (A -> Bool) -> List A -> List A
filter f Nil = Nil
filter f (Cons x xs) with f x
  | True => Cons x (filter f xs)
  | False => filter f xs
`;

  function getFilterAuxDecl() {
    const results = compileSource(withSource);
    // Block name is the auxiliary (e.g. filter-with-N), find by declarations containing 'filter'
    const filterBlock = results.find(r =>
      r.declarations.some(d => d.name === 'filter')
    );
    expect(filterBlock).toBeDefined();
    const auxDecl = filterBlock!.declarations.find(d => d.name !== 'filter' && d.name?.includes('filter'));
    expect(auxDecl).toBeDefined();
    expect(auxDecl!.sourceMap).toBeDefined();
    expect(auxDecl!.typeInfoMap).toBeDefined();
    return auxDecl!;
  }

  test('with-clause pattern True has type info (Bool)', () => {
    const auxDecl = getFilterAuxDecl();

    if (auxDecl.sourceMap && auxDecl.typeInfoMap) {
      // Look for the True with-pattern in the sourceMap
      const truePatternPath = 'value.clauses[1].withClauses[0].patterns[0]';
      const trueRange = auxDecl.sourceMap.get(truePatternPath);
      expect(trueRange).toBeDefined();

      if (trueRange) {
        const result = getTypeAtCursor(
          trueRange.start.pos,
          auxDecl.sourceMap,
          auxDecl.elabMap,
          auxDecl.typeInfoMap,
        );
        expect(result).toBeDefined();
        expect(result!.prettyType).toBe('Bool');
      }
    }
  });

  test('with-clause RHS has type info', () => {
    const auxDecl = getFilterAuxDecl();

    if (auxDecl.sourceMap && auxDecl.typeInfoMap) {
      // Look for the RHS of the True branch (Cons x (filter f xs))
      const rhsPath = 'value.clauses[1].withClauses[0].rhs';
      const rhsRange = auxDecl.sourceMap.get(rhsPath);
      expect(rhsRange).toBeDefined();

      if (rhsRange) {
        const result = getTypeAtSelection(
          rhsRange.start.pos,
          rhsRange.end.pos,
          auxDecl.sourceMap,
          auxDecl.elabMap,
          auxDecl.typeInfoMap,
        );
        expect(result).toBeDefined();
        expect(result!.prettyType).toBeDefined();
      }
    }
  });

  test('selecting "a b" in "plus a b" RHS resolves to full application', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)
`;
    const results = compileSource(source);
    const plusBlock = results.find(r => r.name === 'plus');
    expect(plusBlock).toBeDefined();
    const decl = plusBlock!.declarations[0];
    expect(decl.sourceMap).toBeDefined();
    expect(decl.typeInfoMap).toBeDefined();

    if (decl.sourceMap && decl.typeInfoMap) {
      // The RHS "Succ (plus a b)" — find the "plus a b" application's sourceMap range
      // "plus a b" = rhs.arg (argument to Succ), and the first arg "a" is at rhs.arg.fn.arg
      const argAPath = 'value.clauses[1].rhs.arg.fn.arg';
      const argBPath = 'value.clauses[1].rhs.arg.arg';
      const argARange = decl.sourceMap.get(argAPath);
      const argBRange = decl.sourceMap.get(argBPath);

      // If we can find both "a" and "b" ranges, select from start of "a" to end of "b"
      if (argARange && argBRange) {
        const result = getTypeAtSelection(
          argARange.start.pos,
          argBRange.end.pos,
          decl.sourceMap,
          decl.elabMap,
          decl.typeInfoMap,
        );
        expect(result).toBeDefined();
        // "plus a b" has type Nat — the containing application
        expect(result!.prettyType).toBe('Nat');
        // Should resolve to the "plus a b" application, not just "a"
        expect(result!.surfacePath).toBe('value.clauses[1].rhs.arg');
      }
    }
  });

  test('with-clause scrutinee has type info', () => {
    const results = compileSource(withSource);
    const filterBlock = results.find(r =>
      r.declarations.some(d => d.name === 'filter')
    );
    expect(filterBlock).toBeDefined();
    const mainDecl = filterBlock!.declarations.find(d => d.name === 'filter');
    expect(mainDecl).toBeDefined();
    expect(mainDecl!.sourceMap).toBeDefined();
    expect(mainDecl!.typeInfoMap).toBeDefined();

    // The scrutinee "f x" is at value.clauses[1].scrutinee
    const scrutineePath = 'value.clauses[1].scrutinee';
    const scrutineeRange = mainDecl!.sourceMap!.get(scrutineePath);
    expect(scrutineeRange).toBeDefined();

    if (scrutineeRange) {
      // Full scrutinee "f x" via selection
      const result = getTypeAtSelection(
        scrutineeRange.start.pos,
        scrutineeRange.end.pos,
        mainDecl!.sourceMap!,
        mainDecl!.elabMap,
        mainDecl!.typeInfoMap,
      );
      expect(result).toBeDefined();
      expect(result!.prettyType).toBeDefined();
      expect(result!.surfacePath).toBe(scrutineePath);
    }

    // Check "f" in "with f x" via cursor
    const fPath = 'value.clauses[1].scrutinee.fn';
    const fRange = mainDecl!.sourceMap!.get(fPath);
    expect(fRange).toBeDefined();

    if (fRange) {
      const result = getTypeAtCursor(
        fRange.start.pos,
        mainDecl!.sourceMap!,
        mainDecl!.elabMap,
        mainDecl!.typeInfoMap,
      );
      expect(result).toBeDefined();
      expect(result!.surfacePath).toBe(fPath);
    }
  });
});

// ============================================================================
// Zonking: no unsolved metas in type info
// ============================================================================

describe('Type info zonking', () => {
  test('expectedType has no unsolved metas for implicit arguments', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Vec : Type -> Nat -> Type where
  VNil : {A: Type} -> Vec A Zero
  VCons : {A : Type} -> {n : Nat} -> A -> Vec A n -> Vec A (Succ n)

inductive Fin : Nat -> Type where
  FZero : {n : Nat} -> Fin (Succ n)
  FSucc : {n : Nat} -> Fin n -> Fin (Succ n)

nth : {A : Type} -> {n : Nat} -> Vec A n -> Fin n -> A
nth (VCons h _) FZero = h
nth (VCons h tail) (FSucc f) = nth tail f
`;
    const results = compileSource(source);
    const nthBlock = results.find(r => r.name === 'nth');
    expect(nthBlock).toBeDefined();
    expect(nthBlock!.checkSuccess).toBe(true);

    const decl = nthBlock!.declarations[0];
    expect(decl.sourceMap).toBeDefined();
    expect(decl.typeInfoMap).toBeDefined();

    if (decl.sourceMap && decl.typeInfoMap) {
      // Check all entries in clause 1 RHS — none should have unsolved metas
      for (const [surfacePath, range] of decl.sourceMap) {
        if (surfacePath.includes('clauses[1].rhs')) {
          const result = getTypeAtCursor(
            range.start.pos,
            decl.sourceMap,
            decl.elabMap,
            decl.typeInfoMap,
          );
          if (result) {
            expect(result.prettyType).not.toMatch(/\?_/);
            if (result.expectedType) {
              expect(result.expectedType).not.toMatch(/\?_/);
            }
          }
        }
      }
    }
  });

  test('type info for all entries has no unsolved metas', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)
`;
    const results = compileSource(source);
    const plusBlock = results.find(r => r.name === 'plus');
    const decl = plusBlock!.declarations[0];

    if (decl.typeInfoMap) {
      for (const [, entry] of decl.typeInfoMap) {
        const typePP = prettyPrint(entry.type, entry.context.map(c => c.name).reverse());
        expect(typePP).not.toMatch(/\?_/);
        if (entry.expectedType) {
          const expectedPP = prettyPrint(entry.expectedType, entry.context.map(c => c.name).reverse());
          expect(expectedPP).not.toMatch(/\?_/);
        }
      }
    }
  });

  test('no unsolved metas in map/apply style function', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive List : Type -> Type where
  Nil : {A : Type} -> List A
  Cons : {A : Type} -> A -> List A -> List A

map : {A B : Type} -> (A -> B) -> List A -> List B
map f Nil = Nil
map f (Cons x xs) = Cons (f x) (map f xs)
`;
    const results = compileSource(source);
    const mapBlock = results.find(r => r.name === 'map');
    expect(mapBlock).toBeDefined();
    expect(mapBlock!.checkSuccess).toBe(true);
    const decl = mapBlock!.declarations[0];

    if (decl.typeInfoMap) {
      for (const [path, entry] of decl.typeInfoMap) {
        const typePP = prettyPrint(entry.type, entry.context.map(c => c.name).reverse());
        expect(typePP).not.toMatch(/\?_/);
        if (entry.expectedType) {
          const expectedPP = prettyPrint(entry.expectedType, entry.context.map(c => c.name).reverse());
          expect(expectedPP).not.toMatch(/\?_/);
        }
      }
    }
  });

  test.todo('no unsolved metas with meta chains (lambda + sym + implicit args)', () => {
    // BLOCKED: _implicit12 is unsolved in clause 2 (Succ x Zero = No (\eq => ...)).
    // This is a meta/constraint solver issue — the implicit arg meta for `sym`
    // doesn't propagate through the lambda. Needs meta solver enhancement.
    // This tests meta chain propagation in the constraint solver.
    // The lambda body creates metas that chain through other metas (e.g., _10→_14→Succ _12),
    // and the CONV unification provides concrete values that should propagate through the chain.
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

inductive Void : Type where

inductive DecEq : Nat -> Nat -> Type where
  Yes : {m n : Nat} -> Equal m n -> DecEq m n
  No : {m n : Nat} -> (Equal m n -> Void) -> DecEq m n

sym : {A : Type} -> {x y : A} -> Equal x y -> Equal y x
sym refl = refl

zeroNeqSucc : {n : Nat} -> Equal Zero (Succ n) -> Void
zeroNeqSucc refl = #absurd

decEqNat : (x y : Nat) -> DecEq x y
decEqNat Zero Zero = Yes refl
decEqNat Zero (Succ y) = No zeroNeqSucc
decEqNat (Succ x) Zero = No (\\eq => zeroNeqSucc (sym eq))
decEqNat (Succ x) (Succ y) = Yes refl
`;
    const results = compileSource(source);
    const block = results.find(r => r.name === 'decEqNat');
    expect(block).toBeDefined();
    const decl = block!.declarations.find(d => d.name === 'decEqNat')!;

    if (decl.typeInfoMap) {
      for (const [, entry] of decl.typeInfoMap) {
        const typePP = prettyPrint(entry.type, entry.context.map(c => c.name).reverse());
        expect(typePP).not.toMatch(/\?_/);
        if (entry.expectedType) {
          const expectedPP = prettyPrint(entry.expectedType, entry.context.map(c => c.name).reverse());
          expect(expectedPP).not.toMatch(/\?_/);
        }
      }
    }
  });

  test('no unsolved metas in identity/const with implicit args', () => {
    const source = `
id : {A : Type} -> A -> A
id x = x

const : {A B : Type} -> A -> B -> A
const a _ = a
`;
    const results = compileSource(source);

    for (const block of results) {
      for (const decl of block.declarations) {
        if (decl.typeInfoMap) {
          for (const [, entry] of decl.typeInfoMap) {
            const typePP = prettyPrint(entry.type, entry.context.map(c => c.name).reverse());
            expect(typePP).not.toMatch(/\?_/);
          }
        }
      }
    }
  });
});

// ============================================================================
// APP type info: correct path and type for applications
// ============================================================================

describe('APP type info path correctness', () => {
  test('application records type at the correct path, not the arg path', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)
`;
    const results = compileSource(source);
    const plusBlock = results.find(r => r.name === 'plus');
    const decl = plusBlock!.declarations[0];
    expect(decl.typeInfoMap).toBeDefined();

    if (decl.typeInfoMap) {
      // "plus a" application should have type (Nat -> Nat)
      // Check that the APP path exists (not just the arg's path)
      const appPath = 'value.clauses[1].rhs.arg.fn';
      const appEntry = decl.typeInfoMap.get(appPath);
      expect(appEntry).toBeDefined();
      if (appEntry) {
        const names = appEntry.context.map(c => c.name).reverse();
        expect(prettyPrint(appEntry.type, names)).toBe('(Nat -> Nat)');
      }

      // "plus a b" should have type Nat
      const fullAppPath = 'value.clauses[1].rhs.arg';
      const fullAppEntry = decl.typeInfoMap.get(fullAppPath);
      expect(fullAppEntry).toBeDefined();
      if (fullAppEntry) {
        const names = fullAppEntry.context.map(c => c.name).reverse();
        expect(prettyPrint(fullAppEntry.type, names)).toBe('Nat');
      }
    }
  });

  test('Vec A application has type (Nat -> Type) in constructor', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Vec : Type -> Nat -> Type where
  VNil : {A: Type} -> Vec A Zero
  VCons : {A : Type} -> {n : Nat} -> A -> Vec A n -> Vec A (Succ n)
`;
    const results = compileSource(source);
    const vecBlock = results.find(r => r.name === 'Vec');
    const decl = vecBlock!.declarations[0];
    expect(decl.sourceMap).toBeDefined();
    expect(decl.typeInfoMap).toBeDefined();

    if (decl.sourceMap && decl.typeInfoMap) {
      // "Vec A" in the domain of VCons: ... -> Vec A n -> ...
      const domainFnPath = 'constructors[1].type.body.body.body.domain.fn';
      const domainFnRange = decl.sourceMap.get(domainFnPath);
      expect(domainFnRange).toBeDefined();

      if (domainFnRange) {
        const result = getTypeAtSelection(
          domainFnRange.start.pos,
          domainFnRange.end.pos,
          decl.sourceMap,
          decl.elabMap,
          decl.typeInfoMap,
        );
        expect(result).toBeDefined();
        expect(result!.prettyType).toBe('(Nat -> Type)');
      }
    }
  });

  test('argument type info is not overwritten by APP result type', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)
`;
    const results = compileSource(source);
    const plusBlock = results.find(r => r.name === 'plus');
    const decl = plusBlock!.declarations[0];
    expect(decl.typeInfoMap).toBeDefined();

    if (decl.typeInfoMap) {
      // The argument "a" in "plus a" should have type Nat (not Nat -> Nat)
      const argPath = 'value.clauses[1].rhs.arg.fn.arg';
      const argEntry = decl.typeInfoMap.get(argPath);
      expect(argEntry).toBeDefined();
      if (argEntry) {
        const names = argEntry.context.map(c => c.name).reverse();
        expect(prettyPrint(argEntry.type, names)).toBe('Nat');
      }
    }
  });
});

// ============================================================================
// Pattern walk-up: surfacePath updates when walking up to parent
// ============================================================================

describe('Pattern type info walk-up', () => {
  test('cursor on constructor name in pattern shows pattern type with correct source range', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)
`;
    const results = compileSource(source);
    const plusBlock = results.find(r => r.name === 'plus');
    const decl = plusBlock!.declarations[0];
    expect(decl.sourceMap).toBeDefined();
    expect(decl.typeInfoMap).toBeDefined();

    if (decl.sourceMap && decl.typeInfoMap) {
      // "Succ" is part of pattern "(Succ a)" — the constructor name sub-path
      // Find a sourceMap entry for "Succ" within a pattern
      const succNamePath = 'value.clauses[1].patterns[0].name';
      const succRange = decl.sourceMap.get(succNamePath);
      if (succRange) {
        const result = getTypeAtCursor(
          succRange.start.pos,
          decl.sourceMap,
          decl.elabMap,
          decl.typeInfoMap,
        );
        expect(result).toBeDefined();
        if (result) {
          // Hovering on a constructor name in a pattern shows the constructor's full type
          // (e.g., Succ : Nat -> Nat), which is more informative than the matched type (Nat).
          expect(result.prettyType).toBe('(Nat -> Nat)');
        }
      }
    }
  });

  test('cursor on Zero in pattern shows Nat', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

isZero : Nat -> Nat
isZero Zero = Zero
isZero (Succ n) = Zero
`;
    const results = compileSource(source);
    const block = results.find(r => r.name === 'isZero');
    const decl = block!.declarations[0];

    if (decl.sourceMap && decl.typeInfoMap) {
      // Zero in first clause's pattern
      const zeroPath = 'value.clauses[0].patterns[0]';
      const zeroRange = decl.sourceMap.get(zeroPath);
      if (zeroRange) {
        const result = getTypeAtCursor(
          zeroRange.start.pos,
          decl.sourceMap,
          decl.elabMap,
          decl.typeInfoMap,
        );
        expect(result).toBeDefined();
        if (result) {
          expect(result.prettyType).toBe('Nat');
        }
      }
    }
  });
});

// ============================================================================
// Regression tests for type-at-cursor bugs (right function)
// ============================================================================

describe('Type display regression tests', () => {
  // Source: right : {A : Type} -> {B : Type} -> B -> A -> B
  //         right {A} b = \x => b
  const rightSource = `
right : {A : Type} -> {B : Type} -> B -> A -> B
right {A} b = \\x => b
`;

  function getRightDecl() {
    const results = compileSource(rightSource);
    const block = results.find(r => r.name === 'right');
    expect(block).toBeDefined();
    expect(block!.checkSuccess).toBe(true);
    return block!.declarations.find(d => d.name === 'right')!;
  }

  test('implicit pattern {A} shows type Type', () => {
    const decl = getRightDecl();
    expect(decl.sourceMap).toBeDefined();
    expect(decl.typeInfoMap).toBeDefined();
    if (!decl.sourceMap || !decl.typeInfoMap) return;

    // Find the source position for {A} in the pattern
    // The surface path for the A pattern variable name
    const aNamePath = 'value.clauses[0].patterns[0].name';
    const aRange = decl.sourceMap.get(aNamePath);
    if (aRange) {
      const result = getTypeAtCursor(
        aRange.start.pos,
        decl.sourceMap,
        decl.elabMap,
        decl.typeInfoMap,
      );
      expect(result).toBeDefined();
      if (result) {
        expect(result.prettyType).toBe('Type');
      }
    }
  });

  test('lambda parameter \\x shows type A', () => {
    const decl = getRightDecl();
    expect(decl.sourceMap).toBeDefined();
    expect(decl.typeInfoMap).toBeDefined();
    if (!decl.sourceMap || !decl.typeInfoMap) return;

    // The lambda is in the RHS: \x => b
    // The .name sub-path for the lambda parameter
    const lambdaNamePath = 'value.clauses[0].rhs.name';
    const lambdaRange = decl.sourceMap.get(lambdaNamePath);
    if (lambdaRange) {
      const result = getTypeAtCursor(
        lambdaRange.start.pos,
        decl.sourceMap,
        decl.elabMap,
        decl.typeInfoMap,
      );
      expect(result).toBeDefined();
      if (result) {
        // x has type A (the domain of the Pi A -> B)
        expect(result.prettyType).toBe('A');
      }
    }
  });

  test('variable b in lambda body shows type B', () => {
    const decl = getRightDecl();
    expect(decl.sourceMap).toBeDefined();
    expect(decl.typeInfoMap).toBeDefined();
    if (!decl.sourceMap || !decl.typeInfoMap) return;

    // b is in the lambda body: \x => b
    const bodyPath = 'value.clauses[0].rhs.body';
    const bodyRange = decl.sourceMap.get(bodyPath);
    if (bodyRange) {
      const result = getTypeAtCursor(
        bodyRange.start.pos,
        decl.sourceMap,
        decl.elabMap,
        decl.typeInfoMap,
      );
      expect(result).toBeDefined();
      if (result) {
        expect(result.prettyType).toBe('B');
      }
    }
  });

  test('binder name n in {n : Nat} shows type Nat (multi-block)', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

f : {n : Nat} -> Nat
f {n} = n
`;
    const results = compileSource(source);
    const block = results.find(r => r.name === 'f');
    expect(block).toBeDefined();
    expect(block!.checkSuccess).toBe(true);
    const decl = block!.declarations.find(d => d.name === 'f')!;
    expect(decl.sourceMap).toBeDefined();
    expect(decl.typeInfoMap).toBeDefined();
    if (!decl.sourceMap || !decl.typeInfoMap) return;

    // The .name entry for the binder in the type signature: {n : Nat}
    // In the kernel, this is the Pi binder, so the type.name sub-path
    const binderNamePath = 'type.name';
    const binderRange = decl.sourceMap.get(binderNamePath);
    if (binderRange) {
      const result = getTypeAtCursor(
        binderRange.start.pos,
        decl.sourceMap,
        decl.elabMap,
        decl.typeInfoMap,
      );
      expect(result).toBeDefined();
      if (result) {
        // n's type should be Nat (the domain of the Pi)
        expect(result.prettyType).toBe('Nat');
      }
    }
  });
});

describe('nth pattern type-info (multi-block sourceMap)', () => {
  // nth uses Vec/Fin which are indexed inductive types in a separate block
  const nthSource = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Fin : Nat -> Type where
  FZero : {n : Nat} -> Fin (Succ n)
  FSucc : {n : Nat} -> Fin n -> Fin (Succ n)

inductive Vec : Type -> Nat -> Type where
  VNil : {A: Type} -> Vec A Zero
  VCons : {A : Type} -> {n : Nat} -> A -> Vec A n -> Vec A (Succ n)

nth : {A : Type} -> {n : Nat} -> Vec A n -> Fin n -> A
nth (VCons h _) FZero = h
nth (VCons h tail) (FSucc f) = nth tail f
`;

  function getNthDecl() {
    const results = compileSource(nthSource);
    const block = results.find(r => r.name === 'nth');
    expect(block).toBeDefined();
    expect(block!.checkSuccess).toBe(true);
    const decl = block!.declarations.find(d => d.name === 'nth')!;
    expect(decl.sourceMap).toBeDefined();
    expect(decl.typeInfoMap).toBeDefined();
    return decl;
  }

  test('VCons in pattern shows constructor type, not Type', () => {
    const decl = getNthDecl();
    if (!decl.sourceMap || !decl.typeInfoMap) return;

    // Clause 1: nth (VCons h tail) (FSucc f) = nth tail f
    const vconsNamePath = 'value.clauses[1].patterns[0].name';
    const vconsRange = decl.sourceMap.get(vconsNamePath);
    expect(vconsRange).toBeDefined();
    if (vconsRange) {
      const text = nthSource.substring(vconsRange.start.pos, vconsRange.end.pos);
      expect(text).toBe('VCons');
      const result = getTypeAtCursor(
        vconsRange.start.pos + 2, // VCo|ns
        decl.sourceMap,
        decl.elabMap,
        decl.typeInfoMap,
      );
      expect(result).toBeDefined();
      if (result) {
        // VCons should NOT show "Type" - it's a constructor
        expect(result.prettyType).not.toBe('Type');
      }
    }
  });

  test('tail in pattern shows Vec type', () => {
    const decl = getNthDecl();
    if (!decl.sourceMap || !decl.typeInfoMap) return;

    // Clause 1: nth (VCons h tail) (FSucc f) = nth tail f
    const tailPath = 'value.clauses[1].patterns[0].args[1]';
    const tailRange = decl.sourceMap.get(tailPath);
    expect(tailRange).toBeDefined();
    if (tailRange) {
      const text = nthSource.substring(tailRange.start.pos, tailRange.end.pos);
      expect(text).toBe('tail');
      const result = getTypeAtCursor(
        tailRange.start.pos + 2, // ta|il
        decl.sourceMap,
        decl.elabMap,
        decl.typeInfoMap,
      );
      expect(result).toBeDefined();
      if (result) {
        // tail should NOT show "Type" - it has type Vec A n
        expect(result.prettyType).not.toBe('Type');
        expect(result.prettyType).not.toContain('VCons');
        expect(result.prettyType).toContain('Vec');
      }
    }
  });

  test('FSucc in pattern shows constructor type, not Nat', () => {
    const decl = getNthDecl();
    if (!decl.sourceMap || !decl.typeInfoMap) return;

    // Clause 1: nth (VCons h tail) (FSucc f) = nth tail f
    const fsuccNamePath = 'value.clauses[1].patterns[1].name';
    const fsuccRange = decl.sourceMap.get(fsuccNamePath);
    expect(fsuccRange).toBeDefined();
    if (fsuccRange) {
      const text = nthSource.substring(fsuccRange.start.pos, fsuccRange.end.pos);
      expect(text).toBe('FSucc');
      const result = getTypeAtCursor(
        fsuccRange.start.pos + 1, // F|Succ
        decl.sourceMap,
        decl.elabMap,
        decl.typeInfoMap,
      );
      expect(result).toBeDefined();
      if (result) {
        // FSucc should NOT show just "Nat" - it's a constructor of Fin
        expect(result.prettyType).not.toBe('Nat');
      }
    }
  });

  test('f in (FSucc f) pattern shows Fin type', () => {
    const decl = getNthDecl();
    if (!decl.sourceMap || !decl.typeInfoMap) return;

    // Clause 1: (FSucc f) - the f argument
    const fPatPath = 'value.clauses[1].patterns[1].args[0]';
    const fRange = decl.sourceMap.get(fPatPath);
    expect(fRange).toBeDefined();
    if (fRange) {
      const text = nthSource.substring(fRange.start.pos, fRange.end.pos);
      expect(text).toBe('f');
      const result = getTypeAtCursor(
        fRange.start.pos, // f|
        decl.sourceMap,
        decl.elabMap,
        decl.typeInfoMap,
      );
      expect(result).toBeDefined();
      if (result) {
        // f should have type Fin n, not Nat
        expect(result.prettyType).not.toBe('Nat');
        expect(result.prettyType).toContain('Fin');
      }
    }
  });

  // TODO: f in RHS has type A instead of Fin n due to a checker/meta-solving bug:
  // the typeInfoMap records Var(4)=A as the type for rhs.arg instead of App(Fin, Var(3))=Fin n.
  // The fn type also shows Fin n -> n instead of Fin n -> A (de Bruijn index off by one).
  // This is a checker-level issue, not a sourceMap/type-info lookup issue.
  test.todo('f in RHS (nth tail f) shows Fin type, not A', () => {
    const decl = getNthDecl();
    if (!decl.sourceMap || !decl.typeInfoMap) return;

    // Clause 1 RHS: nth tail f - the f argument
    const fRhsPath = 'value.clauses[1].rhs.arg';
    const fRange = decl.sourceMap.get(fRhsPath);
    expect(fRange).toBeDefined();
    if (fRange) {
      const text = nthSource.substring(fRange.start.pos, fRange.end.pos);
      expect(text).toBe('f');
      const result = getTypeAtCursor(
        fRange.start.pos,
        decl.sourceMap,
        decl.elabMap,
        decl.typeInfoMap,
      );
      expect(result).toBeDefined();
      if (result) {
        // f in RHS should have type Fin n, not A
        expect(result.prettyType).not.toBe('A');
        expect(result.prettyType).toContain('Fin');
      }
    }
  });

  test('sourceMap positions are file-absolute for multi-block sources', () => {
    const decl = getNthDecl();
    if (!decl.sourceMap) return;

    // Every sourceMap entry's pos should point to the correct text in nthSource
    for (const [path, range] of decl.sourceMap) {
      const text = nthSource.substring(range.start.pos, range.end.pos);
      // Should not be empty (would indicate out-of-range pos)
      expect(text.length).toBeGreaterThan(0);
      // Should not contain newlines at boundaries (would indicate wrong offset)
      expect(text[0]).not.toBe('\n');
    }
  });
});

describe('with-clause type info via main declaration', () => {
  const withSource = `
inductive Bool : Type where
  True : Bool
  False : Bool

inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive List : Type -> Type where
  Nil : {A : Type} -> List A
  Cons : {A : Type} -> A -> List A -> List A

filter : {A : Type} -> (A -> Bool) -> List A -> List A
filter f Nil = Nil
filter f (Cons x xs) with f x
  | True => Cons x (filter f xs)
  | False => filter f xs
`;

  function getFilterMainDecl() {
    const results = compileSource(withSource);
    const filterBlock = results.find(r =>
      r.declarations.some(d => d.name === 'filter')
    );
    expect(filterBlock).toBeDefined();
    const mainDecl = filterBlock!.declarations.find(d => d.name === 'filter');
    expect(mainDecl).toBeDefined();
    expect(mainDecl!.sourceMap).toBeDefined();
    expect(mainDecl!.typeInfoMap).toBeDefined();
    return mainDecl!;
  }

  test('True pattern in with-clause shows Bool via main declaration', () => {
    const decl = getFilterMainDecl();
    if (!decl.sourceMap || !decl.typeInfoMap) return;

    const truePath = 'value.clauses[1].withClauses[0].patterns[0]';
    const trueRange = decl.sourceMap.get(truePath);
    expect(trueRange).toBeDefined();
    if (trueRange) {
      const result = getTypeAtCursor(trueRange.start.pos, decl.sourceMap, decl.elabMap, decl.typeInfoMap);
      expect(result).toBeDefined();
      expect(result!.prettyType).toBe('Bool');
    }
  });

  test('Cons in with-clause RHS shows constructor type via main declaration', () => {
    const decl = getFilterMainDecl();
    if (!decl.sourceMap || !decl.typeInfoMap) return;

    const consPath = 'value.clauses[1].withClauses[0].rhs.fn.fn';
    const consRange = decl.sourceMap.get(consPath);
    expect(consRange).toBeDefined();
    if (consRange) {
      const result = getTypeAtCursor(consRange.start.pos, decl.sourceMap, decl.elabMap, decl.typeInfoMap);
      expect(result).toBeDefined();
      expect(result!.prettyType).toContain('List');
    }
  });

  test('filter in False branch shows function type via main declaration', () => {
    const decl = getFilterMainDecl();
    if (!decl.sourceMap || !decl.typeInfoMap) return;

    const filterPath = 'value.clauses[1].withClauses[1].rhs.fn.fn';
    const filterRange = decl.sourceMap.get(filterPath);
    expect(filterRange).toBeDefined();
    if (filterRange) {
      const result = getTypeAtCursor(filterRange.start.pos, decl.sourceMap, decl.elabMap, decl.typeInfoMap);
      expect(result).toBeDefined();
      expect(result!.prettyType).toContain('Bool');
      expect(result!.prettyType).toContain('List');
    }
  });

  test('xs in False branch shows List A via main declaration', () => {
    const decl = getFilterMainDecl();
    if (!decl.sourceMap || !decl.typeInfoMap) return;

    const xsPath = 'value.clauses[1].withClauses[1].rhs.arg';
    const xsRange = decl.sourceMap.get(xsPath);
    expect(xsRange).toBeDefined();
    if (xsRange) {
      const result = getTypeAtCursor(xsRange.start.pos, decl.sourceMap, decl.elabMap, decl.typeInfoMap);
      expect(result).toBeDefined();
      expect(result!.prettyType).toContain('List');
    }
  });
});

// ============================================================================
// Constructor pattern argument type info
// ============================================================================

describe('constructor pattern argument type info', () => {
  // Test with plus function which compiles cleanly (no meta-solving issues)
  const plusSource = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)
`;

  function getPlusDecl() {
    const results = compileSource(plusSource);
    const block = results.find(r => r.name === 'plus');
    expect(block).toBeDefined();
    const decl = block!.declarations.find(d => d.name === 'plus')!;
    expect(decl.sourceMap).toBeDefined();
    expect(decl.typeInfoMap).toBeDefined();
    return decl;
  }

  test('cursor on "a" in (Succ a) shows Nat, not (Nat -> Nat)', () => {
    const decl = getPlusDecl();
    if (!decl.sourceMap || !decl.typeInfoMap) return;

    // Find the sourceMap entry for args[0] in (Succ a) pattern
    const argPath = 'value.clauses[1].patterns[0].args[0]';
    const argRange = decl.sourceMap.get(argPath);
    expect(argRange).toBeDefined();
    if (argRange) {
      const result = getTypeAtCursor(argRange.start.pos, decl.sourceMap, decl.elabMap, decl.typeInfoMap);
      expect(result).toBeDefined();
      // "a" is a constructor arg of Succ, should have type Nat
      expect(result!.prettyType).toBe('Nat');
    }
  });

  test('cursor on "Succ" in (Succ a) shows constructor type', () => {
    const decl = getPlusDecl();
    if (!decl.sourceMap || !decl.typeInfoMap) return;

    const namePath = 'value.clauses[1].patterns[0].name';
    const nameRange = decl.sourceMap.get(namePath);
    expect(nameRange).toBeDefined();
    if (nameRange) {
      const result = getTypeAtCursor(nameRange.start.pos, decl.sourceMap, decl.elabMap, decl.typeInfoMap);
      expect(result).toBeDefined();
      // "Succ" constructor name shows constructor type (Nat -> Nat)
      expect(result!.prettyType).toBe('(Nat -> Nat)');
    }
  });

  test('selecting "(Succ a)" shows matched type Nat', () => {
    const decl = getPlusDecl();
    if (!decl.sourceMap || !decl.typeInfoMap) return;

    const patPath = 'value.clauses[1].patterns[0]';
    const patRange = decl.sourceMap.get(patPath);
    expect(patRange).toBeDefined();
    if (patRange) {
      const result = getTypeAtSelection(patRange.start.pos, patRange.end.pos, decl.sourceMap, decl.elabMap, decl.typeInfoMap);
      expect(result).toBeDefined();
      expect(result!.prettyType).toBe('Nat');
    }
  });

  // Test with constructor pattern with implicit args (neq in (No neq))
  // Uses DecEq which has implicit {m n : Nat} parameters
  test.todo('cursor on "neq" in (No neq) shows Equal m n -> Void (blocked by clause 0 meta-solving bug)');

  test.todo('cursor on "No" in (No neq) shows constructor type (blocked by clause 0 meta-solving bug)');
});
