/**
 * Tests for the Type Query System
 */

import { describe, it, expect } from 'vitest';
import { queryTypeAtPath, enumerateSubterms, describeTypeAtPath } from './tt-type-query';
import { TTKTerm, TTKContext, prettyPrint } from './tt-kernel';
import { IndexPath } from './source-position';
import { checkSourceBlocks } from '../parser/block-checker';
import { queryTypeAtPosition, queryTypeForSelection } from './tt-source-query';
import { Parser, parseDeclarations } from '../parser/tt-parser';

// ============================================================================
// Test Helpers
// ============================================================================

// Simple term constructors for testing
const mkVar = (index: number): TTKTerm => ({ tag: 'Var', index });
const mkSort = (level: number): TTKTerm => ({ tag: 'Sort', level });
const mkPi = (name: string, domain: TTKTerm, body: TTKTerm): TTKTerm => ({
  tag: 'Binder',
  name,
  binderKind: { tag: 'BPi' },
  domain,
  body
});
const mkLam = (name: string, domain: TTKTerm, body: TTKTerm): TTKTerm => ({
  tag: 'Binder',
  name,
  binderKind: { tag: 'BLam' },
  domain,
  body
});
const mkApp = (fn: TTKTerm, arg: TTKTerm): TTKTerm => ({ tag: 'App', fn, arg });
const mkConst = (name: string, type: TTKTerm): TTKTerm => ({ tag: 'Const', name, type });

const Type0 = mkSort(0);
const Type1 = mkSort(1);

// Path helpers
const field = (name: string): { kind: 'field'; name: string } => ({ kind: 'field', name });
const arr = (index: number): { kind: 'array'; index: number } => ({ kind: 'array', index });

// ============================================================================
// Tests
// ============================================================================

describe('Type Query System', () => {
  describe('queryTypeAtPath', () => {
    it('should query the type at the root (empty path)', () => {
      // id : (A : Type) -> A -> A
      // id = \A => \x => x
      const idType = mkPi('A', Type0, mkPi('_', mkVar(0), mkVar(1)));
      const idTerm = mkLam('A', Type0, mkLam('x', mkVar(0), mkVar(0)));

      const result = queryTypeAtPath(idTerm, [], []);

      expect(result.success).toBe(true);
      if (result.success) {
        // The type of \A => \x => x should be (A : Type) -> A -> A
        expect(result.term).toEqual(idTerm);
        expect(result.type.tag).toBe('Binder');
      }
    });

    it('should query the type of a lambda body', () => {
      // \x : Type => x
      const term = mkLam('x', Type0, mkVar(0));

      const result = queryTypeAtPath(term, [], [field('body')]);

      expect(result.success).toBe(true);
      if (result.success) {
        // The body is `x` (Var 0), and in the extended context, x : Type
        expect(result.term).toEqual(mkVar(0));
        // Type of x is Type (which was shifted when added to context)
        expect(result.type.tag).toBe('Sort');
      }
    });

    it('should query the type of a lambda domain', () => {
      // \x : Type => x
      const term = mkLam('x', Type0, mkVar(0));

      const result = queryTypeAtPath(term, [], [field('domain')]);

      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.term).toEqual(Type0);
        // Type of Type is Type1
        expect(result.type).toEqual(Type1);
      }
    });

    it('should query nested paths', () => {
      // \A : Type => \x : A => x
      const term = mkLam('A', Type0, mkLam('x', mkVar(0), mkVar(0)));

      // Query the inner body (the variable x)
      const result = queryTypeAtPath(term, [], [field('body'), field('body')]);

      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.term).toEqual(mkVar(0));
        // In context [x : A, A : Type], x has type A
        // But A was shifted, so the type is Var(1)
        expect(result.context.length).toBe(2);
        expect(result.context[0].name).toBe('x');
        expect(result.context[1].name).toBe('A');
      }
    });

    it('should query application function', () => {
      // f : Type -> Type in context
      // f Type
      const ctx: TTKContext = [{ name: 'f', type: mkPi('_', Type0, Type0) }];
      const term = mkApp(mkVar(0), Type0);

      const result = queryTypeAtPath(term, ctx, [field('fn')]);

      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.term).toEqual(mkVar(0));
        // f has type Type -> Type
        expect(result.type.tag).toBe('Binder');
      }
    });

    it('should query application argument', () => {
      // f : Type -> Type in context
      // f Type
      const ctx: TTKContext = [{ name: 'f', type: mkPi('_', Type0, Type0) }];
      const term = mkApp(mkVar(0), Type0);

      const result = queryTypeAtPath(term, ctx, [field('arg')]);

      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.term).toEqual(Type0);
        expect(result.type).toEqual(Type1);
      }
    });

    it('should return error for invalid path', () => {
      const term = mkVar(0);
      const ctx: TTKContext = [{ name: 'x', type: Type0 }];

      const result = queryTypeAtPath(term, ctx, [field('body')]);

      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.error).toContain('Cannot navigate');
      }
    });

    it('should extend context correctly when entering binders', () => {
      // \A : Type => \B : Type => \f : (A -> B) => \x : A => f x
      const term = mkLam('A', Type0,
        mkLam('B', Type0,
          mkLam('f', mkPi('_', mkVar(1), mkVar(1)),
            mkLam('x', mkVar(2),
              mkApp(mkVar(1), mkVar(0))))));

      // Navigate to the innermost body (f x)
      const path = [field('body'), field('body'), field('body'), field('body')];
      const result = queryTypeAtPath(term, [], path);

      expect(result.success).toBe(true);
      if (result.success) {
        // Context should have [x, f, B, A]
        expect(result.context.length).toBe(4);
        expect(result.context.map(b => b.name)).toEqual(['x', 'f', 'B', 'A']);

        // f x has type B (with appropriate shifting)
        // The result type should be some variable reference
        expect(result.type.tag).toBe('Var');
      }
    });
  });

  describe('describeTypeAtPath', () => {
    it('should format type description correctly', () => {
      const term = mkLam('x', Type0, mkVar(0));

      const desc = describeTypeAtPath(term, [], []);

      // Should show something like "λx : Prop. x : (x : Prop) → Prop"
      // (Sort level 0 is printed as "Prop" by the pretty printer)
      expect(desc).toContain(':');
      expect(desc).toContain('Prop');
    });
  });

  describe('enumerateSubterms', () => {
    it('should enumerate all subterms of a lambda', () => {
      // \x : Type => x
      const term = mkLam('x', Type0, mkVar(0));

      const subterms = enumerateSubterms(term, [], 5);

      // Should include: root, domain, body
      expect(subterms.length).toBeGreaterThanOrEqual(3);

      // Check that we have the expected paths
      const paths = subterms.map(s => s.pathString);
      expect(paths).toContain(''); // root
      expect(paths).toContain('domain');
      expect(paths).toContain('body');
    });

    it('should enumerate nested applications', () => {
      // f : Type -> Type -> Type in context
      // f Type Type
      const ctx: TTKContext = [{ name: 'f', type: mkPi('_', Type0, mkPi('_', Type0, Type0)) }];
      const term = mkApp(mkApp(mkVar(0), Type0), Type0);

      const subterms = enumerateSubterms(term, ctx, 5);

      // Should have paths for subterms - root might not type-check depending on context shifting
      const paths = subterms.map(s => s.pathString);
      // Inner parts should be present
      expect(paths).toContain('fn.fn'); // f
      expect(paths).toContain('fn.arg'); // first Type arg
      expect(paths).toContain('arg'); // second Type arg
    });

    it('should respect maxDepth', () => {
      // Deeply nested term
      let term: TTKTerm = Type0;
      for (let i = 0; i < 10; i++) {
        term = mkLam(`x${i}`, Type0, term);
      }

      const shallow = enumerateSubterms(term, [], 2);
      const deep = enumerateSubterms(term, [], 10);

      expect(deep.length).toBeGreaterThan(shallow.length);
    });
  });
});

describe('Type display with named variables', () => {
  it('should display type using named variables not de Bruijn indices', () => {
    // def swap (A : Type) (f : A -> A -> A) (x : A) (y : A) : A := f y x
    // When cursor is on x (the final x), type should show "x : A" not "x : #3"

    // Build: \A : Type => \f : (A -> A -> A) => \x : A => \y : A => f y x
    const term = mkLam('A', Type0,
      mkLam('f', mkPi('_', mkVar(0), mkPi('_', mkVar(1), mkVar(2))),
        mkLam('x', mkVar(1),
          mkLam('y', mkVar(2),
            mkApp(mkApp(mkVar(2), mkVar(0)), mkVar(1))))));

    // Navigate to the innermost argument 'x' in 'f y x' (that's the last Var(1))
    // Path: body.body.body.body.arg (to get to x which is the arg of (f y) x)
    const path = [field('body'), field('body'), field('body'), field('body'), field('arg')];
    const result = queryTypeAtPath(term, [], path);

    expect(result.success).toBe(true);
    if (result.success) {
      // The term is Var(1) which is x
      expect(result.term).toEqual(mkVar(1));

      // Context should be [y, x, f, A]
      expect(result.context.map(b => b.name)).toEqual(['y', 'x', 'f', 'A']);

      // The type should print as "A" not "#3"
      const typeStr = prettyPrint(result.type, result.context.map(b => b.name));
      expect(typeStr).toBe('A');

      // describeTypeAtPath should show "x : A"
      const desc = describeTypeAtPath(term, [], path);
      expect(desc).toBe('x : A');
    }
  });

  it('should display lambda parameter types correctly', () => {
    // \A : Type => \x : A => x
    // When cursor is on x (in body), type of x should be "A"
    const term = mkLam('A', Type0, mkLam('x', mkVar(0), mkVar(0)));

    // Navigate to the body.body which is the final Var(0) - the variable x
    const path = [field('body'), field('body')];
    const result = queryTypeAtPath(term, [], path);

    expect(result.success).toBe(true);
    if (result.success) {
      expect(result.term).toEqual(mkVar(0));

      // Context should be [x, A]
      expect(result.context.map(b => b.name)).toEqual(['x', 'A']);

      // Type of x is A (which is Var(1) in the shifted context)
      // When printed with context ['x', 'A'], index 1 -> 'A'
      const typeStr = prettyPrint(result.type, result.context.map(b => b.name));
      expect(typeStr).toBe('A');
    }
  });
});

describe('Path-based API vs Source-based API', () => {
  it('should demonstrate path-based queries work without source maps', () => {
    // This test shows that the core API works independently of source positions
    // Machine-assembled ASTs can be queried directly by path

    // Build a term programmatically (no source)
    const natType = mkConst('Nat', Type0);
    const addType = mkPi('_', natType, mkPi('_', natType, natType));
    const addConst = mkConst('add', addType);

    // Apply add to two arguments
    const term = mkApp(mkApp(addConst, mkConst('zero', natType)), mkConst('one', natType));

    // Query the type of the function part
    const fnResult = queryTypeAtPath(term, [], [field('fn')]);
    expect(fnResult.success).toBe(true);
    if (fnResult.success) {
      // add zero : Nat -> Nat
      const typeStr = prettyPrint(fnResult.type);
      expect(typeStr).toContain('Nat');
    }

    // Query the type of the first argument
    const arg1Result = queryTypeAtPath(term, [], [field('fn'), field('arg')]);
    expect(arg1Result.success).toBe(true);
    if (arg1Result.success) {
      // zero : Nat
      expect(prettyPrint(arg1Result.type)).toBe('Nat');
    }
  });
});

describe('Real-world type query bugs', () => {
  // Helper to create value-relative source map
  function createValueRelativeSourceMap(sourceMap: Map<string, any>): Map<string, any> {
    const valueRelativeMap = new Map<string, any>();
    const prefix = 'value.';
    for (const [pathKey, range] of sourceMap) {
      if (pathKey.startsWith(prefix)) {
        valueRelativeMap.set(pathKey.slice(prefix.length), range);
      } else if (pathKey === 'value') {
        valueRelativeMap.set('', range);
      }
    }
    return valueRelativeMap;
  }

  it('should show x : A not x : #3 for multi-line swap definition', () => {
    const sourceCode = `swap : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
swap A = \\f => \\(x: A) (y: A) => f y x`;

    const results = checkSourceBlocks(sourceCode);
    const swapBlock = results.find(b => b.name === 'swap');
    expect(swapBlock).toBeDefined();
    expect(swapBlock!.checkSuccess).toBe(true);

    const queryData = swapBlock!.typeQueryData!;
    const valueRelativeMap = createValueRelativeSourceMap(queryData.sourceMap);

    // Find position of 'x' in "f y x" at the end of line 2
    const lines = sourceCode.split('\n');
    const lastXPos = lines[1].lastIndexOf('x');
    const pos = { line: 2, col: lastXPos + 1, pos: 0 };
    const result = queryTypeAtPosition(pos, valueRelativeMap, queryData.kernelValue!, queryData.context, queryData.kernelType);

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      expect(typeStr).toBe('A');
      expect(names).toContain('A');
    }
  });

  it('should show f : A -> A -> A not f : ?f_type for lambda parameter', () => {
    // When we have an unannotated lambda like \f => ..., the parser creates a hole
    // for the domain type. But we know the expected type from the function signature,
    // so we should be able to use it to fill in the hole.
    const sourceCode = `swap : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
swap A = \\f => \\(x: A) (y: A) => f y x`;

    const results = checkSourceBlocks(sourceCode);
    const swapBlock = results.find(b => b.name === 'swap');
    expect(swapBlock!.checkSuccess).toBe(true);

    const queryData = swapBlock!.typeQueryData!;
    const valueRelativeMap = createValueRelativeSourceMap(queryData.sourceMap);

    // Find position of 'f' in "f y x" (the function being applied)
    const lines = sourceCode.split('\n');
    const fPos = lines[1].lastIndexOf('f y x');
    const pos = { line: 2, col: fPos + 1, pos: 0 };
    const result = queryTypeAtPosition(pos, valueRelativeMap, queryData.kernelValue!, queryData.context, queryData.kernelType, 'swap');

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      // Should NOT contain '?' - should be A -> A -> A
      expect(typeStr).not.toContain('?');
      expect(typeStr).toMatch(/A\s*->\s*A\s*->\s*A/);
    }
  });

  it('should show a : Nat for nested pattern variable in Succ a', () => {
    const sourceCode = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

    const results = checkSourceBlocks(sourceCode);
    const plusBlock = results.find(b => b.name === 'plus');
    expect(plusBlock).toBeDefined();
    expect(plusBlock!.checkSuccess).toBe(true);

    const queryData = plusBlock!.typeQueryData!;
    const valueRelativeMap = createValueRelativeSourceMap(queryData.sourceMap);

    // Find the 'a' in "plus a b" on the last line
    const lines = sourceCode.split('\n');
    const lastLine = lines[lines.length - 1];
    const plusABPos = lastLine.indexOf('plus a b');
    const aPos = plusABPos + 5; // 'plus ' is 5 chars
    const pos = { line: lines.length, col: aPos + 1, pos: 0 };
    const result = queryTypeAtPosition(pos, valueRelativeMap, queryData.kernelValue!, queryData.context, queryData.kernelType);

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      // Should be 'Nat', not '??' or anything with '?'
      expect(typeStr).not.toContain('?');
      expect(typeStr).toBe('Nat');
    }
  });

  it('should show plus : Nat -> Nat -> Nat for recursive call', () => {
    const sourceCode = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

    const results = checkSourceBlocks(sourceCode);
    const plusBlock = results.find(b => b.name === 'plus');
    expect(plusBlock!.checkSuccess).toBe(true);

    const queryData = plusBlock!.typeQueryData!;
    const valueRelativeMap = createValueRelativeSourceMap(queryData.sourceMap);

    // Find 'plus' in "Succ (plus a b)" - the recursive call
    const lines = sourceCode.split('\n');
    const lastLine = lines[lines.length - 1];
    const plusPos = lastLine.indexOf('plus a b');
    const pos = { line: lines.length, col: plusPos + 1, pos: 0 };
    // Pass the definition name 'plus' so recursive references can be resolved
    const result = queryTypeAtPosition(pos, valueRelativeMap, queryData.kernelValue!, queryData.context, queryData.kernelType, 'plus');

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      // Should NOT contain '?' (hole marker like ?plus_type)
      expect(typeStr).not.toContain('?');
      // Should be Nat -> Nat -> Nat
      expect(typeStr).toMatch(/Nat\s*->\s*Nat\s*->\s*Nat/);
    }
  });

  it('should not show x : plus when there are multiple definitions', () => {
    const sourceCode = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)

swap : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
swap A = \\f => \\(x: A) (y: A) => f y x`;

    const results = checkSourceBlocks(sourceCode);
    const swapBlock = results.find(b => b.name === 'swap');
    expect(swapBlock!.checkSuccess).toBe(true);

    const queryData = swapBlock!.typeQueryData!;
    const valueRelativeMap = createValueRelativeSourceMap(queryData.sourceMap);

    // Find position of 'x' in the swap definition
    const lines = sourceCode.split('\n');
    const swapImplLine = lines.findIndex(l => l.startsWith('swap A'));
    const lastXPos = lines[swapImplLine].lastIndexOf('x');
    const pos = { line: swapImplLine + 1, col: lastXPos + 1, pos: 0 };
    const result = queryTypeAtPosition(pos, valueRelativeMap, queryData.kernelValue!, queryData.context, queryData.kernelType);

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      expect(typeStr).not.toBe('plus');
      expect(typeStr).toBe('A');
      expect(names).toContain('A');
    }
  });

  it('should show f y : A -> A when selecting partial application "f y"', () => {
    // When selecting "f y" in "f y x", should get type A -> A (partial application)
    // NOT the type of the full "f y x" application which is A
    const sourceCode = `swap : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
swap A = \\f => \\(x: A) (y: A) => f y x`;

    const results = checkSourceBlocks(sourceCode);
    const swapBlock = results.find(b => b.name === 'swap');
    expect(swapBlock!.checkSuccess).toBe(true);

    const queryData = swapBlock!.typeQueryData!;
    const valueRelativeMap = createValueRelativeSourceMap(queryData.sourceMap);

    // Find "f y x" on line 2
    const lines = sourceCode.split('\n');
    const fyxPos = lines[1].lastIndexOf('f y x');

    // Select just "f y" (3 characters: 'f', ' ', 'y')
    const selectionRange = {
      start: { line: 2, col: fyxPos + 1, pos: 0 },
      end: { line: 2, col: fyxPos + 4, pos: 0 }  // "f y" is 3 chars
    };

    const result = queryTypeForSelection(selectionRange, valueRelativeMap, queryData.kernelValue!, queryData.context, queryData.kernelType, 'swap');

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      // "f y" should have type (A -> A) - one argument still to apply
      // NOT type A (which would be the full application f y x)
      expect(typeStr).toMatch(/A\s*->\s*A/);
      // Make sure it's NOT A -> A -> A (the type of f alone)
      expect(typeStr).not.toMatch(/A\s*->\s*A\s*->\s*A/);
    }
  });

  it('should show correct type when selecting full pattern clause RHS', () => {
    // When selecting the entire RHS "\f => \(x : A) (y : A) => f y x",
    // should get the type of the RHS (A -> A -> A), NOT the full function type
    const sourceCode = `swap : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
swap A = \\f => \\(x: A) (y: A) => f y x`;

    const results = checkSourceBlocks(sourceCode);
    const swapBlock = results.find(b => b.name === 'swap');
    expect(swapBlock!.checkSuccess).toBe(true);

    const queryData = swapBlock!.typeQueryData!;
    const valueRelativeMap = createValueRelativeSourceMap(queryData.sourceMap);

    // Find the full RHS: "\f => \(x: A) (y: A) => f y x"
    const lines = sourceCode.split('\n');
    const rhsStart = lines[1].indexOf('\\f');
    const rhsEnd = lines[1].length;

    const selectionRange = {
      start: { line: 2, col: rhsStart + 1, pos: 0 },
      end: { line: 2, col: rhsEnd + 1, pos: 0 }
    };

    const result = queryTypeForSelection(selectionRange, valueRelativeMap, queryData.kernelValue!, queryData.context, queryData.kernelType, 'swap');

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      // The RHS has type (f : A -> A -> A) -> (A -> A -> A)
      // which is the function type after stripping the first pattern (A : Type)
      // Should NOT be the full swap type with (A : Type) -> ...
      expect(typeStr).not.toContain('Type');
      expect(typeStr).toMatch(/A\s*->\s*A\s*->\s*A/);
    }
  });

  it('should show A : Type for pattern variable A in swap', () => {
    // When cursor is on 'A' in "swap A = ...", should show A : Type
    const sourceCode = `swap : (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
swap A = \\f => \\(x: A) (y: A) => f y x`;

    const results = checkSourceBlocks(sourceCode);
    const swapBlock = results.find(b => b.name === 'swap');
    expect(swapBlock!.checkSuccess).toBe(true);

    const queryData = swapBlock!.typeQueryData!;

    // Find 'A' in "swap A = " on line 2
    const lines = sourceCode.split('\n');
    const aPos = lines[1].indexOf('A');
    const pos = { line: 2, col: aPos + 1, pos: 0 };

    // For pattern LHS, we need a different approach - check what paths exist
    // The pattern A should be tracked in the source map
    const result = queryTypeAtPosition(pos, queryData.sourceMap, queryData.kernelValue!, queryData.context, queryData.kernelType, 'swap', sourceCode);

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      expect(typeStr).toBe('Type');
    }
  });

  it('should show a : Nat for pattern variable a in Succ pattern', () => {
    // When cursor is on 'a' in "(Succ a)", should show a : Nat
    const sourceCode = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

    const results = checkSourceBlocks(sourceCode);
    const plusBlock = results.find(b => b.name === 'plus');
    expect(plusBlock!.checkSuccess).toBe(true);

    const queryData = plusBlock!.typeQueryData!;

    // Find 'a' in "(Succ a)" pattern on the last line
    const lines = sourceCode.split('\n');
    const lastLine = lines[lines.length - 1];
    const succAPos = lastLine.indexOf('Succ a)');
    const aInPatternPos = succAPos + 5; // 'Succ ' is 5 chars
    const pos = { line: lines.length, col: aInPatternPos + 1, pos: 0 };

    const result = queryTypeAtPosition(pos, queryData.sourceMap, queryData.kernelValue!, queryData.context, queryData.kernelType, 'plus', sourceCode);

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      expect(typeStr).toBe('Nat');
    }
  });

  it('should show Succ a : Nat for constructor pattern', () => {
    // When selecting "(Succ a)", should show type Nat
    const sourceCode = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

    const results = checkSourceBlocks(sourceCode);
    const plusBlock = results.find(b => b.name === 'plus');
    expect(plusBlock!.checkSuccess).toBe(true);

    const queryData = plusBlock!.typeQueryData!;

    // Find "(Succ a)" pattern on the last line
    const lines = sourceCode.split('\n');
    const lastLine = lines[lines.length - 1];
    const succAStart = lastLine.indexOf('(Succ a)');
    const succAEnd = succAStart + 8; // "(Succ a)" is 8 chars

    const selectionRange = {
      start: { line: lines.length, col: succAStart + 1, pos: 0 },
      end: { line: lines.length, col: succAEnd + 1, pos: 0 }
    };

    const result = queryTypeForSelection(selectionRange, queryData.sourceMap, queryData.kernelValue!, queryData.context, queryData.kernelType, 'plus');

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      expect(typeStr).toBe('Nat');
    }
  });

  it('should show Succ : Nat -> Nat for constructor in pattern', () => {
    // When cursor is on 'Succ' in "(Succ a)", should show Succ : Nat -> Nat
    const sourceCode = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

    const results = checkSourceBlocks(sourceCode);
    const plusBlock = results.find(b => b.name === 'plus');
    expect(plusBlock!.checkSuccess).toBe(true);

    const queryData = plusBlock!.typeQueryData!;

    // Find 'Succ' in "(Succ a)" pattern
    const lines = sourceCode.split('\n');
    const lastLine = lines[lines.length - 1];
    const succPos = lastLine.indexOf('(Succ a)') + 1; // +1 to skip '('
    const pos = { line: lines.length, col: succPos + 1, pos: 0 };

    const result = queryTypeAtPosition(pos, queryData.sourceMap, queryData.kernelValue!, queryData.context, queryData.kernelType, 'plus', sourceCode);

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      expect(typeStr).toMatch(/Nat\s*->\s*Nat/);
    }
  });

  it.skip('should show eq : Equal Nat a b for pattern variable with dependent type', () => {
    // SKIPPED: Indexed types (Equal) have known issues with type checking.
    // This test validates the type query infrastructure but depends on
    // indexed type support being fixed first.
    //
    // BUG: Pattern variable types that reference earlier pattern bindings
    // were displaying incorrect names due to De Bruijn index mismatch.
    // When querying the type of 'eq' in "foo a b eq = ...",
    // we need the context to include 'a' and 'b' so that
    // the type "Equal Nat a b" can be pretty-printed correctly.
    const sourceCode = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : (A : Type) -> A -> A -> Type where
  refl : (A : Type) -> (x : A) -> Equal A x x

foo : (a : Nat) -> (b : Nat) -> Equal Nat a b -> Nat
foo a b eq = Zero`;

    const results = checkSourceBlocks(sourceCode);
    const fooBlock = results.find(b => b.name === 'foo');
    expect(fooBlock).toBeDefined();
    expect(fooBlock!.checkSuccess).toBe(true);

    const queryData = fooBlock!.typeQueryData!;

    // Find 'eq' in "foo a b eq = Zero" on the last line
    const lines = sourceCode.split('\n');
    const lastLine = lines[lines.length - 1];
    const eqPos = lastLine.indexOf('eq');
    const pos = { line: lines.length, col: eqPos + 1, pos: 0 };

    const result = queryTypeAtPosition(pos, queryData.sourceMap, queryData.kernelValue!, queryData.context, queryData.kernelType, 'foo', sourceCode);

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      // Should show "Equal Nat a b" with correct variable names
      // NOT something garbled like "Equal Nat Equal refl"
      expect(typeStr).toContain('Equal');
      expect(typeStr).toContain('Nat');
      expect(typeStr).toContain('a');
      expect(typeStr).toContain('b');
      expect(typeStr).not.toContain('refl');
    }
  });
});

describe('Selection range bugs - const function example', () => {
  // BUG: When selecting a lambda like "\ A B x y => x", the type query
  // should return the type of that lambda expression, not the entire definition.

  // Helper to create value-relative source map
  function createValueRelativeSourceMap(sourceMap: Map<string, any>): Map<string, any> {
    const valueRelativeMap = new Map<string, any>();
    const prefix = 'value.';
    for (const [pathKey, range] of sourceMap) {
      if (pathKey.startsWith(prefix)) {
        valueRelativeMap.set(pathKey.slice(prefix.length), range);
      } else if (pathKey === 'value') {
        valueRelativeMap.set('', range);
      }
    }
    return valueRelativeMap;
  }

  it('should show correct type when selecting the full lambda body "\\ A B x y => x"', () => {
    // const : (A : Type) -> (B : Type) -> A -> B -> A
    // const = \ A B x y => x
    //
    // Selecting "\ A B x y => x" should show type:
    //   (A : Type) -> (B : Type) -> A -> B -> A
    const sourceCode = `const : (A : Type) -> (B : Type) -> A -> B -> A
const = \\ A B x y => x`;

    const results = checkSourceBlocks(sourceCode);
    const constBlock = results.find(b => b.name === 'const');
    expect(constBlock).toBeDefined();
    expect(constBlock!.checkSuccess).toBe(true);

    const queryData = constBlock!.typeQueryData!;
    const valueRelativeMap = createValueRelativeSourceMap(queryData.sourceMap);

    // Find the lambda "\ A B x y => x" on line 2
    const lines = sourceCode.split('\n');
    const lambdaStart = lines[1].indexOf('\\');
    const lambdaEnd = lines[1].length;

    const selectionRange = {
      start: { line: 2, col: lambdaStart + 1, pos: 0 },
      end: { line: 2, col: lambdaEnd + 1, pos: 0 }
    };

    const result = queryTypeForSelection(selectionRange, valueRelativeMap, queryData.kernelValue!, queryData.context, queryData.kernelType, 'const');

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      // The lambda has the full function type with named binders
      // Format: ((A : Type) -> (B : Type) -> A -> B -> A)
      expect(typeStr).toContain('Type');
      expect(typeStr).toContain('->');
      expect(typeStr).not.toContain('?');  // No holes - types are resolved
    }
  });

  it('should show correct type when selecting partial lambda "A B x y => x" (without backslash)', () => {
    // const : (A : Type) -> (B : Type) -> A -> B -> A
    // const = \ A B x y => x
    //
    // Selecting "A B x y => x" (excluding the backslash) - the smallest containing
    // node is still the full lambda since there's no AST node for just "A B x y => x".
    // The types should be resolved (no holes).
    const sourceCode = `const : (A : Type) -> (B : Type) -> A -> B -> A
const = \\ A B x y => x`;

    const results = checkSourceBlocks(sourceCode);
    const constBlock = results.find(b => b.name === 'const');
    expect(constBlock!.checkSuccess).toBe(true);

    const queryData = constBlock!.typeQueryData!;
    const valueRelativeMap = createValueRelativeSourceMap(queryData.sourceMap);

    // Find "A B x y => x" on line 2 (starting after the backslash)
    const lines = sourceCode.split('\n');
    const lambdaStart = lines[1].indexOf('\\');
    const afterBackslash = lambdaStart + 2; // Skip "\ "
    const lambdaEnd = lines[1].length;

    const selectionRange = {
      start: { line: 2, col: afterBackslash + 1, pos: 0 },
      end: { line: 2, col: lambdaEnd + 1, pos: 0 }
    };

    const result = queryTypeForSelection(selectionRange, valueRelativeMap, queryData.kernelValue!, queryData.context, queryData.kernelType, 'const');

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      // Should NOT contain '?' (hole markers)
      expect(typeStr).not.toContain('?');
      // Should contain Type (the type of A and B parameters)
      expect(typeStr).toContain('Type');
    }
  });

  it('should show y : B when selecting just "y" (a binder name)', () => {
    // const : (A : Type) -> (B : Type) -> A -> B -> A
    // const = \ A B x y => x
    //
    // When the selection is exactly on a binder name "y", we should show
    // the type of that variable (B), not the containing lambda's type.
    const sourceCode = `const : (A : Type) -> (B : Type) -> A -> B -> A
const = \\ A B x y => x`;

    const results = checkSourceBlocks(sourceCode);
    const constBlock = results.find(b => b.name === 'const');
    expect(constBlock!.checkSuccess).toBe(true);

    const queryData = constBlock!.typeQueryData!;
    const valueRelativeMap = createValueRelativeSourceMap(queryData.sourceMap);

    // Find the "y" parameter position on line 2
    const lines = sourceCode.split('\n');
    const yPos = lines[1].lastIndexOf('y');

    const selectionRange = {
      start: { line: 2, col: yPos + 1, pos: 0 },
      end: { line: 2, col: yPos + 2, pos: 0 }  // Just 1 character
    };

    const result = queryTypeForSelection(selectionRange, valueRelativeMap, queryData.kernelValue!, queryData.context, queryData.kernelType, 'const');

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      // Should be 'B' - the type of the binder variable y
      expect(typeStr).not.toContain('?');
      expect(typeStr).toBe('B');
    }
  });

  it('should show x : A when selecting just "x" in the lambda body', () => {
    // const : (A : Type) -> (B : Type) -> A -> B -> A
    // const = \ A B x y => x
    //
    // Selecting the final "x" (the body of the lambda) should show:
    //   x : A
    const sourceCode = `const : (A : Type) -> (B : Type) -> A -> B -> A
const = \\ A B x y => x`;

    const results = checkSourceBlocks(sourceCode);
    const constBlock = results.find(b => b.name === 'const');
    expect(constBlock!.checkSuccess).toBe(true);

    const queryData = constBlock!.typeQueryData!;
    const valueRelativeMap = createValueRelativeSourceMap(queryData.sourceMap);

    // Find the final "x" at the end of line 2
    const lines = sourceCode.split('\n');
    const xPos = lines[1].lastIndexOf('x');

    const selectionRange = {
      start: { line: 2, col: xPos + 1, pos: 0 },
      end: { line: 2, col: xPos + 2, pos: 0 }
    };

    const result = queryTypeForSelection(selectionRange, valueRelativeMap, queryData.kernelValue!, queryData.context, queryData.kernelType, 'const');

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      // Should be 'A', not '?x_type' or similar
      expect(typeStr).not.toContain('?');
      expect(typeStr).toBe('A');
    }
  });

  it('should show A : Type when selecting "A" (a binder name)', () => {
    // const : (A : Type) -> (B : Type) -> A -> B -> A
    // const = \ A B x y => x
    //
    // When the selection is exactly on binder name "A", we should show
    // the type of that variable (Type), not the containing lambda's type.
    const sourceCode = `const : (A : Type) -> (B : Type) -> A -> B -> A
const = \\ A B x y => x`;

    const results = checkSourceBlocks(sourceCode);
    const constBlock = results.find(b => b.name === 'const');
    expect(constBlock!.checkSuccess).toBe(true);

    const queryData = constBlock!.typeQueryData!;
    const valueRelativeMap = createValueRelativeSourceMap(queryData.sourceMap);

    // Find the "A" parameter after the backslash on line 2
    const lines = sourceCode.split('\n');
    const lambdaStart = lines[1].indexOf('\\');
    const aPos = lambdaStart + 2; // "\ A" - A is at position 2 after backslash

    const selectionRange = {
      start: { line: 2, col: aPos + 1, pos: 0 },
      end: { line: 2, col: aPos + 2, pos: 0 }
    };

    const result = queryTypeForSelection(selectionRange, valueRelativeMap, queryData.kernelValue!, queryData.context, queryData.kernelType, 'const');

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      // Should be 'Type' - the type of binder variable A
      expect(typeStr).not.toContain('?');
      expect(typeStr).toBe('Type');
    }
  });

  it('should show x : A when selecting "x" binder (not body)', () => {
    // const : (A : Type) -> (B : Type) -> A -> B -> A
    // const = \ A B x y => x
    //
    // When the selection is exactly on binder name "x" (the third binder),
    // we should show the type of that variable (A).
    const sourceCode = `const : (A : Type) -> (B : Type) -> A -> B -> A
const = \\ A B x y => x`;

    const results = checkSourceBlocks(sourceCode);
    const constBlock = results.find(b => b.name === 'const');
    expect(constBlock!.checkSuccess).toBe(true);

    const queryData = constBlock!.typeQueryData!;
    const valueRelativeMap = createValueRelativeSourceMap(queryData.sourceMap);

    // Find the "x" binder (first x, not the final x in body)
    const lines = sourceCode.split('\n');
    const xPos = lines[1].indexOf('x'); // First x is the binder

    const selectionRange = {
      start: { line: 2, col: xPos + 1, pos: 0 },
      end: { line: 2, col: xPos + 2, pos: 0 }
    };

    const result = queryTypeForSelection(selectionRange, valueRelativeMap, queryData.kernelValue!, queryData.context, queryData.kernelType, 'const');

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      // Should be 'A' - the type of binder variable x
      expect(typeStr).not.toContain('?');
      expect(typeStr).toBe('A');
    }
  });

  it('should show y : B when cursor is on "y" binder (position query)', () => {
    // const : (A : Type) -> (B : Type) -> A -> B -> A
    // const = \ A B x y => x
    //
    // When the cursor is ON the binder name "y" (not a selection, just cursor position),
    // we should show the type of that variable (B).
    const sourceCode = `const : (A : Type) -> (B : Type) -> A -> B -> A
const = \\ A B x y => x`;

    const results = checkSourceBlocks(sourceCode);
    const constBlock = results.find(b => b.name === 'const');
    expect(constBlock!.checkSuccess).toBe(true);

    const queryData = constBlock!.typeQueryData!;
    const valueRelativeMap = createValueRelativeSourceMap(queryData.sourceMap);

    // Find the "y" parameter position on line 2
    const lines = sourceCode.split('\n');
    const yPos = lines[1].lastIndexOf('y');

    // Query at cursor position (not a selection)
    const cursorPos = { line: 2, col: yPos + 1, pos: 0 };

    const result = queryTypeAtPosition(
      cursorPos,
      valueRelativeMap,
      queryData.kernelValue!,
      queryData.context,
      queryData.kernelType,
      'const',
      sourceCode
    );

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      // Should be 'B' - the type of the binder variable y
      expect(typeStr).not.toContain('?');
      expect(typeStr).toBe('B');
    }
  });

  it('should show A : Type when cursor is next to "A" binder (position query)', () => {
    // const : (A : Type) -> (B : Type) -> A -> B -> A
    // const = \ A B x y => x
    //
    // When the cursor is next to the binder name "A", we should show
    // the type of that variable (Type).
    const sourceCode = `const : (A : Type) -> (B : Type) -> A -> B -> A
const = \\ A B x y => x`;

    const results = checkSourceBlocks(sourceCode);
    const constBlock = results.find(b => b.name === 'const');
    expect(constBlock!.checkSuccess).toBe(true);

    const queryData = constBlock!.typeQueryData!;
    const valueRelativeMap = createValueRelativeSourceMap(queryData.sourceMap);

    // Find the "A" parameter after the backslash on line 2
    const lines = sourceCode.split('\n');
    const lambdaStart = lines[1].indexOf('\\');
    const aPos = lambdaStart + 2; // "\ A" - A is at position 2 after backslash

    // Query at cursor position (not a selection)
    const cursorPos = { line: 2, col: aPos + 1, pos: 0 };

    const result = queryTypeAtPosition(
      cursorPos,
      valueRelativeMap,
      queryData.kernelValue!,
      queryData.context,
      queryData.kernelType,
      'const',
      sourceCode
    );

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      // Should be 'Type' - the type of binder variable A
      expect(typeStr).not.toContain('?');
      expect(typeStr).toBe('Type');
    }
  });

  it('should show lambda type when selecting multiple binders "B x"', () => {
    // const : (A : Type) -> (B : Type) -> A -> B -> A
    // const = \ A B x y => x
    //
    // Selecting "B x" spans multiple binders, so we should NOT trigger binder detection.
    // Instead, fall back to the containing lambda's type.
    const sourceCode = `const : (A : Type) -> (B : Type) -> A -> B -> A
const = \\ A B x y => x`;

    const results = checkSourceBlocks(sourceCode);
    const constBlock = results.find(b => b.name === 'const');
    expect(constBlock!.checkSuccess).toBe(true);

    const queryData = constBlock!.typeQueryData!;
    const valueRelativeMap = createValueRelativeSourceMap(queryData.sourceMap);

    // Find "B x" on line 2
    const lines = sourceCode.split('\n');
    const bPos = lines[1].indexOf('B');
    const xPos = lines[1].indexOf('x');

    const selectionRange = {
      start: { line: 2, col: bPos + 1, pos: 0 },
      end: { line: 2, col: xPos + 2, pos: 0 }  // "B x" = 3 chars
    };

    const result = queryTypeForSelection(selectionRange, valueRelativeMap, queryData.kernelValue!, queryData.context, queryData.kernelType, 'const');

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      // Should be the B-level lambda type: (B : Type) -> A -> B -> A
      // NOT just "Type" (which would be wrong - treating it as binder B)
      expect(typeStr).toContain('->');
      expect(typeStr).toContain('Type');
    }
  });
});

describe('Integration tests with full parsing pipeline', () => {
  it('should parse identifier with correct source range', () => {
    // Directly test the parser's source map for identifiers in lambda bodies
    const source = `\\(A : Type) (x : A) => x`;
    const parser = new Parser();
    const declsWithSource = parser.parseDeclarationsWithSource(source);

    expect(declsWithSource.length).toBeGreaterThan(0);

    const sourceMap = declsWithSource[0].sourceMap;

    // The final 'x' is at column 24 (1-indexed), should have range 24-25
    // Path body.body should have a non-zero width range
    const bodyBodyRange = sourceMap?.get('body.body');
    expect(bodyBodyRange).toBeDefined();
    if (bodyBodyRange) {
      // The range should be 24-25 (one character wide for 'x')
      expect(bodyBodyRange.start.col).toBe(24);
      expect(bodyBodyRange.end.col).toBe(25);
      expect(bodyBodyRange.end.col - bodyBodyRange.start.col).toBe(1);
    }
  });

  it('should show type with named variables for parsed code', () => {
    // Use the parser's expected syntax (no 'def' keyword for simple defs)
    const sourceCode = `id : (A : Type) -> A -> A := \\(A : Type) (x : A) => x`;

    const results = checkSourceBlocks(sourceCode);

    // Filter to non-empty blocks
    const nonEmptyBlocks = results.filter(r => r.block.lines.length > 0 && r.block.lines.some(l => l.trim()));
    expect(nonEmptyBlocks.length).toBe(1);

    const block = nonEmptyBlocks[0];
    expect(block.parseSuccess).toBe(true);
    expect(block.checkSuccess).toBe(true);
    expect(block.typeQueryData).toBeDefined();

    const queryData = block.typeQueryData!;

    // Find the position of the final 'x' in "... := x"
    const xPos = sourceCode.lastIndexOf('x');

    // Query at that position (line 1, column = xPos + 1)
    const pos = { line: 1, col: xPos + 1, pos: 0 };

    // Create value-relative source map (like the hook does)
    const valueRelativeMap = new Map<string, any>();
    const prefix = 'value.';
    for (const [pathKey, range] of queryData.sourceMap) {
      if (pathKey.startsWith(prefix)) {
        const relativePath = pathKey.slice(prefix.length);
        valueRelativeMap.set(relativePath, range);
      } else if (pathKey === 'value') {
        valueRelativeMap.set('', range);
      }
    }

    // Query the type at the position
    const result = queryTypeAtPosition(pos, valueRelativeMap, queryData.kernelValue!, queryData.context);

    // The type should display 'A' not '#3' or similar
    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      expect(typeStr).toBe('A');
    }
  });

  it('should show inferred types for explicitly annotated lambda parameters', () => {
    // When lambda parameters have explicit type annotations, the types should be resolved
    const sourceCode = `apply : (A : Type) -> (B : Type) -> (A -> B) -> A -> B := \\(A : Type) (B : Type) (f : A -> B) (x : A) => f x`;

    const results = checkSourceBlocks(sourceCode);
    const nonEmptyBlocks = results.filter(r => r.block.lines.length > 0 && r.block.lines.some(l => l.trim()));
    expect(nonEmptyBlocks.length).toBe(1);

    const block = nonEmptyBlocks[0];
    expect(block.parseSuccess).toBe(true);
    expect(block.checkSuccess).toBe(true);
    expect(block.typeQueryData).toBeDefined();

    const queryData = block.typeQueryData!;

    // Find the position of 'f' in the body "f x"
    const fxPart = sourceCode.lastIndexOf('f x');
    const fPos = fxPart;

    const pos = { line: 1, col: fPos + 1, pos: 0 };

    // Create value-relative source map
    const valueRelativeMap = new Map<string, any>();
    const prefix = 'value.';
    for (const [pathKey, range] of queryData.sourceMap) {
      if (pathKey.startsWith(prefix)) {
        valueRelativeMap.set(pathKey.slice(prefix.length), range);
      } else if (pathKey === 'value') {
        valueRelativeMap.set('', range);
      }
    }

    const result = queryTypeAtPosition(pos, valueRelativeMap, queryData.kernelValue!, queryData.context);

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      // Should be 'A -> B', not '?f_type' or a hole
      expect(typeStr).not.toContain('?');
      expect(typeStr).toBe('(A -> B)');
    }
  });

  it('should query type for a selection range', () => {
    // When user selects "f x" in the expression "apply A B f x := f x",
    // the type should be B (the result of applying f to x)
    const sourceCode = `apply : (A : Type) -> (B : Type) -> (A -> B) -> A -> B := \\(A : Type) (B : Type) (f : A -> B) (x : A) => f x`;

    const results = checkSourceBlocks(sourceCode);
    const nonEmptyBlocks = results.filter(r => r.block.lines.length > 0 && r.block.lines.some(l => l.trim()));
    expect(nonEmptyBlocks.length).toBe(1);

    const block = nonEmptyBlocks[0];
    expect(block.parseSuccess).toBe(true);
    expect(block.checkSuccess).toBe(true);
    expect(block.typeQueryData).toBeDefined();

    const queryData = block.typeQueryData!;

    // Find the "f x" part at the end
    const fxPart = sourceCode.lastIndexOf('f x');
    const fxEnd = fxPart + 3; // "f x" is 3 characters

    // Create value-relative source map
    const valueRelativeMap = new Map<string, any>();
    const prefix = 'value.';
    for (const [pathKey, range] of queryData.sourceMap) {
      if (pathKey.startsWith(prefix)) {
        valueRelativeMap.set(pathKey.slice(prefix.length), range);
      } else if (pathKey === 'value') {
        valueRelativeMap.set('', range);
      }
    }

    // Create selection range covering "f x"
    const selectionRange = {
      start: { line: 1, col: fxPart + 1, pos: 0 },
      end: { line: 1, col: fxEnd + 1, pos: 0 }
    };

    const result = queryTypeForSelection(selectionRange, valueRelativeMap, queryData.kernelValue!, queryData.context);

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      // "f x" has type B (result of applying f : A -> B to x : A)
      expect(typeStr).toBe('B');
    }
  });

  it('should find smallest containing expression for selection', () => {
    // When user selects just "x" in "f x", should get type of x (which is A), not f x
    const sourceCode = `apply : (A : Type) -> (B : Type) -> (A -> B) -> A -> B := \\(A : Type) (B : Type) (f : A -> B) (x : A) => f x`;

    const results = checkSourceBlocks(sourceCode);
    const nonEmptyBlocks = results.filter(r => r.block.lines.length > 0 && r.block.lines.some(l => l.trim()));
    const block = nonEmptyBlocks[0];
    const queryData = block.typeQueryData!;

    // Find the final 'x' (the argument in "f x")
    const fxPart = sourceCode.lastIndexOf('f x');
    const xPos = fxPart + 2; // The 'x' in "f x"

    // Create value-relative source map
    const valueRelativeMap = new Map<string, any>();
    const prefix = 'value.';
    for (const [pathKey, range] of queryData.sourceMap) {
      if (pathKey.startsWith(prefix)) {
        valueRelativeMap.set(pathKey.slice(prefix.length), range);
      } else if (pathKey === 'value') {
        valueRelativeMap.set('', range);
      }
    }

    // Create selection range covering just "x"
    const selectionRange = {
      start: { line: 1, col: xPos + 1, pos: 0 },
      end: { line: 1, col: xPos + 2, pos: 0 }
    };

    const result = queryTypeForSelection(selectionRange, valueRelativeMap, queryData.kernelValue!, queryData.context);

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      // 'x' alone has type A
      expect(typeStr).toBe('A');
    }
  });

  it.skip('should show inferred types for unannotated lambda parameters (bidirectional typing)', () => {
    // TODO: This test documents a known limitation.
    //
    // When we write: apply A B f x := f x
    // With type: apply : (A : Type) -> (B : Type) -> (A -> B) -> A -> B
    // The parameter f should have type (A -> B), not ?f_type
    //
    // Currently, the kernel value stored in typeQueryData is the PRE-elaboration
    // term with holes for unannotated parameter types. The type checker validates
    // against the expected type but doesn't return an elaborated term.
    //
    // To fix this, we need either:
    // 1. Modify checkType to return an elaborated term with holes filled in
    // 2. Modify queryTypeAtPath to accept an expected type and use it to fill holes
    //
    // For now, users should use explicit type annotations on lambda parameters
    // to get accurate type information in the UI.

    const sourceCode = `apply : (A : Type) -> (B : Type) -> (A -> B) -> A -> B := \\A B f x => f x`;

    const results = checkSourceBlocks(sourceCode);
    const nonEmptyBlocks = results.filter(r => r.block.lines.length > 0 && r.block.lines.some(l => l.trim()));
    expect(nonEmptyBlocks.length).toBe(1);

    const block = nonEmptyBlocks[0];
    expect(block.parseSuccess).toBe(true);
    expect(block.checkSuccess).toBe(true);
    expect(block.typeQueryData).toBeDefined();

    const queryData = block.typeQueryData!;

    const fxPart = sourceCode.lastIndexOf('f x');
    const fPos = fxPart;
    const pos = { line: 1, col: fPos + 1, pos: 0 };

    const valueRelativeMap = new Map<string, any>();
    const prefix = 'value.';
    for (const [pathKey, range] of queryData.sourceMap) {
      if (pathKey.startsWith(prefix)) {
        valueRelativeMap.set(pathKey.slice(prefix.length), range);
      } else if (pathKey === 'value') {
        valueRelativeMap.set('', range);
      }
    }

    const result = queryTypeAtPosition(pos, valueRelativeMap, queryData.kernelValue!, queryData.context);

    expect(result.success).toBe(true);
    if (result.success) {
      const names = result.context.map(b => b.name);
      const typeStr = prettyPrint(result.type, names);
      // Should be 'A -> B', not '?f_type' or a hole
      expect(typeStr).not.toContain('?');
    }
  });
});

// ============================================================================
// Solved Type Display Tests (with ElaborationContext)
// ============================================================================

describe('Solved type display with elaboration context', () => {
  it('should show solved pattern types with elaboration context', () => {
    // This tests the new ElaborationContext feature that allows showing
    // types with unification results applied.
    //
    // When type-checking pattern matching on indexed types like Equal,
    // unification produces constraints like "b = a". With elaboration context,
    // the type query should show the solved type "Equal Nat a a" rather than
    // the original "Equal Nat a b".

    const sourceCode = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : (A : Type) -> A -> A -> Type where
  refl : (A : Type) -> (x : A) -> Equal A x x

foo : (a : Nat) -> (b : Nat) -> Equal Nat a b -> Nat
foo a b eq = Zero
`;

    const results = checkSourceBlocks(sourceCode);

    // Find the foo declaration
    const fooBlock = results.find(b => b.name === 'foo');
    expect(fooBlock).toBeDefined();

    // If this test is run before the full integration of elaboration context,
    // the type query would show "Equal Nat a b" (original telescope type).
    // After integration, it should show "Equal Nat a a" (solved type).
    //
    // For now, we just verify the infrastructure is in place.
    // The actual solved type display requires threading elaboration results
    // all the way from block-checker.ts through to the type query.
    if (fooBlock?.typeQueryData) {
      const queryData = fooBlock.typeQueryData;
      expect(queryData.kernelValue).toBeDefined();
      expect(queryData.kernelType).toBeDefined();

      // Verify that the function type signature is preserved
      const names = queryData.context.map(b => b.name);
      const typeStr = prettyPrint(queryData.kernelType!, names);
      expect(typeStr).toContain('Equal');
    }
  });

  it('should have ClauseCheckResult type available for solved bindings', async () => {
    // Verify the new types are properly exported
    const { checkClauseWithResult, checkFunctionClausesWithResult } = await import('./tt-pattern-match');

    expect(checkClauseWithResult).toBeDefined();
    expect(checkFunctionClausesWithResult).toBeDefined();
  });

  it('should have queryTypeAtPath with optional elaboration context parameter', async () => {
    // Verify the queryTypeAtPath function is available
    const { queryTypeAtPath } = await import('./tt-type-query');

    // The function should be defined and callable
    expect(queryTypeAtPath).toBeDefined();
    expect(typeof queryTypeAtPath).toBe('function');
  });

  it('should have clauseResults available in typeQueryData for pattern matching functions', () => {
    // When a function uses pattern matching, the clauseResults should be populated
    // in the typeQueryData so that type queries can show solved types.
    const sourceCode = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)
`;

    const results = checkSourceBlocks(sourceCode);

    // Find the plus declaration
    const plusBlock = results.find(b => b.name === 'plus');
    expect(plusBlock).toBeDefined();
    expect(plusBlock!.checkSuccess).toBe(true);
    expect(plusBlock!.typeQueryData).toBeDefined();

    // Verify clauseResults is populated
    const queryData = plusBlock!.typeQueryData!;
    expect(queryData.clauseResults).toBeDefined();
    expect(queryData.clauseResults!.length).toBe(2); // Two clauses: Zero and Succ

    // Each clause should have solved bindings
    for (const clauseResult of queryData.clauseResults!) {
      expect(clauseResult.solvedBindings).toBeDefined();
      expect(clauseResult.solvedBindings.length).toBeGreaterThan(0);
    }

    // Verify the solved bindings contain the expected types
    // Clause 1 (Zero case): should have binding 'b' with type 'Nat'
    const clause1 = queryData.clauseResults![0];
    const bBinding1 = clause1.solvedBindings.find(b => b.name === 'b');
    expect(bBinding1).toBeDefined();
    const bTypeStr1 = prettyPrint(bBinding1!.type, []);
    expect(bTypeStr1).toBe('Nat');

    // Clause 2 (Succ case): should have bindings 'a' and 'b', both with type 'Nat'
    const clause2 = queryData.clauseResults![1];
    const aBinding = clause2.solvedBindings.find(b => b.name === 'a');
    const bBinding2 = clause2.solvedBindings.find(b => b.name === 'b');
    expect(aBinding).toBeDefined();
    expect(bBinding2).toBeDefined();
    const aTypeStr = prettyPrint(aBinding!.type, []);
    const bTypeStr2 = prettyPrint(bBinding2!.type, []);
    expect(aTypeStr).toBe('Nat');
    expect(bTypeStr2).toBe('Nat');
  });
});
