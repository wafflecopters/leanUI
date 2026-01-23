/**
 * Tests for structural recursion checking in recursion.ts
 *
 * These tests verify:
 * 1. collectPatternVars - collecting variable names from patterns
 * 2. buildStructurallySmallerMap - building the smaller-than relation
 * 3. extractAppSpineFromParentStack - extracting args from parent stack
 * 4. visitTermWithParentStack - visiting terms with parent context
 * 5. checkRecursiveCallSite - checking if a call is structurally decreasing
 * 6. findRecursiveCallSites - finding all recursive calls in a term
 * 7. checkClauseRecursion - checking recursion for a clause
 * 8. checkStructuralRecursion - top-level check
 */

import { describe, test, expect } from "vitest";
import { TTKPattern, TTKTerm, TTKClause, mkVar, mkConst, mkApp, mkLambda, mkType } from "./kernel";
import { fieldSeg } from "../types/source-position";
import {
  collectPatternVars,
  buildStructurallySmallerMap,
  extractAppSpineFromParentStack,
  visitTermWithParentStack,
  checkRecursiveCallSite,
  findRecursiveCallSites,
  checkClauseRecursion,
  checkStructuralRecursion,
  StructurallySmallerMap,
} from "./recursion";

// ============================================================================
// Helper Functions
// ============================================================================

const mkPVar = (name: string): TTKPattern => ({ tag: 'PVar', name });
const mkPWild = (name: string): TTKPattern => ({ tag: 'PWild', name });
const mkPCtor = (name: string, args: TTKPattern[]): TTKPattern => ({ tag: 'PCtor', name, args });

// ============================================================================
// Tests for collectPatternVars
// ============================================================================

describe('collectPatternVars', () => {
  test('single PVar pattern', () => {
    const patterns = [mkPVar('n')];
    const result = collectPatternVars(patterns);
    expect(result).toEqual(['n']);
  });

  test('single PWild pattern', () => {
    const patterns = [mkPWild('_w0')];
    const result = collectPatternVars(patterns);
    expect(result).toEqual(['_w0']);
  });

  test('multiple PVar patterns', () => {
    const patterns = [mkPVar('x'), mkPVar('y'), mkPVar('z')];
    const result = collectPatternVars(patterns);
    expect(result).toEqual(['x', 'y', 'z']);
  });

  test('PCtor with no args', () => {
    const patterns = [mkPCtor('Zero', [])];
    const result = collectPatternVars(patterns);
    expect(result).toEqual([]);
  });

  test('PCtor with PVar args', () => {
    // Pattern: (Succ n)
    const patterns = [mkPCtor('Succ', [mkPVar('n')])];
    const result = collectPatternVars(patterns);
    expect(result).toEqual(['n']);
  });

  test('nested PCtor patterns', () => {
    // Pattern: (Succ (Succ n))
    const patterns = [mkPCtor('Succ', [mkPCtor('Succ', [mkPVar('n')])])];
    const result = collectPatternVars(patterns);
    expect(result).toEqual(['n']);
  });

  test('mixed patterns - multiple args', () => {
    // Patterns: (Succ n) m
    const patterns = [mkPCtor('Succ', [mkPVar('n')]), mkPVar('m')];
    const result = collectPatternVars(patterns);
    expect(result).toEqual(['n', 'm']);
  });

  test('PCtor with multiple args', () => {
    // Pattern: (Cons h t)
    const patterns = [mkPCtor('Cons', [mkPVar('h'), mkPVar('t')])];
    const result = collectPatternVars(patterns);
    expect(result).toEqual(['h', 't']);
  });
});

// ============================================================================
// Tests for buildStructurallySmallerMap
// ============================================================================

describe('buildStructurallySmallerMap', () => {
  test('single PVar at top level - not smaller than anything', () => {
    // Pattern: n
    // n is NOT inside a PCtor, so it's not smaller than anything
    const patterns = [mkPVar('n')];
    const result = buildStructurallySmallerMap(patterns);
    expect(result.size).toBe(0);
  });

  test('single Zero PCtor - no vars, no smaller relations', () => {
    const patterns = [mkPCtor('Zero', [])];
    const result = buildStructurallySmallerMap(patterns);
    expect(result.size).toBe(0);
  });

  test('(Succ n) - n is smaller than position 0', () => {
    // Pattern: (Succ n)
    // Binding order: [n]
    // Total vars = 1
    // n at binding position 0 => De Bruijn index = 1 - 1 - 0 = 0
    // n is inside PCtor at pattern position 0
    // So: {0 -> 0}
    const patterns = [mkPCtor('Succ', [mkPVar('n')])];
    const result = buildStructurallySmallerMap(patterns);

    expect(result.size).toBe(1);
    expect(result.get(0)).toBe(0);
  });

  test('(Succ n) m - n is smaller than position 0, m is not smaller', () => {
    // Patterns: (Succ n), m
    // Binding order: [n, m]
    // Total vars = 2
    // n at binding position 0 => De Bruijn index = 2 - 1 - 0 = 1
    // m at binding position 1 => De Bruijn index = 2 - 1 - 1 = 0
    // n is inside PCtor at pattern position 0 => {1 -> 0}
    // m is at top level (position 1), not inside PCtor => not in map
    const patterns = [mkPCtor('Succ', [mkPVar('n')]), mkPVar('m')];
    const result = buildStructurallySmallerMap(patterns);

    expect(result.size).toBe(1);
    expect(result.get(1)).toBe(0);  // n (index 1) is smaller than position 0
    expect(result.has(0)).toBe(false);  // m (index 0) is not smaller
  });

  test('n (Succ m) - n is not smaller, m is smaller than position 1', () => {
    // Patterns: n, (Succ m)
    // Binding order: [n, m]
    // Total vars = 2
    // n at binding position 0 => De Bruijn index = 2 - 1 - 0 = 1
    // m at binding position 1 => De Bruijn index = 2 - 1 - 1 = 0
    // n is at top level (position 0), not inside PCtor
    // m is inside PCtor at pattern position 1 => {0 -> 1}
    const patterns = [mkPVar('n'), mkPCtor('Succ', [mkPVar('m')])];
    const result = buildStructurallySmallerMap(patterns);

    expect(result.size).toBe(1);
    expect(result.has(1)).toBe(false);  // n (index 1) is not smaller
    expect(result.get(0)).toBe(1);  // m (index 0) is smaller than position 1
  });

  test('(Succ (Succ n)) - n is smaller than position 0 (nested)', () => {
    // Pattern: (Succ (Succ n))
    // Binding order: [n]
    // Total vars = 1
    // n at binding position 0 => De Bruijn index = 0
    // n is inside a nested PCtor, but still under position 0
    const patterns = [mkPCtor('Succ', [mkPCtor('Succ', [mkPVar('n')])])];
    const result = buildStructurallySmallerMap(patterns);

    expect(result.size).toBe(1);
    expect(result.get(0)).toBe(0);  // n (index 0) is smaller than position 0
  });

  test('(Cons h t) - both h and t smaller than position 0', () => {
    // Pattern: (Cons h t)
    // Binding order: [h, t]
    // Total vars = 2
    // h at binding position 0 => De Bruijn index = 1
    // t at binding position 1 => De Bruijn index = 0
    // Both inside PCtor at position 0
    const patterns = [mkPCtor('Cons', [mkPVar('h'), mkPVar('t')])];
    const result = buildStructurallySmallerMap(patterns);

    expect(result.size).toBe(2);
    expect(result.get(1)).toBe(0);  // h (index 1) is smaller than position 0
    expect(result.get(0)).toBe(0);  // t (index 0) is smaller than position 0
  });

  test('Zero m - neither is smaller (Zero has no vars, m is top-level)', () => {
    // Patterns: Zero, m
    // Zero is PCtor with no args
    // m is PVar at top level
    const patterns = [mkPCtor('Zero', []), mkPVar('m')];
    const result = buildStructurallySmallerMap(patterns);

    expect(result.size).toBe(0);
  });

  test('three patterns with one PCtor in the middle', () => {
    // Patterns: x, (Succ n), y
    // Binding order: [x, n, y]
    // Total vars = 3
    // x at pos 0 => index 2
    // n at pos 1 => index 1
    // y at pos 2 => index 0
    // Only n is inside PCtor at pattern position 1
    const patterns = [mkPVar('x'), mkPCtor('Succ', [mkPVar('n')]), mkPVar('y')];
    const result = buildStructurallySmallerMap(patterns);

    expect(result.size).toBe(1);
    expect(result.get(1)).toBe(1);  // n (index 1) is smaller than position 1
  });
});

// ============================================================================
// Tests for extractAppSpineFromParentStack
// ============================================================================

describe('extractAppSpineFromParentStack', () => {
  test('empty stack returns null', () => {
    const f = mkConst('f');
    const result = extractAppSpineFromParentStack(f, []);
    expect(result).toBe(null);
  });

  test('non-App parent returns null', () => {
    const f = mkConst('f');
    const parentStack = [mkConst('Nat')];
    const result = extractAppSpineFromParentStack(f, parentStack);
    expect(result).toBe(null);
  });

  test('single App parent where current is fn', () => {
    // If current is Const "f" and parent is App(f, arg1)
    // Then args should be [arg1]
    const f = mkConst('f');
    const arg1 = mkVar(0);
    const parentApp: TTKTerm = { tag: 'App', fn: f, arg: arg1 };
    const result = extractAppSpineFromParentStack(f, [parentApp]);

    expect(result).toEqual([arg1]);
  });

  test('single App parent where current is arg returns null', () => {
    // If current is Const "f" but it's in the arg position of App(g, f)
    // Then this is NOT an App spine for f
    const f = mkConst('f');
    const g = mkConst('g');
    const parentApp: TTKTerm = { tag: 'App', fn: g, arg: f };
    const result = extractAppSpineFromParentStack(f, [parentApp]);

    expect(result).toBe(null);
  });

  test('multiple App parents form spine', () => {
    // Current: Const "f"
    // Tree: App(App(f, arg1), arg2)
    // Stack: [outerApp, innerApp]
    const f = mkConst('f');
    const arg1 = mkVar(0);
    const arg2 = mkVar(1);
    const innerApp: TTKTerm = { tag: 'App', fn: f, arg: arg1 };
    const outerApp: TTKTerm = { tag: 'App', fn: innerApp, arg: arg2 };

    const parentStack = [outerApp, innerApp];
    const result = extractAppSpineFromParentStack(f, parentStack);

    expect(result).toEqual([arg1, arg2]);
  });

  test('App chain stops when current is in arg position', () => {
    // Tree: App(Succ, App(f, x)) - f is applied to x, but App(f,x) is arg of outer
    // Current is f, parent is App(f, x), grandparent is App(Succ, App(f,x))
    // f is fn of parent, so collect x
    // parent is ARG of grandparent (not fn), so stop
    const f = mkConst('f');
    const succ = mkConst('Succ');
    const x = mkVar(0);
    const innerApp: TTKTerm = { tag: 'App', fn: f, arg: x };
    const outerApp: TTKTerm = { tag: 'App', fn: succ, arg: innerApp };

    const parentStack = [outerApp, innerApp];
    const result = extractAppSpineFromParentStack(f, parentStack);

    // Should only collect x, not continue through outerApp
    expect(result).toEqual([x]);
  });

  test('nested application Succ (Succ (f x))', () => {
    // Tree: App(Succ, App(Succ, App(f, x)))
    // f is only applied to x
    const f = mkConst('f');
    const succ = mkConst('Succ');
    const x = mkVar(0);
    const innerApp: TTKTerm = { tag: 'App', fn: f, arg: x };
    const middleApp: TTKTerm = { tag: 'App', fn: succ, arg: innerApp };
    const outerApp: TTKTerm = { tag: 'App', fn: succ, arg: middleApp };

    const parentStack = [outerApp, middleApp, innerApp];
    const result = extractAppSpineFromParentStack(f, parentStack);

    expect(result).toEqual([x]);
  });
});

// ============================================================================
// Tests for visitTermWithParentStack
// ============================================================================

describe('visitTermWithParentStack', () => {
  test('visits simple Const', () => {
    const term = mkConst('x');
    const visited: { term: TTKTerm; stackLen: number }[] = [];

    visitTermWithParentStack(term, (t, stack) => {
      visited.push({ term: t, stackLen: stack.length });
    });

    expect(visited.length).toBe(1);
    expect(visited[0].term).toEqual(term);
    expect(visited[0].stackLen).toBe(0);
  });

  test('visits App and its children with correct stack', () => {
    const fn = mkConst('f');
    const arg = mkConst('x');
    const app = mkApp(fn, arg);
    const visited: { term: TTKTerm; stackLen: number }[] = [];

    visitTermWithParentStack(app, (t, stack) => {
      visited.push({ term: t, stackLen: stack.length });
    });

    // Should visit: app (stack 0), fn (stack 1), arg (stack 1)
    expect(visited.length).toBe(3);
    expect(visited[0].term).toEqual(app);
    expect(visited[0].stackLen).toBe(0);
    expect(visited[1].term).toEqual(fn);
    expect(visited[1].stackLen).toBe(1);
    expect(visited[2].term).toEqual(arg);
    expect(visited[2].stackLen).toBe(1);
  });

  test('parent stack contains correct parents', () => {
    const fn = mkConst('f');
    const arg = mkConst('x');
    const app = mkApp(fn, arg);
    let fnStack: TTKTerm[] = [];

    visitTermWithParentStack(app, (t, stack) => {
      if (t.tag === 'Const' && t.name === 'f') {
        fnStack = [...stack];
      }
    });

    expect(fnStack.length).toBe(1);
    expect(fnStack[0]).toEqual(app);
  });

  test('deeply nested term has correct stack depth', () => {
    // Build: App(App(App(f, a), b), c)
    const f = mkConst('f');
    const a = mkConst('a');
    const b = mkConst('b');
    const c = mkConst('c');
    const app1 = mkApp(f, a);
    const app2 = mkApp(app1, b);
    const app3 = mkApp(app2, c);

    let fStackLen = 0;
    visitTermWithParentStack(app3, (t, stack) => {
      if (t.tag === 'Const' && t.name === 'f') {
        fStackLen = stack.length;
      }
    });

    // f is under app3 -> app2 -> app1 -> f
    expect(fStackLen).toBe(3);
  });
});

// ============================================================================
// Tests for checkRecursiveCallSite
// ============================================================================

describe('checkRecursiveCallSite', () => {
  test('valid call with decreasing arg at position 0', () => {
    // Arg is Var(1), which is smaller than position 0
    const smallerMap: StructurallySmallerMap = new Map([[1, 0]]);
    const args = [mkVar(1)];
    const contextNames = ['m', 'n'];  // index 0 = m, index 1 = n

    const result = checkRecursiveCallSite(args, smallerMap, contextNames);

    expect(result.isValid).toBe(true);
    expect(result.decreasingArgPosition).toBe(0);
  });

  test('valid call with decreasing arg at position 1', () => {
    // Args: [Var(1), Var(0)] where Var(0) is smaller than position 1
    const smallerMap: StructurallySmallerMap = new Map([[0, 1]]);
    const args = [mkVar(1), mkVar(0)];
    const contextNames = ['m', 'n'];

    const result = checkRecursiveCallSite(args, smallerMap, contextNames);

    expect(result.isValid).toBe(true);
    expect(result.decreasingArgPosition).toBe(1);
  });

  test('invalid call - no decreasing arg', () => {
    // Var(0) is not smaller than position 0
    const smallerMap: StructurallySmallerMap = new Map();  // empty - nothing is smaller
    const args = [mkVar(0)];
    const contextNames = ['n'];

    const result = checkRecursiveCallSite(args, smallerMap, contextNames);

    expect(result.isValid).toBe(false);
    expect(result.error).toBeDefined();
  });

  test('invalid call - arg is at wrong position', () => {
    // Var(1) is smaller than position 0, but appears at position 1
    const smallerMap: StructurallySmallerMap = new Map([[1, 0]]);
    const args = [mkVar(0), mkVar(1)];  // Var(1) at position 1, but smaller than 0
    const contextNames = ['m', 'n'];

    const result = checkRecursiveCallSite(args, smallerMap, contextNames);

    expect(result.isValid).toBe(false);
  });

  test('invalid call - arg is not a Var', () => {
    const smallerMap: StructurallySmallerMap = new Map([[0, 0]]);
    const args = [mkConst('Zero')];  // Const, not Var
    const contextNames = ['n'];

    const result = checkRecursiveCallSite(args, smallerMap, contextNames);

    expect(result.isValid).toBe(false);
  });

  test('no args is invalid', () => {
    const smallerMap: StructurallySmallerMap = new Map([[0, 0]]);
    const args: TTKTerm[] = [];
    const contextNames: string[] = [];

    const result = checkRecursiveCallSite(args, smallerMap, contextNames);

    expect(result.isValid).toBe(false);
  });
});

// ============================================================================
// Tests for findRecursiveCallSites
// ============================================================================

describe('findRecursiveCallSites', () => {
  test('no recursive calls', () => {
    const rhs = mkConst('Zero');
    const result = findRecursiveCallSites(rhs, 'myFunc');
    expect(result.length).toBe(0);
  });

  test('finds recursive call with one arg', () => {
    // rhs = (myFunc x) = App(myFunc, x)
    const rhs = mkApp(mkConst('myFunc'), mkVar(0));
    const result = findRecursiveCallSites(rhs, 'myFunc');

    expect(result.length).toBe(1);
    expect(result[0].args).toEqual([mkVar(0)]);
  });

  test('finds recursive call with two args', () => {
    // rhs = ((myFunc x) y) = App(App(myFunc, x), y)
    const rhs = mkApp(mkApp(mkConst('myFunc'), mkVar(0)), mkVar(1));
    const result = findRecursiveCallSites(rhs, 'myFunc');

    expect(result.length).toBe(1);
    expect(result[0].args).toEqual([mkVar(0), mkVar(1)]);
  });

  test('finds bare Const reference (zero args)', () => {
    // rhs = myFunc (just the constant, not applied)
    const rhs = mkConst('myFunc');
    const result = findRecursiveCallSites(rhs, 'myFunc');

    expect(result.length).toBe(1);
    expect(result[0].args).toEqual([]);
  });

  test('finds multiple recursive calls', () => {
    // rhs = App(App(Succ, (myFunc x)), (myFunc y))
    const call1 = mkApp(mkConst('myFunc'), mkVar(0));
    const call2 = mkApp(mkConst('myFunc'), mkVar(1));
    const rhs = mkApp(mkApp(mkConst('Succ'), call1), call2);

    const result = findRecursiveCallSites(rhs, 'myFunc');

    expect(result.length).toBe(2);
  });

  test('ignores non-recursive calls', () => {
    // rhs = (otherFunc x) - not a recursive call
    const rhs = mkApp(mkConst('otherFunc'), mkVar(0));
    const result = findRecursiveCallSites(rhs, 'myFunc');

    expect(result.length).toBe(0);
  });

  test('tracks correct index path for simple call', () => {
    // rhs = (myFunc x) = App(myFunc, x)
    // myFunc is at path ['fn']
    const rhs = mkApp(mkConst('myFunc'), mkVar(0));
    const result = findRecursiveCallSites(rhs, 'myFunc');

    expect(result.length).toBe(1);
    expect(result[0].indexPath).toEqual([fieldSeg('fn')]);
  });

  test('tracks correct index path for nested call', () => {
    // rhs = Succ (myFunc x) = App(Succ, App(myFunc, x))
    // myFunc is at path ['arg', 'fn']
    const call = mkApp(mkConst('myFunc'), mkVar(0));
    const rhs = mkApp(mkConst('Succ'), call);
    const result = findRecursiveCallSites(rhs, 'myFunc');

    expect(result.length).toBe(1);
    expect(result[0].indexPath).toEqual([fieldSeg('arg'), fieldSeg('fn')]);
  });

  test('tracks correct index paths for multiple calls', () => {
    // rhs = App(App(add, (myFunc x)), (myFunc y))
    // First call (myFunc x) is at ['fn', 'arg', 'fn']
    // Second call (myFunc y) is at ['arg', 'fn']
    const call1 = mkApp(mkConst('myFunc'), mkVar(0));
    const call2 = mkApp(mkConst('myFunc'), mkVar(1));
    const rhs = mkApp(mkApp(mkConst('add'), call1), call2);
    const result = findRecursiveCallSites(rhs, 'myFunc');

    expect(result.length).toBe(2);
    // The calls are visited in pre-order (fn before arg)
    expect(result[0].indexPath).toEqual([fieldSeg('fn'), fieldSeg('arg'), fieldSeg('fn')]);
    expect(result[1].indexPath).toEqual([fieldSeg('arg'), fieldSeg('fn')]);
  });
});

// ============================================================================
// Tests for checkClauseRecursion
// ============================================================================

describe('checkClauseRecursion', () => {
  test('non-recursive clause is valid', () => {
    // | Zero => Zero
    const clause: TTKClause = {
      patterns: [mkPCtor('Zero', [])],
      rhs: mkConst('Zero'),
    };

    const result = checkClauseRecursion(clause, 0, 'myFunc');

    expect(result.isValid).toBe(true);
    expect(result.callSites.length).toBe(0);
    expect(result.errors.length).toBe(0);
  });

  test('valid recursive clause with decreasing arg', () => {
    // | (Succ n) => (myFunc n)
    // n has De Bruijn index 0, smaller than position 0
    const clause: TTKClause = {
      patterns: [mkPCtor('Succ', [mkPVar('n')])],
      rhs: mkApp(mkConst('myFunc'), mkVar(0)),
      contextNames: ['n'],
    };

    const result = checkClauseRecursion(clause, 0, 'myFunc');

    expect(result.isValid).toBe(true);
    expect(result.callSites.length).toBe(1);
    expect(result.errors.length).toBe(0);
  });

  test('invalid recursive clause - no decreasing arg', () => {
    // | n => (myFunc n)
    // n is at top level (PVar), not smaller than anything
    const clause: TTKClause = {
      patterns: [mkPVar('n')],
      rhs: mkApp(mkConst('myFunc'), mkVar(0)),
      contextNames: ['n'],
    };

    const result = checkClauseRecursion(clause, 0, 'myFunc');

    expect(result.isValid).toBe(false);
    expect(result.callSites.length).toBe(1);
    expect(result.errors.length).toBe(1);
  });

  test('error includes rhsPath to call site', () => {
    // | n => Succ (bad n)
    // The bad call is at rhs path ['arg', 'fn']
    const clause: TTKClause = {
      patterns: [mkPVar('n')],
      rhs: mkApp(mkConst('Succ'), mkApp(mkConst('bad'), mkVar(0))),
      contextNames: ['n'],
    };

    const result = checkClauseRecursion(clause, 0, 'bad');

    expect(result.isValid).toBe(false);
    expect(result.errors.length).toBe(1);
    expect(result.errors[0].rhsPath).toEqual([fieldSeg('arg'), fieldSeg('fn')]);
    expect(result.errors[0].message).toContain('not structurally decreasing');
  });

  test('two arg function - valid recursion on first arg', () => {
    // add : Nat -> Nat -> Nat
    // | (Succ n) m => Succ (add n m)
    // n has index 1 (bound first), m has index 0 (bound second)
    // n is smaller than position 0
    const clause: TTKClause = {
      patterns: [mkPCtor('Succ', [mkPVar('n')]), mkPVar('m')],
      rhs: mkApp(mkConst('Succ'), mkApp(mkApp(mkConst('add'), mkVar(1)), mkVar(0))),
      contextNames: ['m', 'n'],  // De Bruijn order: index 0 first
    };

    const result = checkClauseRecursion(clause, 0, 'add');

    expect(result.isValid).toBe(true);
    expect(result.callSites.length).toBe(1);
  });

  test('two arg function - valid recursion on second arg', () => {
    // add2 : Nat -> Nat -> Nat
    // | n (Succ m) => Succ (add2 n m)
    // n has index 1, m has index 0
    // m is smaller than position 1
    const clause: TTKClause = {
      patterns: [mkPVar('n'), mkPCtor('Succ', [mkPVar('m')])],
      rhs: mkApp(mkConst('Succ'), mkApp(mkApp(mkConst('add2'), mkVar(1)), mkVar(0))),
      contextNames: ['m', 'n'],
    };

    const result = checkClauseRecursion(clause, 0, 'add2');

    expect(result.isValid).toBe(true);
    expect(result.callSites.length).toBe(1);
  });

  test('invalid - recursion with args swapped', () => {
    // | (Succ n) m => (add m n)  -- args swapped!
    // n (index 1) is smaller than position 0
    // But in call: position 0 has m (index 0), position 1 has n (index 1)
    // n at position 1 is NOT smaller than position 1 (it's smaller than 0)
    // m at position 0 is NOT smaller than position 0
    const clause: TTKClause = {
      patterns: [mkPCtor('Succ', [mkPVar('n')]), mkPVar('m')],
      rhs: mkApp(mkApp(mkConst('add'), mkVar(0)), mkVar(1)),  // (add m n)
      contextNames: ['m', 'n'],
    };

    const result = checkClauseRecursion(clause, 0, 'add');

    expect(result.isValid).toBe(false);
    expect(result.errors.length).toBe(1);
  });
});

// ============================================================================
// Tests for checkStructuralRecursion (top-level)
// ============================================================================

describe('checkStructuralRecursion', () => {
  test('valid function with multiple clauses', () => {
    // pred : Nat -> Nat
    // | Zero => Zero
    // | (Succ n) => n
    const clauses: TTKClause[] = [
      {
        patterns: [mkPCtor('Zero', [])],
        rhs: mkConst('Zero'),
      },
      {
        patterns: [mkPCtor('Succ', [mkPVar('n')])],
        rhs: mkVar(0),  // n
        contextNames: ['n'],
      },
    ];

    const result = checkStructuralRecursion('pred', clauses);

    expect(result.isValid).toBe(true);
    expect(result.errors.length).toBe(0);
  });

  test('valid recursive function', () => {
    // double : Nat -> Nat
    // | Zero => Zero
    // | (Succ n) => Succ (Succ (double n))
    const clauses: TTKClause[] = [
      {
        patterns: [mkPCtor('Zero', [])],
        rhs: mkConst('Zero'),
      },
      {
        patterns: [mkPCtor('Succ', [mkPVar('n')])],
        rhs: mkApp(mkConst('Succ'), mkApp(mkConst('Succ'), mkApp(mkConst('double'), mkVar(0)))),
        contextNames: ['n'],
      },
    ];

    const result = checkStructuralRecursion('double', clauses);

    expect(result.isValid).toBe(true);
    expect(result.errors.length).toBe(0);
  });

  test('invalid non-decreasing recursion', () => {
    // bad : Nat -> Nat
    // | n => bad n
    const clauses: TTKClause[] = [
      {
        patterns: [mkPVar('n')],
        rhs: mkApp(mkConst('bad'), mkVar(0)),
        contextNames: ['n'],
      },
    ];

    const result = checkStructuralRecursion('bad', clauses);

    expect(result.isValid).toBe(false);
    expect(result.errors.length).toBe(1);
  });

  test('invalid - multiple bad calls in one clause', () => {
    // bad2 : Nat -> Nat
    // | n => add (bad2 n) (bad2 n)
    const call1 = mkApp(mkConst('bad2'), mkVar(0));
    const call2 = mkApp(mkConst('bad2'), mkVar(0));
    const clauses: TTKClause[] = [
      {
        patterns: [mkPVar('n')],
        rhs: mkApp(mkApp(mkConst('add'), call1), call2),
        contextNames: ['n'],
      },
    ];

    const result = checkStructuralRecursion('bad2', clauses);

    expect(result.isValid).toBe(false);
    expect(result.errors.length).toBe(2);  // Two bad calls
  });

  test('one valid clause, one invalid clause', () => {
    // mixed : Nat -> Nat
    // | Zero => Zero
    // | n => mixed n  -- invalid
    const clauses: TTKClause[] = [
      {
        patterns: [mkPCtor('Zero', [])],
        rhs: mkConst('Zero'),
      },
      {
        patterns: [mkPVar('n')],
        rhs: mkApp(mkConst('mixed'), mkVar(0)),
        contextNames: ['n'],
      },
    ];

    const result = checkStructuralRecursion('mixed', clauses);

    expect(result.isValid).toBe(false);
    expect(result.clauseResults[0].isValid).toBe(true);
    expect(result.clauseResults[1].isValid).toBe(false);
  });

  test('complex valid recursion - add function', () => {
    // add : Nat -> Nat -> Nat
    // | Zero y => y
    // | (Succ x) y => Succ (add x y)
    const clauses: TTKClause[] = [
      {
        patterns: [mkPCtor('Zero', []), mkPVar('y')],
        rhs: mkVar(0),  // y
        contextNames: ['y'],
      },
      {
        patterns: [mkPCtor('Succ', [mkPVar('x')]), mkPVar('y')],
        rhs: mkApp(mkConst('Succ'), mkApp(mkApp(mkConst('add'), mkVar(1)), mkVar(0))),
        contextNames: ['y', 'x'],  // x=index1, y=index0
      },
    ];

    const result = checkStructuralRecursion('add', clauses);

    expect(result.isValid).toBe(true);
  });
});

// ============================================================================
// Integration Tests for Error Source Position
// ============================================================================

import { compileSource } from '../test-utils';
import { serializeIndexPath, ElabMap, SourceMap, SourceRange } from '../types/source-position';

describe('Recursion Error Source Position', () => {
  test('recursion error has valid error path through elabMap and sourceMap', () => {
    const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

bad : Nat -> Nat
bad n = bad n`;

    const results = compileSource(source);

    // Find the 'bad' declaration
    const badResult = results.find(r => r.name === 'bad');
    expect(badResult).toBeDefined();

    // It should fail due to non-structural recursion
    expect(badResult!.checkSuccess).toBe(false);
    expect(badResult!.checkErrors.length).toBeGreaterThan(0);
    expect(badResult!.checkErrors[0].message).toContain('not structurally decreasing');

    // Get the declaration details
    const badDecl = badResult!.declarations.find(d => d.name === 'bad');
    expect(badDecl).toBeDefined();

    // Check that elabMap and sourceMap exist
    expect(badDecl!.elabMap).toBeDefined();
    expect(badDecl!.sourceMap).toBeDefined();

    // Get the error path from the TCEnvError
    const errorPath = badDecl!.checkErrors[0].env.indexPath;
    const errorPathStr = serializeIndexPath(errorPath);

    // Try progressively shorter paths like mapErrorPathToSourceRange does
    let currentPath = errorPath;
    let foundMapping = false;
    while (currentPath.length > 0 && !foundMapping) {
      const pathStr = serializeIndexPath(currentPath);
      const surfPath = badDecl!.elabMap!.get(pathStr);
      if (surfPath) {
        const range = badDecl!.sourceMap!.get(surfPath);
        if (range) foundMapping = true;
      }
      currentPath = currentPath.slice(0, -1);
    }

    // The error path should eventually find a mapping
    expect(foundMapping).toBe(true);
  });

  test('recursion error source range points to correct location', () => {
    const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

bad : Nat -> Nat
bad n = bad n`;

    const results = compileSource(source);
    const badDecl = results.find(r => r.name === 'bad')?.declarations.find(d => d.name === 'bad');

    expect(badDecl).toBeDefined();
    expect(badDecl!.checkErrors.length).toBeGreaterThan(0);

    const errorPath = badDecl!.checkErrors[0].env.indexPath;
    const elabMap = badDecl!.elabMap!;
    const sourceMap = badDecl!.sourceMap!;

    // Find the mapping by walking up the path
    let range: SourceRange | undefined;
    let currentPath = errorPath;
    while (currentPath.length > 0 && !range) {
      const pathStr = serializeIndexPath(currentPath);
      const surfPath = elabMap.get(pathStr);
      if (surfPath) {
        range = sourceMap.get(surfPath);
      }
      currentPath = currentPath.slice(0, -1);
    }

    // The range should exist and point to line 6 (the "bad n = bad n" line)
    // In source (1-indexed): line 6
    // Note: sourceMap uses 1-indexed lines relative to block start
    expect(range).toBeDefined();

    // The error should NOT be at the very end of the file
    const lines = source.split('\n');
    const lastLineNum = lines.length;
    // If the error is at the last line + 1, that's the "end of file" bug
    if (range) {
      expect(range.start.line).toBeLessThanOrEqual(lastLineNum);
      expect(range.end.line).toBeLessThanOrEqual(lastLineNum);
    }
  });
});
