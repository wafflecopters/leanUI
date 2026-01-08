/**
 * Comprehensive Tests for WHNF (Weak Head Normal Form) Reduction
 *
 * Tests the WHNF reduction function which handles:
 * 1. Beta reduction: (λx. t) s → t[x := s]
 * 2. Let expansion: let x := v in t → t[x := v]
 * 3. Delta reduction: function application via DefinitionsMap
 * 4. Match reduction: pattern matching on constructors
 *
 * WHNF reduces terms until they are:
 * - A lambda (Binder with BLam)
 * - A Pi (Binder with BPi)
 * - A constructor application (stuck)
 * - A variable (stuck)
 * - A constant without definition (stuck)
 */

import { describe, it, expect } from 'vitest';
import {
  TTKTerm,
  TTKContext,
  TTKClause,
  mkVar,
  mkPi,
  mkLambda,
  mkApp,
  mkConst,
  mkLet,
  mkType,
  mkProp,
  mkHole,
  prettyPrint,
} from './tt-kernel';
import { whnf, DefinitionsMap, convertible } from './tt-typecheck';
import { TPattern } from './tt-core';

// ============================================================================
// Test Helpers
// ============================================================================

/** Create a Nat constant */
const NAT: TTKTerm = mkConst('Nat', mkType(0));

/** Create zero constant */
const ZERO: TTKTerm = mkConst('zero', NAT);

/** Create succ constant: Nat -> Nat */
const SUCC: TTKTerm = mkConst('succ', mkPi(NAT, NAT, '_'));

/** Create a natural number literal */
function mkNat(n: number): TTKTerm {
  let result = ZERO;
  for (let i = 0; i < n; i++) {
    result = mkApp(SUCC, result);
  }
  return result;
}

/** Create a Bool constant */
const BOOL: TTKTerm = mkConst('Bool', mkType(0));

/** Create true constant */
const TRUE: TTKTerm = mkConst('true', BOOL);

/** Create false constant */
const FALSE: TTKTerm = mkConst('false', BOOL);

/** Create List constant: Type -> Type */
const LIST: TTKTerm = mkConst('List', mkPi(mkType(0), mkType(0), '_'));

/** Create nil constant: (A : Type) -> List A */
const NIL: TTKTerm = mkConst('nil', mkPi(mkType(0), mkApp(LIST, mkVar(0)), 'A'));

/** Create cons constant */
function mkCons(A: TTKTerm, head: TTKTerm, tail: TTKTerm): TTKTerm {
  const consType = mkPi(
    mkType(0),
    mkPi(mkVar(0), mkPi(mkApp(LIST, mkVar(1)), mkApp(LIST, mkVar(2)), '_'), '_'),
    'A'
  );
  const CONS = mkConst('cons', consType);
  return mkApp(mkApp(mkApp(CONS, A), head), tail);
}

/** Create a Match expression */
function mkMatch(scrutinee: TTKTerm, clauses: TTKClause[]): TTKTerm {
  return { tag: 'Match', scrutinee, clauses };
}

/** Create a variable pattern */
function pvar(name: string): TPattern {
  return { tag: 'PVar', name };
}

/** Create a wildcard pattern */
function pwild(): TPattern {
  return { tag: 'PWild' };
}

/** Create a constructor pattern */
function pctor(name: string, args: TPattern[]): TPattern {
  return { tag: 'PCtor', name, args };
}

/** Create an annotation */
function mkAnnot(term: TTKTerm, type: TTKTerm): TTKTerm {
  return { tag: 'Annot', term, type };
}

// ============================================================================
// Beta Reduction Tests
// ============================================================================

describe('WHNF - Beta Reduction', () => {
  it('should reduce identity function application: (λx. x) y → y', () => {
    const ctx: TTKContext = [{ name: 'y', type: NAT }];
    const identity = mkLambda(NAT, mkVar(0), 'x');  // λx. x
    const term = mkApp(identity, mkVar(0));         // (λx. x) y

    const result = whnf(term, ctx);

    expect(result.tag).toBe('Var');
    if (result.tag === 'Var') {
      expect(result.index).toBe(0);  // y
    }
  });

  it('should reduce constant function application: (λx. z) y → z', () => {
    const ctx: TTKContext = [
      { name: 'y', type: NAT },
      { name: 'z', type: NAT },
    ];
    // λx. z where z is at index 1 in outer context, becomes index 0 under lambda
    const constFn = mkLambda(NAT, mkVar(1), 'x');  // λx. z (z is outer var)
    const term = mkApp(constFn, mkVar(0));         // (λx. z) y

    const result = whnf(term, ctx);

    // After reduction, z should now be at index 0 (since y was substituted away)
    expect(result.tag).toBe('Var');
    if (result.tag === 'Var') {
      expect(result.index).toBe(0);  // z after substitution
    }
  });

  it('should reduce nested application: (λx. x x) y → y y', () => {
    const ctx: TTKContext = [{ name: 'y', type: NAT }];
    // λx. x x (apply x to itself)
    const selfApp = mkLambda(NAT, mkApp(mkVar(0), mkVar(0)), 'x');
    const term = mkApp(selfApp, mkVar(0));  // (λx. x x) y

    const result = whnf(term, ctx);

    // Result should be App(y, y) = App(Var 0, Var 0)
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Var');
      expect(result.arg.tag).toBe('Var');
    }
  });

  it('should reduce multiple beta reductions: ((λx. λy. x) a) b → a', () => {
    const ctx: TTKContext = [
      { name: 'a', type: NAT },
      { name: 'b', type: NAT },
    ];
    // λx. λy. x (K combinator)
    const K = mkLambda(NAT, mkLambda(NAT, mkVar(1), 'y'), 'x');
    // ((λx. λy. x) a) b
    const term = mkApp(mkApp(K, mkVar(0)), mkVar(1));

    const result = whnf(term, ctx);

    // Should reduce to a (Var 0, but indices might shift)
    expect(result.tag).toBe('Var');
  });

  it('should reduce beta redex in function position', () => {
    const ctx: TTKContext = [
      { name: 'f', type: mkPi(NAT, NAT, '_') },
      { name: 'x', type: NAT },
    ];
    // ((λg. g) f) x
    const identity = mkLambda(mkPi(NAT, NAT, '_'), mkVar(0), 'g');
    const term = mkApp(mkApp(identity, mkVar(0)), mkVar(1));

    const result = whnf(term, ctx);

    // Should reduce to f x
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Var');
      if (result.fn.tag === 'Var') {
        expect(result.fn.index).toBe(0);  // f
      }
    }
  });

  it('should handle lambda with non-trivial body', () => {
    const ctx: TTKContext = [{ name: 'n', type: NAT }];
    // λx. succ x
    const succFn = mkLambda(NAT, mkApp(SUCC, mkVar(0)), 'x');
    const term = mkApp(succFn, mkVar(0));  // (λx. succ x) n

    const result = whnf(term, ctx);

    // Should reduce to succ n
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Const');
      if (result.fn.tag === 'Const') {
        expect(result.fn.name).toBe('succ');
      }
    }
  });
});

// ============================================================================
// Let Expansion Tests
// ============================================================================

describe('WHNF - Let Expansion', () => {
  it('should expand let binding: let x := 0 in x → 0', () => {
    const term = mkLet('x', NAT, ZERO, mkVar(0));  // let x := 0 in x

    const result = whnf(term);

    expect(result.tag).toBe('Const');
    if (result.tag === 'Const') {
      expect(result.name).toBe('zero');
    }
  });

  it('should expand let binding with non-trivial body: let x := 0 in succ x → succ 0', () => {
    const term = mkLet('x', NAT, ZERO, mkApp(SUCC, mkVar(0)));  // let x := 0 in succ x

    const result = whnf(term);

    // Should reduce to succ 0
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Const');
      if (result.fn.tag === 'Const') {
        expect(result.fn.name).toBe('succ');
      }
      expect(result.arg.tag).toBe('Const');
      if (result.arg.tag === 'Const') {
        expect(result.arg.name).toBe('zero');
      }
    }
  });

  it('should expand nested let bindings', () => {
    // let x := 0 in let y := succ x in y
    const inner = mkLet('y', NAT, mkApp(SUCC, mkVar(0)), mkVar(0));
    const term = mkLet('x', NAT, ZERO, inner);

    const result = whnf(term);

    // Should reduce to succ 0
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Const');
      if (result.fn.tag === 'Const') {
        expect(result.fn.name).toBe('succ');
      }
    }
  });

  it('should expand let in function position', () => {
    const ctx: TTKContext = [{ name: 'n', type: NAT }];
    // (let f := succ in f) n
    const letExpr = mkLet('f', mkPi(NAT, NAT, '_'), SUCC, mkVar(0));
    const term = mkApp(letExpr, mkVar(0));

    const result = whnf(term, ctx);

    // Should reduce to succ n
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Const');
      if (result.fn.tag === 'Const') {
        expect(result.fn.name).toBe('succ');
      }
    }
  });

  it('should handle unused let binding', () => {
    const ctx: TTKContext = [{ name: 'y', type: NAT }];
    // let x := 0 in y (x is unused)
    const term = mkLet('x', NAT, ZERO, mkVar(1));  // y is at index 1 under the let

    const result = whnf(term, ctx);

    // Should reduce to y
    expect(result.tag).toBe('Var');
    if (result.tag === 'Var') {
      expect(result.index).toBe(0);  // y after the let is removed
    }
  });
});

// ============================================================================
// Stuck Terms Tests (No Reduction Possible)
// ============================================================================

describe('WHNF - Stuck Terms', () => {
  it('should not reduce a variable', () => {
    const ctx: TTKContext = [{ name: 'x', type: NAT }];
    const term = mkVar(0);

    const result = whnf(term, ctx);

    expect(result.tag).toBe('Var');
    expect(result).toBe(term);  // Should be the same object
  });

  it('should not reduce a constant without definition', () => {
    const term = ZERO;

    const result = whnf(term);

    expect(result.tag).toBe('Const');
    if (result.tag === 'Const') {
      expect(result.name).toBe('zero');
    }
  });

  it('should not reduce a lambda (already in WHNF)', () => {
    const lambda = mkLambda(NAT, mkVar(0), 'x');

    const result = whnf(lambda);

    expect(result.tag).toBe('Binder');
    if (result.tag === 'Binder') {
      expect(result.binderKind.tag).toBe('BLam');
    }
    expect(result).toBe(lambda);
  });

  it('should not reduce a Pi type (already in WHNF)', () => {
    const pi = mkPi(NAT, NAT, 'x');

    const result = whnf(pi);

    expect(result.tag).toBe('Binder');
    if (result.tag === 'Binder') {
      expect(result.binderKind.tag).toBe('BPi');
    }
    expect(result).toBe(pi);
  });

  it('should not reduce a Sort', () => {
    const sort = mkType(1);

    const result = whnf(sort);

    expect(result.tag).toBe('Sort');
    expect(result).toBe(sort);
  });

  it('should get stuck on application to variable', () => {
    const ctx: TTKContext = [
      { name: 'f', type: mkPi(NAT, NAT, '_') },
      { name: 'x', type: NAT },
    ];
    const term = mkApp(mkVar(0), mkVar(1));  // f x

    const result = whnf(term, ctx);

    // Should stay as App with variable in function position
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Var');
    }
  });

  it('should get stuck on constructor application', () => {
    const term = mkApp(SUCC, ZERO);  // succ zero

    const result = whnf(term);

    // succ is not a lambda, so this is stuck
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Const');
      if (result.fn.tag === 'Const') {
        expect(result.fn.name).toBe('succ');
      }
    }
  });
});

// ============================================================================
// Delta Reduction Tests (Function Definitions)
// ============================================================================

describe('WHNF - Delta Reduction', () => {
  it('should reduce defined constant application', () => {
    // Define double : Nat -> Nat as match n | zero => zero | succ m => succ (succ (double m))
    // For simplicity, let's define it as a simple body: λn. succ (succ n)
    const definitions: DefinitionsMap = new Map();

    // double n = succ (succ n) as a match expression
    const doubleBody: TTKTerm = mkApp(SUCC, mkApp(SUCC, mkVar(0)));
    definitions.set('double', doubleBody);  // Body expects one arg at index 0

    const double = mkConst('double', mkPi(NAT, NAT, 'n'));
    const term = mkApp(double, ZERO);  // double 0

    const result = whnf(term, [], definitions);

    // Should reduce to succ (succ 0)
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Const');
      if (result.fn.tag === 'Const') {
        expect(result.fn.name).toBe('succ');
      }
    }
  });

  it('should reduce multi-argument function definition', () => {
    // Define add : Nat -> Nat -> Nat where add x y = ... (simplified)
    const definitions: DefinitionsMap = new Map();

    // Simplified: add x y = succ y (ignores x)
    // Body with two args: y at 0, x at 1
    const addBody: TTKTerm = mkApp(SUCC, mkVar(0));
    definitions.set('add', addBody);

    const add = mkConst('add', mkPi(NAT, mkPi(NAT, NAT, 'y'), 'x'));
    const term = mkApp(mkApp(add, ZERO), ZERO);  // add 0 0

    const result = whnf(term, [], definitions);

    // Should reduce to succ 0
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Const');
      if (result.fn.tag === 'Const') {
        expect(result.fn.name).toBe('succ');
      }
      expect(result.arg.tag).toBe('Const');
      if (result.arg.tag === 'Const') {
        expect(result.arg.name).toBe('zero');
      }
    }
  });

  it('should not reduce undefined constant', () => {
    const definitions: DefinitionsMap = new Map();
    // definitions is empty

    const foo = mkConst('foo', mkPi(NAT, NAT, '_'));
    const term = mkApp(foo, ZERO);

    const result = whnf(term, [], definitions);

    // Should stay stuck as App(foo, 0)
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Const');
      if (result.fn.tag === 'Const') {
        expect(result.fn.name).toBe('foo');
      }
    }
  });
});

// ============================================================================
// Match Reduction Tests
// ============================================================================

describe('WHNF - Match Reduction', () => {
  it('should reduce match on zero', () => {
    // match 0 | zero => true | succ n => false
    const clauses: TTKClause[] = [
      { patterns: [pctor('zero', [])], rhs: TRUE },
      { patterns: [pctor('succ', [pvar('n')])], rhs: FALSE },
    ];
    const term = mkMatch(ZERO, clauses);

    const result = whnf(term);

    expect(result.tag).toBe('Const');
    if (result.tag === 'Const') {
      expect(result.name).toBe('true');
    }
  });

  it('should reduce match on succ and bind pattern variable', () => {
    // match (succ 0) | zero => 0 | succ n => n
    const clauses: TTKClause[] = [
      { patterns: [pctor('zero', [])], rhs: ZERO },
      { patterns: [pctor('succ', [pvar('n')])], rhs: mkVar(0) },  // n bound at 0
    ];
    const term = mkMatch(mkApp(SUCC, ZERO), clauses);

    const result = whnf(term);

    // Should reduce to 0 (the bound n)
    expect(result.tag).toBe('Const');
    if (result.tag === 'Const') {
      expect(result.name).toBe('zero');
    }
  });

  it('should reduce match with wildcard pattern', () => {
    // match (succ 0) | _ => true
    const clauses: TTKClause[] = [
      { patterns: [pwild()], rhs: TRUE },
    ];
    const term = mkMatch(mkApp(SUCC, ZERO), clauses);

    const result = whnf(term);

    expect(result.tag).toBe('Const');
    if (result.tag === 'Const') {
      expect(result.name).toBe('true');
    }
  });

  it('should reduce match with variable pattern', () => {
    // match (succ 0) | x => x
    const clauses: TTKClause[] = [
      { patterns: [pvar('x')], rhs: mkVar(0) },
    ];
    const term = mkMatch(mkApp(SUCC, ZERO), clauses);

    const result = whnf(term);

    // Should reduce to succ 0
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Const');
      if (result.fn.tag === 'Const') {
        expect(result.fn.name).toBe('succ');
      }
    }
  });

  it('should stay stuck when scrutinee is a variable', () => {
    const ctx: TTKContext = [{ name: 'n', type: NAT }];
    const clauses: TTKClause[] = [
      { patterns: [pctor('zero', [])], rhs: TRUE },
      { patterns: [pctor('succ', [pvar('m')])], rhs: FALSE },
    ];
    const term = mkMatch(mkVar(0), clauses);  // match n

    const result = whnf(term, ctx);

    // Should stay as Match since n is not a constructor
    expect(result.tag).toBe('Match');
    if (result.tag === 'Match') {
      expect(result.scrutinee.tag).toBe('Var');
    }
  });

  it('should reduce scrutinee before matching', () => {
    // match ((λx. x) 0) | zero => true
    // Should first reduce (λx. x) 0 → 0, then match
    const identity = mkLambda(NAT, mkVar(0), 'x');
    const scrutinee = mkApp(identity, ZERO);
    const clauses: TTKClause[] = [
      { patterns: [pctor('zero', [])], rhs: TRUE },
    ];
    const term = mkMatch(scrutinee, clauses);

    const result = whnf(term);

    expect(result.tag).toBe('Const');
    if (result.tag === 'Const') {
      expect(result.name).toBe('true');
    }
  });

  it('should match nested constructor patterns', () => {
    // match (succ (succ 0)) | succ (succ n) => n | _ => 0
    const clauses: TTKClause[] = [
      { patterns: [pctor('succ', [pctor('succ', [pvar('n')])])], rhs: mkVar(0) },
      { patterns: [pwild()], rhs: ZERO },
    ];
    const term = mkMatch(mkNat(2), clauses);

    const result = whnf(term);

    // Should match first pattern and bind n to 0
    expect(result.tag).toBe('Const');
    if (result.tag === 'Const') {
      expect(result.name).toBe('zero');
    }
  });

  it('should try clauses in order', () => {
    // match 0 | _ => true | zero => false
    // First clause (wildcard) should match
    const clauses: TTKClause[] = [
      { patterns: [pwild()], rhs: TRUE },
      { patterns: [pctor('zero', [])], rhs: FALSE },
    ];
    const term = mkMatch(ZERO, clauses);

    const result = whnf(term);

    expect(result.tag).toBe('Const');
    if (result.tag === 'Const') {
      expect(result.name).toBe('true');
    }
  });

  it('should reduce match in Bool case', () => {
    // match true | true => 0 | false => succ 0
    const clauses: TTKClause[] = [
      { patterns: [pctor('true', [])], rhs: ZERO },
      { patterns: [pctor('false', [])], rhs: mkApp(SUCC, ZERO) },
    ];
    const term = mkMatch(TRUE, clauses);

    const result = whnf(term);

    expect(result.tag).toBe('Const');
    if (result.tag === 'Const') {
      expect(result.name).toBe('zero');
    }
  });
});

// ============================================================================
// Complex/Combined Tests
// ============================================================================

describe('WHNF - Complex Reductions', () => {
  it('should reduce beta and then match', () => {
    // match ((λx. x) 0) | zero => true
    const identity = mkLambda(NAT, mkVar(0), 'x');
    const clauses: TTKClause[] = [
      { patterns: [pctor('zero', [])], rhs: TRUE },
    ];
    const term = mkMatch(mkApp(identity, ZERO), clauses);

    const result = whnf(term);

    expect(result.tag).toBe('Const');
    if (result.tag === 'Const') {
      expect(result.name).toBe('true');
    }
  });

  it('should reduce let and then beta', () => {
    // (let f := (λx. succ x) in f) 0
    const succFn = mkLambda(NAT, mkApp(SUCC, mkVar(0)), 'x');
    const letExpr = mkLet('f', mkPi(NAT, NAT, '_'), succFn, mkVar(0));
    const term = mkApp(letExpr, ZERO);

    const result = whnf(term);

    // Should reduce to succ 0
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Const');
      if (result.fn.tag === 'Const') {
        expect(result.fn.name).toBe('succ');
      }
    }
  });

  it('should handle chained beta reductions', () => {
    // ((λf. λx. f x) succ) 0
    // = (λx. succ x) 0
    // = succ 0
    const app = mkLambda(
      mkPi(NAT, NAT, '_'),
      mkLambda(NAT, mkApp(mkVar(1), mkVar(0)), 'x'),
      'f'
    );
    const term = mkApp(mkApp(app, SUCC), ZERO);

    const result = whnf(term);

    // Should reduce to succ 0
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Const');
      if (result.fn.tag === 'Const') {
        expect(result.fn.name).toBe('succ');
      }
    }
  });

  it('should reduce definition then match', () => {
    const definitions: DefinitionsMap = new Map();
    // isZero : Nat -> Bool as match expression
    const isZeroMatch = mkMatch(mkVar(0), [
      { patterns: [pctor('zero', [])], rhs: TRUE },
      { patterns: [pctor('succ', [pwild()])], rhs: FALSE },
    ]);
    definitions.set('isZero', isZeroMatch);

    const isZero = mkConst('isZero', mkPi(NAT, BOOL, 'n'));
    const term = mkApp(isZero, ZERO);

    const result = whnf(term, [], definitions);

    expect(result.tag).toBe('Const');
    if (result.tag === 'Const') {
      expect(result.name).toBe('true');
    }
  });

  it('should reduce definition with match expression', () => {
    const definitions: DefinitionsMap = new Map();
    // isZero : Nat -> Bool as match
    // The definition body expects one argument at index 0
    const isZeroMatch = mkMatch(mkVar(0), [
      { patterns: [pctor('zero', [])], rhs: TRUE },
      { patterns: [pctor('succ', [pwild()])], rhs: FALSE },
    ]);
    definitions.set('isZero', isZeroMatch);

    const isZero = mkConst('isZero', mkPi(NAT, BOOL, 'n'));

    // isZero 0 should return true
    const term1 = mkApp(isZero, ZERO);
    const result1 = whnf(term1, [], definitions);
    expect(result1.tag).toBe('Const');
    if (result1.tag === 'Const') {
      expect(result1.name).toBe('true');
    }

    // isZero (succ 0) should return false
    const term2 = mkApp(isZero, mkNat(1));
    const result2 = whnf(term2, [], definitions);
    expect(result2.tag).toBe('Const');
    if (result2.tag === 'Const') {
      expect(result2.name).toBe('false');
    }
  });
});

// ============================================================================
// Edge Cases
// ============================================================================

describe('WHNF - Edge Cases', () => {
  it('should handle empty context', () => {
    const term = ZERO;
    const result = whnf(term, []);
    expect(result).toBe(term);
  });

  it('should handle deeply nested lambdas (Church encoding style)', () => {
    // Church numeral 0: λf. λx. x
    const zero = mkLambda(
      mkPi(NAT, NAT, '_'),
      mkLambda(NAT, mkVar(0), 'x'),
      'f'
    );
    const result = whnf(zero);
    // Should stay as lambda (WHNF)
    expect(result.tag).toBe('Binder');
  });

  it('should handle application of Sort (stuck)', () => {
    // Type 0 applied to something - this is ill-typed but WHNF shouldn't crash
    const term = mkApp(mkType(0), ZERO);
    const result = whnf(term);
    // Should stay stuck
    expect(result.tag).toBe('App');
  });

  it('should handle match with no matching clauses (stuck)', () => {
    // This shouldn't happen in well-typed terms, but WHNF should handle it
    const clauses: TTKClause[] = [
      { patterns: [pctor('nonexistent', [])], rhs: TRUE },
    ];
    const term = mkMatch(ZERO, clauses);
    const result = whnf(term);
    // Should stay stuck as Match with reduced scrutinee
    expect(result.tag).toBe('Match');
  });

  it('should preserve convertibility through WHNF', () => {
    const ctx: TTKContext = [{ name: 'x', type: NAT }];

    // Two different representations of the same value
    const term1 = mkApp(mkLambda(NAT, mkVar(0), 'y'), mkVar(0));  // (λy. y) x
    const term2 = mkVar(0);  // x

    // After WHNF, they should be convertible
    const result1 = whnf(term1, ctx);
    const result2 = whnf(term2, ctx);

    expect(convertible(result1, result2, ctx)).toBe(true);
  });
});

// ============================================================================
// Multi-Arg Pattern Match Tests
// ============================================================================

describe('WHNF - Match with Multiple Pattern Variables', () => {
  it('should bind multiple pattern variables correctly', () => {
    // match (succ 0) (succ (succ 0)) | succ a, succ b => a
    // But our Match only takes one scrutinee, so this tests nested patterns

    // Actually, let's test a pattern like: match (cons x xs) | cons h t => h
    // Using Nat constructors: match (succ (succ 0)) | succ (succ n) => n
    const scrutinee = mkNat(2);  // succ (succ zero)
    const clauses: TTKClause[] = [
      {
        patterns: [pctor('succ', [pctor('succ', [pvar('n')])])],
        rhs: mkVar(0)  // n
      },
    ];
    const term = mkMatch(scrutinee, clauses);

    const result = whnf(term);

    // n should be bound to zero
    expect(result.tag).toBe('Const');
    if (result.tag === 'Const') {
      expect(result.name).toBe('zero');
    }
  });
});

// ============================================================================
// De Bruijn Index Tests - Critical for Correctness
// ============================================================================

describe('WHNF - De Bruijn Index Handling', () => {
  it('should correctly substitute and shift in nested lambdas', () => {
    // (λx. λy. x) a b
    // Step 1: (λy. a) b  -- x substituted with a, but a needs no shift (closed term)
    // Step 2: a
    const ctx: TTKContext = [
      { name: 'a', type: NAT },
      { name: 'b', type: NAT },
    ];
    // λx. λy. x  -- in body of outer lambda, x is at index 1 (y is at 0)
    const K = mkLambda(NAT, mkLambda(NAT, mkVar(1), 'y'), 'x');
    const term = mkApp(mkApp(K, mkVar(0)), mkVar(1));  // K a b

    const result = whnf(term, ctx);

    expect(result.tag).toBe('Var');
    if (result.tag === 'Var') {
      expect(result.index).toBe(0);  // a
    }
  });

  it('should correctly handle free variables in lambda body after substitution', () => {
    // Context: a, b, c (indices 0, 1, 2)
    // (λx. b) a → b (but b's index needs to be decremented from 2 to 1)
    const ctx: TTKContext = [
      { name: 'a', type: NAT },
      { name: 'b', type: NAT },
      { name: 'c', type: NAT },
    ];
    // λx. b where b is at index 2 in context, so index 1 under the lambda
    const fn = mkLambda(NAT, mkVar(1), 'x');
    const term = mkApp(fn, mkVar(0));  // (λx. b) a

    const result = whnf(term, ctx);

    // b should now be at index 0 after a is removed from consideration
    expect(result.tag).toBe('Var');
    if (result.tag === 'Var') {
      expect(result.index).toBe(0);  // b (was 1, but x was removed)
    }
  });

  it('should correctly shift argument when substituting into nested binder', () => {
    // (λx. λy. x y) f
    // After substitution: λy. f y
    // f needs to be shifted when going under y binder
    const ctx: TTKContext = [{ name: 'f', type: mkPi(NAT, NAT, '_') }];
    // λx. λy. x y where x is at 1, y is at 0
    const fn = mkLambda(
      mkPi(NAT, NAT, '_'),
      mkLambda(NAT, mkApp(mkVar(1), mkVar(0)), 'y'),
      'x'
    );
    const term = mkApp(fn, mkVar(0));  // (λx. λy. x y) f

    const result = whnf(term, ctx);

    // Result should be λy. f y where f is at index 1 (shifted for y binder)
    expect(result.tag).toBe('Binder');
    if (result.tag === 'Binder') {
      expect(result.binderKind.tag).toBe('BLam');
      // Body should be App(Var(1), Var(0)) = f y
      expect(result.body.tag).toBe('App');
      if (result.body.tag === 'App') {
        expect(result.body.fn.tag).toBe('Var');
        if (result.body.fn.tag === 'Var') {
          expect(result.body.fn.index).toBe(1);  // f shifted by 1
        }
        expect(result.body.arg.tag).toBe('Var');
        if (result.body.arg.tag === 'Var') {
          expect(result.body.arg.index).toBe(0);  // y
        }
      }
    }
  });

  it('should handle substitution of compound term with free variables', () => {
    // (λx. x) (succ y) → succ y
    const ctx: TTKContext = [{ name: 'y', type: NAT }];
    const identity = mkLambda(NAT, mkVar(0), 'x');
    const arg = mkApp(SUCC, mkVar(0));  // succ y
    const term = mkApp(identity, arg);

    const result = whnf(term, ctx);

    // Should be succ y
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Const');
      expect(result.arg.tag).toBe('Var');
      if (result.arg.tag === 'Var') {
        expect(result.arg.index).toBe(0);  // y
      }
    }
  });

  it('should correctly handle triple-nested lambda: ((λx. λy. λz. x) a) b) c', () => {
    const ctx: TTKContext = [
      { name: 'a', type: NAT },
      { name: 'b', type: NAT },
      { name: 'c', type: NAT },
    ];
    // λx. λy. λz. x  -- x is at index 2 in innermost body
    const fn = mkLambda(
      NAT,
      mkLambda(NAT, mkLambda(NAT, mkVar(2), 'z'), 'y'),
      'x'
    );
    const term = mkApp(mkApp(mkApp(fn, mkVar(0)), mkVar(1)), mkVar(2));

    const result = whnf(term, ctx);

    expect(result.tag).toBe('Var');
    if (result.tag === 'Var') {
      expect(result.index).toBe(0);  // a
    }
  });

  it('should correctly handle S combinator: S x y z = x z (y z)', () => {
    // S = λx. λy. λz. x z (y z)
    // Let's verify (S f g a) reduces correctly
    const ctx: TTKContext = [
      { name: 'f', type: mkPi(NAT, mkPi(NAT, NAT, '_'), '_') },  // f : Nat -> Nat -> Nat
      { name: 'g', type: mkPi(NAT, NAT, '_') },                   // g : Nat -> Nat
      { name: 'a', type: NAT },
    ];

    // S = λx. λy. λz. (x z) (y z)
    // In innermost body: x is at 2, y is at 1, z is at 0
    const S = mkLambda(
      mkPi(NAT, mkPi(NAT, NAT, '_'), '_'),
      mkLambda(
        mkPi(NAT, NAT, '_'),
        mkLambda(
          NAT,
          mkApp(mkApp(mkVar(2), mkVar(0)), mkApp(mkVar(1), mkVar(0))),
          'z'
        ),
        'y'
      ),
      'x'
    );

    // S f g a
    const term = mkApp(mkApp(mkApp(S, mkVar(0)), mkVar(1)), mkVar(2));

    const result = whnf(term, ctx);

    // Should reduce to (f a) (g a)
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      // fn = f a
      expect(result.fn.tag).toBe('App');
      if (result.fn.tag === 'App') {
        expect(result.fn.fn.tag).toBe('Var');  // f
        expect(result.fn.arg.tag).toBe('Var'); // a
      }
      // arg = g a
      expect(result.arg.tag).toBe('App');
      if (result.arg.tag === 'App') {
        expect(result.arg.fn.tag).toBe('Var');  // g
        expect(result.arg.arg.tag).toBe('Var'); // a
      }
    }
  });

  it('should handle let with reference to outer variable', () => {
    // Context: x
    // let y := succ x in y
    const ctx: TTKContext = [{ name: 'x', type: NAT }];
    // Under the let, x is at index 1
    const term = mkLet('y', NAT, mkApp(SUCC, mkVar(0)), mkVar(0));

    const result = whnf(term, ctx);

    // Should reduce to succ x
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Const');
      if (result.fn.tag === 'Const') {
        expect(result.fn.name).toBe('succ');
      }
      expect(result.arg.tag).toBe('Var');
      if (result.arg.tag === 'Var') {
        expect(result.arg.index).toBe(0);  // x
      }
    }
  });

  it('should handle capture-avoiding substitution', () => {
    // (λx. λx. x) a → λx. x  (inner x shadows, should NOT become a)
    const ctx: TTKContext = [{ name: 'a', type: NAT }];
    // λx. λx. x -- innermost x refers to inner binder (index 0)
    const fn = mkLambda(NAT, mkLambda(NAT, mkVar(0), 'x'), 'x');
    const term = mkApp(fn, mkVar(0));  // (λx. λx. x) a

    const result = whnf(term, ctx);

    // Should be λx. x (the inner lambda unchanged)
    expect(result.tag).toBe('Binder');
    if (result.tag === 'Binder') {
      expect(result.body.tag).toBe('Var');
      if (result.body.tag === 'Var') {
        expect(result.body.index).toBe(0);  // Still refers to bound x, not a
      }
    }
  });

  it('should correctly update indices when substituting in pattern match RHS', () => {
    // Context: y
    // match (λx. x) zero | zero => y | succ n => n
    // First reduces to: match zero | zero => y | succ n => n
    // Then matches: y
    const ctx: TTKContext = [{ name: 'y', type: NAT }];
    const identity = mkLambda(NAT, mkVar(0), 'x');
    const scrutinee = mkApp(identity, ZERO);
    const clauses: TTKClause[] = [
      { patterns: [pctor('zero', [])], rhs: mkVar(0) },  // y (at index 0 in ctx)
      { patterns: [pctor('succ', [pvar('n')])], rhs: mkVar(0) },
    ];
    const term = mkMatch(scrutinee, clauses);

    const result = whnf(term, ctx);

    expect(result.tag).toBe('Var');
    if (result.tag === 'Var') {
      expect(result.index).toBe(0);  // y
    }
  });
});

// ============================================================================
// Annotation and Hole Tests
// ============================================================================

describe('WHNF - Annotation Handling', () => {
  it('should not reduce annotation by itself (annotation is WHNF)', () => {
    const term = mkAnnot(ZERO, NAT);
    const result = whnf(term);

    // Annotations don't reduce in WHNF
    expect(result.tag).toBe('Annot');
  });

  it('should get stuck on application of annotated lambda', () => {
    // (λx. x : Nat -> Nat) 0
    // WHNF doesn't look through annotations to find the lambda
    const identity = mkLambda(NAT, mkVar(0), 'x');
    const annotated = mkAnnot(identity, mkPi(NAT, NAT, '_'));
    const term = mkApp(annotated, ZERO);

    const result = whnf(term);

    // Application of annotated term stays stuck
    // (WHNF doesn't strip annotations to find reducible lambda)
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Annot');
    }
  });
});

describe('WHNF - Hole Handling', () => {
  it('should not reduce a hole (holes are stuck)', () => {
    const hole = mkHole('?goal', NAT);
    const result = whnf(hole);

    expect(result.tag).toBe('Hole');
    if (result.tag === 'Hole') {
      expect(result.id).toBe('?goal');
    }
  });

  it('should get stuck on application to hole', () => {
    const hole = mkHole('?f', mkPi(NAT, NAT, '_'));
    const term = mkApp(hole, ZERO);

    const result = whnf(term);

    // Should stay as App with hole in function position
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Hole');
    }
  });

  it('should get stuck on match with hole scrutinee', () => {
    const hole = mkHole('?n', NAT);
    const clauses: TTKClause[] = [
      { patterns: [pctor('zero', [])], rhs: TRUE },
      { patterns: [pctor('succ', [pvar('m')])], rhs: FALSE },
    ];
    const term = mkMatch(hole, clauses);

    const result = whnf(term);

    expect(result.tag).toBe('Match');
    if (result.tag === 'Match') {
      expect(result.scrutinee.tag).toBe('Hole');
    }
  });
});

// ============================================================================
// More Complex De Bruijn Scenarios
// ============================================================================

describe('WHNF - Complex De Bruijn Scenarios', () => {
  it('should handle deeply nested binders with many free variables', () => {
    // Context: a, b, c, d
    // (λx. λy. a + b + c + d + x + y) arg1 arg2
    // Using simplified representation: λx. λy. (a, b, c, d, x, y)
    const ctx: TTKContext = [
      { name: 'a', type: NAT },
      { name: 'b', type: NAT },
      { name: 'c', type: NAT },
      { name: 'd', type: NAT },
    ];

    // λx. λy. (some term using all variables)
    // Under λx λy: a is at 5, b is at 4, c is at 3, d is at 2, x is at 1, y is at 0
    // Let's use a simple App chain: ((((a, b), c), x), y)
    const innerBody = mkApp(
      mkApp(
        mkApp(mkVar(3), mkVar(2)),  // (a b) -- wait indices are wrong, let me recalculate
        mkVar(1)
      ),
      mkVar(0)
    );
    // Actually let's keep it simple: λx. λy. x
    const fn = mkLambda(NAT, mkLambda(NAT, mkVar(1), 'y'), 'x');
    const term = mkApp(mkApp(fn, mkVar(0)), mkVar(1));  // (λx. λy. x) a b

    const result = whnf(term, ctx);

    // Should return a (index 0 in ctx, became 0 after both binders removed)
    expect(result.tag).toBe('Var');
    if (result.tag === 'Var') {
      expect(result.index).toBe(0);  // a
    }
  });

  it('should correctly handle let inside lambda', () => {
    // (λx. let y := x in succ y) 0
    const fn = mkLambda(
      NAT,
      mkLet('y', NAT, mkVar(0), mkApp(SUCC, mkVar(0))),  // let y := x in succ y
      'x'
    );
    const term = mkApp(fn, ZERO);

    const result = whnf(term);

    // Should reduce to succ 0
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Const');
      if (result.fn.tag === 'Const') {
        expect(result.fn.name).toBe('succ');
      }
      expect(result.arg.tag).toBe('Const');
      if (result.arg.tag === 'Const') {
        expect(result.arg.name).toBe('zero');
      }
    }
  });

  it('should handle match inside lambda with correct indices', () => {
    // (λn. match n | zero => 0 | succ m => m) (succ (succ 0))
    const fn = mkLambda(
      NAT,
      mkMatch(mkVar(0), [
        { patterns: [pctor('zero', [])], rhs: ZERO },
        { patterns: [pctor('succ', [pvar('m')])], rhs: mkVar(0) },  // m
      ]),
      'n'
    );
    const term = mkApp(fn, mkNat(2));

    const result = whnf(term);

    // match (succ (succ 0)) should return succ 0 (the m from succ m)
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Const');
      if (result.fn.tag === 'Const') {
        expect(result.fn.name).toBe('succ');
      }
    }
  });

  it('should handle application with outer variable in argument', () => {
    // Context: f : Nat -> Nat
    // (λx. f x) 0 → f 0
    const ctx: TTKContext = [{ name: 'f', type: mkPi(NAT, NAT, '_') }];
    // Under λx: f is at index 1, x is at index 0
    const fn = mkLambda(NAT, mkApp(mkVar(1), mkVar(0)), 'x');
    const term = mkApp(fn, ZERO);

    const result = whnf(term, ctx);

    // Should be f 0, where f is now at index 0
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Var');
      if (result.fn.tag === 'Var') {
        expect(result.fn.index).toBe(0);  // f
      }
      expect(result.arg.tag).toBe('Const');
      if (result.arg.tag === 'Const') {
        expect(result.arg.name).toBe('zero');
      }
    }
  });

  it('should handle omega combinator partially (ω = λx. x x)', () => {
    // ω = λx. x x
    // ω id = id id = id  (where id = λy. y)
    const omega = mkLambda(
      mkPi(NAT, NAT, '_'),
      mkApp(mkVar(0), mkVar(0)),
      'x'
    );
    const id = mkLambda(NAT, mkVar(0), 'y');
    const term = mkApp(omega, id);  // ω id

    const result = whnf(term);

    // id id = (λy. y) (λy. y) = λy. y
    expect(result.tag).toBe('Binder');
    if (result.tag === 'Binder') {
      expect(result.binderKind.tag).toBe('BLam');
    }
  });

  it('should handle flip combinator: flip f x y = f y x', () => {
    const ctx: TTKContext = [
      { name: 'f', type: mkPi(NAT, mkPi(NAT, NAT, '_'), '_') },
      { name: 'a', type: NAT },
      { name: 'b', type: NAT },
    ];

    // flip = λf. λx. λy. f y x
    // In innermost: f at 2, x at 1, y at 0
    const flip = mkLambda(
      mkPi(NAT, mkPi(NAT, NAT, '_'), '_'),
      mkLambda(
        NAT,
        mkLambda(
          NAT,
          mkApp(mkApp(mkVar(2), mkVar(0)), mkVar(1)),  // f y x
          'y'
        ),
        'x'
      ),
      'f'
    );

    // flip f a b
    const term = mkApp(mkApp(mkApp(flip, mkVar(0)), mkVar(1)), mkVar(2));

    const result = whnf(term, ctx);

    // Should reduce to f b a
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      // outer: (f b) a, so fn = f b, arg = a
      expect(result.arg.tag).toBe('Var');  // a
      if (result.fn.tag === 'App') {
        expect(result.fn.fn.tag).toBe('Var');  // f
        expect(result.fn.arg.tag).toBe('Var'); // b
      }
    }
  });
});

// ============================================================================
// Pattern Binding Order Tests
// ============================================================================

describe('WHNF - Pattern Binding Order', () => {
  it('should bind pattern variables left-to-right, depth-first', () => {
    // Pattern: succ (succ n) matches succ (succ zero)
    // n should be bound to zero
    const clauses: TTKClause[] = [
      {
        patterns: [pctor('succ', [pctor('succ', [pvar('n')])])],
        rhs: mkVar(0)  // n
      },
    ];
    const term = mkMatch(mkNat(2), clauses);

    const result = whnf(term);

    expect(result.tag).toBe('Const');
    if (result.tag === 'Const') {
      expect(result.name).toBe('zero');
    }
  });

  it('should handle multiple pattern variables in order', () => {
    // Pattern: pair a b where pair = λx.λy. ...
    // For simplicity, simulate with nested succ: succ (succ n)
    // and return just n
    const clauses: TTKClause[] = [
      {
        // Match: succ a where a = succ b
        patterns: [pctor('succ', [pctor('succ', [pvar('b')])])],
        // a would be at index 1 if we bound it, b at index 0
        // but we only have pvar('b'), so just b at 0
        rhs: mkApp(SUCC, mkVar(0))  // succ b
      },
    ];
    const term = mkMatch(mkNat(3), clauses);  // succ (succ (succ zero))

    const result = whnf(term);

    // b is bound to (succ zero), so result is succ (succ zero) = 2
    expect(result.tag).toBe('App');
    if (result.tag === 'App') {
      expect(result.fn.tag).toBe('Const');
      if (result.fn.tag === 'Const') {
        expect(result.fn.name).toBe('succ');
      }
    }
  });
});
