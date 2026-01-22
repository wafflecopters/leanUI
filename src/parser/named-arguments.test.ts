/**
 * Tests for Named Arguments Feature
 *
 * Named arguments allow parameters to be specified by name at call sites.
 * This file tests:
 * 1. Parsing named binders in Pi types: { A : Type } -> B
 * 2. Parsing named arguments in applications: f { A := x }
 * 3. Parsing named patterns: foo {A} x = ...
 * 4. Elaboration of named arguments to positional
 */

import { describe, test, expect } from 'vitest';
import { parseExpr, ParseError } from './parser';
import { TTerm } from '../compiler/surface';

// ============================================================================
// Helper Functions
// ============================================================================

function assertBinder(term: TTerm): asserts term is Extract<TTerm, { tag: 'Binder' }> {
  expect(term.tag).toBe('Binder');
}

function assertMultiBinder(term: TTerm): asserts term is Extract<TTerm, { tag: 'MultiBinder' }> {
  expect(term.tag).toBe('MultiBinder');
}

function assertApp(term: TTerm): asserts term is Extract<TTerm, { tag: 'App' }> {
  expect(term.tag).toBe('App');
}

function assertConst(term: TTerm): asserts term is Extract<TTerm, { tag: 'Const' }> {
  expect(term.tag).toBe('Const');
}

// ============================================================================
// Named Binders in Pi Types
// ============================================================================

describe('Named Binders in Pi Types', () => {
  test('Parse single named binder: { A : Type } -> A', () => {
    const term = parseExpr('{ A : Type } -> A');
    assertBinder(term);
    expect(term.binderKind.tag).toBe('BPiTT');
    expect(term.name).toBe('A');
    expect(term.named).toBe(true);
    expect(term.domain?.tag).toBe('Sort');
  });

  test('Parse named binder with body referencing bound var', () => {
    const term = parseExpr('{ A : Type } -> A -> A');
    assertBinder(term);
    expect(term.named).toBe(true);
    expect(term.name).toBe('A');

    // Body should be A -> A (another Pi)
    assertBinder(term.body);
    expect(term.body.binderKind.tag).toBe('BPiTT');
    // The domain should reference A (Var 0)
    expect(term.body.domain?.tag).toBe('Var');
    if (term.body.domain?.tag === 'Var') {
      expect(term.body.domain.index).toBe(0);
    }
  });

  test('Parse multi-name named binder: { A B : Type } -> A', () => {
    const term = parseExpr('{ A B : Type } -> A');
    assertMultiBinder(term);
    expect(term.binderKind.tag).toBe('BPiTT');
    expect(term.names).toEqual(['A', 'B']);
    expect(term.named).toBe(true);
    expect(term.domain.tag).toBe('Sort');
  });

  test('Parse multiple named parameters: { A : Type } -> { B : Type } -> A', () => {
    const term = parseExpr('{ A : Type } -> { B : Type } -> A');
    assertBinder(term);
    expect(term.named).toBe(true);
    expect(term.name).toBe('A');

    assertBinder(term.body);
    expect(term.body.named).toBe(true);
    expect(term.body.name).toBe('B');
  });

  test('Parse mixed named and positional parameters', () => {
    // { A : Type } -> Nat -> { B : Type } -> A
    const term = parseExpr('{ A : Type } -> Nat -> { B : Type } -> A');

    // First: { A : Type }
    assertBinder(term);
    expect(term.named).toBe(true);
    expect(term.name).toBe('A');

    // Second: Nat -> (positional, no name or default name)
    assertBinder(term.body);
    expect(term.body.named).toBeUndefined(); // positional

    // Third: { B : Type }
    assertBinder(term.body.body);
    expect(term.body.body.named).toBe(true);
    expect(term.body.body.name).toBe('B');
  });

  test('Named binder with underscore: { _ : Type } -> Nat', () => {
    const term = parseExpr('{ _ : Type } -> Nat');
    assertBinder(term);
    expect(term.named).toBe(true);
    expect(term.name).toBe('_');
  });

  test('Named binder with complex domain type', () => {
    const term = parseExpr('{ F : Type -> Type } -> F Nat');
    assertBinder(term);
    expect(term.named).toBe(true);
    expect(term.name).toBe('F');
    // Domain should be Type -> Type
    assertBinder(term.domain!);
  });

  test('Error: named binder without arrow', () => {
    expect(() => parseExpr('{ A : Type }')).toThrow(ParseError);
  });

  test('Error: empty named binder', () => {
    expect(() => parseExpr('{ : Type } -> A')).toThrow(ParseError);
  });

  test('Error: named binder without type', () => {
    expect(() => parseExpr('{ A } -> B')).toThrow(ParseError);
  });

  test('Positional binder has named undefined', () => {
    const term = parseExpr('(A : Type) -> A');
    assertBinder(term);
    expect(term.named).toBeUndefined();
  });

  test('Non-dependent arrow has named undefined', () => {
    const term = parseExpr('Nat -> Bool');
    assertBinder(term);
    expect(term.named).toBeUndefined();
  });

  test('Multiple names in named binder: { A B C : Type } -> A', () => {
    const term = parseExpr('{ A B C : Type } -> A');
    assertMultiBinder(term);
    expect(term.names).toEqual(['A', 'B', 'C']);
    expect(term.named).toBe(true);
  });

  test('Mixed multi-name binders', () => {
    // { A B : Type } -> (x y : Nat) -> A
    const term = parseExpr('{ A B : Type } -> (x y : Nat) -> A');

    // First: { A B : Type } - named multi-binder
    assertMultiBinder(term);
    expect(term.named).toBe(true);
    expect(term.names).toEqual(['A', 'B']);

    // Body: (x y : Nat) -> A - positional multi-binder
    assertMultiBinder(term.body);
    expect(term.body.named).toBeUndefined();
    expect(term.body.names).toEqual(['x', 'y']);
  });
});

// ============================================================================
// Contrast with Positional Binders
// ============================================================================

describe('Contrast: Named vs Positional Binders', () => {
  test('Positional single binder', () => {
    const term = parseExpr('(A : Type) -> A');
    assertBinder(term);
    expect(term.named).toBeUndefined();
    expect(term.name).toBe('A');
  });

  test('Positional multi-binder', () => {
    const term = parseExpr('(A B : Type) -> A');
    assertMultiBinder(term);
    expect(term.named).toBeUndefined();
    expect(term.names).toEqual(['A', 'B']);
  });

  test('Named and positional produce same body structure', () => {
    const named = parseExpr('{ A : Type } -> A -> A');
    const positional = parseExpr('(A : Type) -> A -> A');

    assertBinder(named);
    assertBinder(positional);

    // Both should have same body structure (A -> A)
    assertBinder(named.body);
    assertBinder(positional.body);

    // Names should match
    expect(named.name).toBe(positional.name);
  });
});

// ============================================================================
// Edge Cases and Error Handling
// ============================================================================

describe('Named Binders: Edge Cases', () => {
  test('Nested braces are not allowed (for now)', () => {
    // This would be confusing syntax, so we don't support it
    expect(() => parseExpr('{ A : { B : Type } -> B } -> A')).not.toThrow();
    // Actually this should work - the domain is a named Pi type
    const term = parseExpr('{ A : { B : Type } -> B } -> A');
    assertBinder(term);
    expect(term.named).toBe(true);
    // Domain is another named Pi
    assertBinder(term.domain!);
    expect(term.domain!.named).toBe(true);
  });

  test('Named binder in lambda position is not allowed', () => {
    // Lambdas don't use {} syntax - that's only for Pi types
    // \{ A : Type } => A should fail
    expect(() => parseExpr('\\{ A : Type } => A')).toThrow();
  });

  test('Greek letters in named binders', () => {
    const term = parseExpr('{ α : Type } -> α');
    assertBinder(term);
    expect(term.named).toBe(true);
    expect(term.name).toBe('α');
  });

  test('Complex expression in domain', () => {
    const term = parseExpr('{ F : (A : Type) -> A -> Type } -> F Nat Zero');
    assertBinder(term);
    expect(term.named).toBe(true);
    expect(term.name).toBe('F');
  });
});

// ============================================================================
// Named Arguments in Applications
// ============================================================================

describe('Named Arguments in Applications', () => {
  test('Parse simple named argument: f { A := Nat }', () => {
    const term = parseExpr('f { A := Nat }');
    assertApp(term);
    expect(term.argName).toBe('A');
    assertConst(term.fn);
    expect(term.fn.name).toBe('f');
    assertConst(term.arg);
    expect(term.arg.name).toBe('Nat');
  });

  test('Parse named argument with complex value: f { A := Nat -> Bool }', () => {
    const term = parseExpr('f { A := Nat -> Bool }');
    assertApp(term);
    expect(term.argName).toBe('A');
    assertBinder(term.arg);
  });

  test('Parse multiple named arguments: f { A := Nat } { B := Bool }', () => {
    const term = parseExpr('f { A := Nat } { B := Bool }');
    // This should be: App(App(f, Nat), Bool) with argNames
    assertApp(term);
    expect(term.argName).toBe('B');

    assertApp(term.fn);
    expect(term.fn.argName).toBe('A');
  });

  test('Parse mixed positional and named: f x { A := Nat }', () => {
    const term = parseExpr('f x { A := Nat }');
    // App(App(f, x), Nat) where last has argName
    assertApp(term);
    expect(term.argName).toBe('A');

    assertApp(term.fn);
    expect(term.fn.argName).toBeUndefined(); // positional
  });

  test('Parse named argument followed by positional: f { A := Nat } x', () => {
    const term = parseExpr('f { A := Nat } x');
    // App(App(f, Nat), x) where first app has argName
    assertApp(term);
    expect(term.argName).toBeUndefined(); // positional

    assertApp(term.fn);
    expect(term.fn.argName).toBe('A');
  });

  test('Named argument in nested application', () => {
    const term = parseExpr('f (g { A := Nat })');
    assertApp(term);
    expect(term.argName).toBeUndefined(); // outer is positional

    // Inner arg is the application g { A := Nat }
    assertApp(term.arg);
    expect(term.arg.argName).toBe('A');
  });

  test('Named argument with expression value: f { A := x + y }', () => {
    const term = parseExpr('f { A := x + y }');
    assertApp(term);
    expect(term.argName).toBe('A');
    // arg should be (+ x y)
    assertApp(term.arg);
  });

  test('Named argument with lambda value: f { A := \\x => x }', () => {
    const term = parseExpr('f { A := \\x => x }');
    assertApp(term);
    expect(term.argName).toBe('A');
    assertBinder(term.arg);
    expect(term.arg.binderKind.tag).toBe('BLamTT');
  });

  test('Named argument distinguishes from named binder', () => {
    // { A := x } is a named argument (has :=)
    // { A : Type } -> ... is a named binder (has : then ->)
    const namedArg = parseExpr('f { A := Nat }');
    assertApp(namedArg);
    expect(namedArg.argName).toBe('A');

    const namedBinder = parseExpr('{ A : Type } -> A');
    assertBinder(namedBinder);
    expect(namedBinder.named).toBe(true);
  });

  test('Parse complex scenario: id { A := Nat } Zero', () => {
    const term = parseExpr('id { A := Nat } Zero');
    // App(App(id, Nat), Zero)
    assertApp(term);
    expect(term.argName).toBeUndefined(); // Zero is positional

    assertApp(term.fn);
    expect(term.fn.argName).toBe('A'); // Nat is named

    assertConst(term.fn.fn);
    expect(term.fn.fn.name).toBe('id');
  });

  test('Shorthand: {name} expands to {name := name}', () => {
    // {A} is shorthand for {A := A} - now valid syntax!
    const term = parseExpr('f {A}');
    assertApp(term);
    expect(term.argName).toBe('A');
    // The argument is a Const 'A' (since A is not in context, treated as constant)
    assertConst(term.arg);
    expect(term.arg.name).toBe('A');
  });

  test('Error: named argument without closing brace', () => {
    expect(() => parseExpr('f { A := Nat')).toThrow();
  });

  test('Multiple named args interleaved: f { A := Nat } x { B := Bool } y', () => {
    const term = parseExpr('f { A := Nat } x { B := Bool } y');
    // Structure: App(App(App(App(f, Nat), x), Bool), y)

    // Outermost: y (positional)
    assertApp(term);
    expect(term.argName).toBeUndefined();

    // Next: Bool (named B)
    assertApp(term.fn);
    expect(term.fn.argName).toBe('B');

    // Next: x (positional)
    assertApp(term.fn.fn);
    expect(term.fn.fn.argName).toBeUndefined();

    // Next: Nat (named A)
    assertApp(term.fn.fn.fn);
    expect(term.fn.fn.fn.argName).toBe('A');
  });
});

// ============================================================================
// Named Arguments: Edge Cases
// ============================================================================

describe('Named Arguments: Edge Cases', () => {
  test('Named arg with parenthesized value', () => {
    const term = parseExpr('f { A := (x) }');
    assertApp(term);
    expect(term.argName).toBe('A');
  });

  test('Named arg with type annotation value', () => {
    const term = parseExpr('f { A := (x : Nat) }');
    assertApp(term);
    expect(term.argName).toBe('A');
    expect(term.arg.tag).toBe('Annot');
  });

  test('Named arg following operator', () => {
    const term = parseExpr('x + f { A := Nat }');
    // Should be: add(x, App(f, Nat))
    assertApp(term);
    assertApp(term.arg);
    expect(term.arg.argName).toBe('A');
  });

  test('Named arg in let binding value', () => {
    const term = parseExpr('let x = f { A := Nat } in x');
    assertBinder(term);
    // The binding value is f { A := Nat }
    expect(term.binderKind.tag).toBe('BLetTT');
    if (term.binderKind.tag === 'BLetTT') {
      assertApp(term.binderKind.defVal);
      expect(term.binderKind.defVal.argName).toBe('A');
    }
    // Body is just the variable x
    expect(term.body.tag).toBe('Var');
  });

  test('Greek letters in named argument', () => {
    const term = parseExpr('f { α := Nat }');
    assertApp(term);
    expect(term.argName).toBe('α');
  });

  test('Named argument after complex function expression', () => {
    const term = parseExpr('(\\f => f) { A := Nat }');
    assertApp(term);
    expect(term.argName).toBe('A');
    assertBinder(term.fn);
  });
});

// ============================================================================
// Named Patterns in Definitions
// ============================================================================

import { parseDeclarations } from './parser';
import { TPattern } from '../compiler/surface';

function assertPVar(p: TPattern): asserts p is Extract<TPattern, { tag: 'PVar' }> {
  expect(p.tag).toBe('PVar');
}

function assertPWild(p: TPattern): asserts p is Extract<TPattern, { tag: 'PWild' }> {
  expect(p.tag).toBe('PWild');
}

function assertPCtor(p: TPattern): asserts p is Extract<TPattern, { tag: 'PCtor' }> {
  expect(p.tag).toBe('PCtor');
}

describe('Named Patterns in Definitions', () => {
  // Note: {name} is shorthand for {name := name}, so it goes to namedPatterns

  test('Parse single named pattern: foo {A} x = x', () => {
    const decls = parseDeclarations('foo {A} x = x');
    expect(decls.length).toBe(1);
    expect(decls[0].kind).toBe('def');

    const value = decls[0].value!;
    expect(value.tag).toBe('Match');
    if (value.tag === 'Match') {
      expect(value.clauses.length).toBe(1);
      const clause = value.clauses[0];

      // Only x is a positional pattern
      expect(clause.patterns.length).toBe(1);
      assertPCtor(clause.patterns[0]);
      expect(clause.patterns[0].name).toBe('x');

      // {A} shorthand goes to namedPatterns as {A := A}
      expect(clause.namedPatterns).toBeDefined();
      expect(clause.namedPatterns!.length).toBe(1);
      expect(clause.namedPatterns![0].name).toBe('A');
      assertPVar(clause.namedPatterns![0].pattern);
      expect(clause.namedPatterns![0].pattern.name).toBe('A');
    }
  });

  test('Parse named wildcard pattern: foo {_} x = x', () => {
    const decls = parseDeclarations('foo {_} x = x');
    expect(decls.length).toBe(1);

    const value = decls[0].value!;
    if (value.tag === 'Match') {
      const patterns = value.clauses[0].patterns;
      // {_} is a named wildcard - stays in patterns array
      assertPWild(patterns[0]);
      expect(patterns[0].named).toBe(true);
    }
  });

  test('Parse multiple named patterns: foo {A} {B} x = x', () => {
    const decls = parseDeclarations('foo {A} {B} x = x');
    expect(decls.length).toBe(1);

    const value = decls[0].value!;
    if (value.tag === 'Match') {
      const clause = value.clauses[0];

      // Only x is a positional pattern
      expect(clause.patterns.length).toBe(1);
      assertPCtor(clause.patterns[0]);
      expect(clause.patterns[0].name).toBe('x');

      // {A} and {B} are in namedPatterns
      expect(clause.namedPatterns).toBeDefined();
      expect(clause.namedPatterns!.length).toBe(2);
      expect(clause.namedPatterns![0].name).toBe('A');
      expect(clause.namedPatterns![1].name).toBe('B');
    }
  });

  test('Parse mixed named and positional patterns', () => {
    const decls = parseDeclarations('foo x {A} y {B} = x');
    expect(decls.length).toBe(1);

    const value = decls[0].value!;
    if (value.tag === 'Match') {
      const clause = value.clauses[0];

      // x and y are positional patterns
      expect(clause.patterns.length).toBe(2);
      assertPCtor(clause.patterns[0]);
      expect(clause.patterns[0].name).toBe('x');
      assertPCtor(clause.patterns[1]);
      expect(clause.patterns[1].name).toBe('y');

      // {A} and {B} are in namedPatterns
      expect(clause.namedPatterns).toBeDefined();
      expect(clause.namedPatterns!.length).toBe(2);
      expect(clause.namedPatterns![0].name).toBe('A');
      expect(clause.namedPatterns![1].name).toBe('B');
    }
  });

  test('Named patterns with constructor patterns', () => {
    const decls = parseDeclarations('foo {A} (Succ n) = n');
    expect(decls.length).toBe(1);

    const value = decls[0].value!;
    if (value.tag === 'Match') {
      const clause = value.clauses[0];

      // Only (Succ n) is a positional pattern
      expect(clause.patterns.length).toBe(1);
      assertPCtor(clause.patterns[0]);
      expect(clause.patterns[0].name).toBe('Succ');
      expect(clause.patterns[0].args.length).toBe(1);

      // {A} is in namedPatterns
      expect(clause.namedPatterns).toBeDefined();
      expect(clause.namedPatterns!.length).toBe(1);
      expect(clause.namedPatterns![0].name).toBe('A');
    }
  });

  test('Named patterns preserve positional undefined', () => {
    const decls = parseDeclarations('foo x = x');
    expect(decls.length).toBe(1);

    const value = decls[0].value!;
    if (value.tag === 'Match') {
      const pattern = value.clauses[0].patterns[0];
      assertPCtor(pattern);
      // Positional patterns should NOT have named: true
      expect((pattern as any).named).toBeUndefined();
    }
  });

  test('Greek letters in named patterns', () => {
    const decls = parseDeclarations('foo {α} x = x');
    expect(decls.length).toBe(1);

    const value = decls[0].value!;
    if (value.tag === 'Match') {
      const clause = value.clauses[0];
      // {α} is in namedPatterns
      expect(clause.namedPatterns).toBeDefined();
      expect(clause.namedPatterns!.length).toBe(1);
      expect(clause.namedPatterns![0].name).toBe('α');
      assertPVar(clause.namedPatterns![0].pattern);
      expect(clause.namedPatterns![0].pattern.name).toBe('α');
    }
  });

  test('Error: empty named pattern', () => {
    expect(() => parseDeclarations('foo {} x = x')).toThrow();
  });

  test('Error: named pattern without closing brace', () => {
    expect(() => parseDeclarations('foo {A x = x')).toThrow();
  });
});

// ============================================================================
// Named Patterns: Edge Cases
// ============================================================================

describe('Named Patterns: Edge Cases', () => {
  test('Named pattern followed by constructor application', () => {
    // {A} is shorthand for {A := A}, so it goes to namedPatterns
    const decls = parseDeclarations('foo {A} Zero = A');
    expect(decls.length).toBe(1);

    const value = decls[0].value!;
    if (value.tag === 'Match') {
      const clause = value.clauses[0];
      // {A} is now in namedPatterns, Zero is the only positional pattern
      expect(clause.patterns.length).toBe(1);
      assertPCtor(clause.patterns[0]);
      expect(clause.patterns[0].name).toBe('Zero');

      // {A} shorthand expands to {A := A}
      expect(clause.namedPatterns).toBeDefined();
      expect(clause.namedPatterns!.length).toBe(1);
      expect(clause.namedPatterns![0].name).toBe('A');
      assertPVar(clause.namedPatterns![0].pattern);
      expect(clause.namedPatterns![0].pattern.name).toBe('A');
    }
  });

  test('Named pattern as constructor argument', () => {
    // This is a nested scenario: Pair {A} x
    // Inside a constructor pattern, {A} becomes a namedArg
    const decls = parseDeclarations('foo (Pair {A} x) = x');
    expect(decls.length).toBe(1);

    const value = decls[0].value!;
    if (value.tag === 'Match') {
      const pattern = value.clauses[0].patterns[0];
      assertPCtor(pattern);
      expect(pattern.name).toBe('Pair');
      // Only x is a positional arg
      expect(pattern.args.length).toBe(1);
      assertPCtor(pattern.args[0]);
      expect(pattern.args[0].name).toBe('x');

      // {A} is in namedArgs
      expect(pattern.namedArgs).toBeDefined();
      expect(pattern.namedArgs!.length).toBe(1);
      expect(pattern.namedArgs![0].name).toBe('A');
      assertPVar(pattern.namedArgs![0].pattern);
    }
  });

  test('Named wildcard in constructor', () => {
    const decls = parseDeclarations('foo (Succ {_}) = Zero');
    expect(decls.length).toBe(1);

    const value = decls[0].value!;
    if (value.tag === 'Match') {
      const pattern = value.clauses[0].patterns[0];
      assertPCtor(pattern);
      // {_} is a named wildcard - still goes to args but with named: true
      expect(pattern.args.length).toBe(1);

      assertPWild(pattern.args[0]);
      expect(pattern.args[0].named).toBe(true);
    }
  });

  test('Multiple clauses with named patterns', () => {
    // {A} is shorthand for {A := A}
    const decls = parseDeclarations(`
      foo {A} Zero = A
      foo {A} (Succ n) = n
    `);
    expect(decls.length).toBe(1);

    const value = decls[0].value!;
    if (value.tag === 'Match') {
      expect(value.clauses.length).toBe(2);

      // Both clauses should have {A} in namedPatterns
      for (const clause of value.clauses) {
        expect(clause.namedPatterns).toBeDefined();
        expect(clause.namedPatterns!.length).toBe(1);
        expect(clause.namedPatterns![0].name).toBe('A');
        assertPVar(clause.namedPatterns![0].pattern);
        expect(clause.namedPatterns![0].pattern.name).toBe('A');
      }
    }
  });
});
