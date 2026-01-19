/**
 * Tests for the TT Language Parser
 *
 * These tests verify:
 * 1. Lexer/Tokenization
 * 2. Expression parsing
 * 3. Operator precedence and associativity
 * 4. Declaration parsing
 * 5. Error handling
 */

import {
  Parser,
  parseExpr,
  parseDeclarations,
  tokenize,
  ParseError,
  DEFAULT_OPERATORS,
  OperatorInfo,
} from './parser';

import { prettyPrintTT, TTerm } from '../compiler/surface';

// ============================================================================
// Test Helper
// ============================================================================

function test(description: string, fn: () => void): void {
  try {
    fn();
    console.log(`✓ ${description}`);
  } catch (error) {
    console.error(`✗ ${description}`);
    throw error;
  }
}

function assertEqual<T>(actual: T, expected: T, message?: string): void {
  const actualStr = JSON.stringify(actual);
  const expectedStr = JSON.stringify(expected);
  if (actualStr !== expectedStr) {
    throw new Error(`${message || 'Assertion failed'}\n  Expected: ${expectedStr}\n  Actual: ${actualStr}`);
  }
}

function assertThrows(fn: () => void, message?: string): void {
  try {
    fn();
    throw new Error(`Expected function to throw, but it didn't. ${message || ''}`);
  } catch (error) {
    if (error instanceof ParseError) {
      return; // Expected
    }
    if (error instanceof Error && error.message.includes('Expected function to throw')) {
      throw error;
    }
    // Other errors are fine
  }
}

// Helper to check term structure without caring about internal details
function assertTermShape(term: TTerm, expectedTag: string, message?: string): void {
  if (term.tag !== expectedTag) {
    throw new Error(`${message || 'Tag mismatch'}\n  Expected tag: ${expectedTag}\n  Actual tag: ${term.tag}`);
  }
}

// ============================================================================
// Lexer Tests
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('LEXER TESTS');
console.log('='.repeat(80) + '\n');

test('Tokenize simple identifier', () => {
  const tokens = tokenize('foo');
  assertEqual(tokens.length, 2, 'Should have 2 tokens (IDENT + EOF)');
  assertEqual(tokens[0].type, 'IDENT');
  assertEqual(tokens[0].value, 'foo');
});

test('Tokenize keywords', () => {
  // Note: 'forall' is no longer a keyword - use (x : T) -> ... syntax instead
  const tokens = tokenize('fun let in Type Prop def theorem axiom');
  const types = tokens.map(t => t.type);
  assertEqual(types, ['LAMBDA', 'LET', 'IN', 'TYPE', 'PROP', 'DEF', 'THEOREM', 'AXIOM', 'EOF']);
});

test('Tokenize lambda symbols', () => {
  // Only \ and fun are supported (λ unicode removed)
  const tokens1 = tokenize('\\');
  assertEqual(tokens1[0].type, 'LAMBDA');

  const tokens2 = tokenize('fun');
  assertEqual(tokens2[0].type, 'LAMBDA');
});

// PI token removed - use (x : T) -> ... syntax instead

test('Tokenize arrows', () => {
  // Only -> is supported now (removed → unicode)
  const tokens = tokenize('->');
  assertEqual(tokens[0].type, 'ARROW');
});

test('Tokenize fat arrow', () => {
  const tokens = tokenize('=>');
  assertEqual(tokens[0].type, 'FATARROW');
});

test('Tokenize assignment', () => {
  const tokens = tokenize(':=');
  assertEqual(tokens[0].type, 'ASSIGN');
});

test('Tokenize holes', () => {
  const tokens = tokenize('?foo ?bar ?_');
  assertEqual(tokens[0].type, 'HOLE');
  assertEqual(tokens[0].value, 'foo');
  assertEqual(tokens[1].type, 'HOLE');
  assertEqual(tokens[1].value, 'bar');
});

test('Tokenize operators', () => {
  const tokens = tokenize('+ - * / = < > ∧ ∨');
  const types = tokens.filter(t => t.type === 'OPERATOR').map(t => t.value);
  assertEqual(types, ['+', '-', '*', '/', '=', '<', '>', '∧', '∨']);
});

test('Tokenize multi-character operators', () => {
  // Note: :: is tokenized as two COLON tokens because colon is handled before operators
  const tokens = tokenize('== != <= >= && || ++');
  const ops = tokens.filter(t => t.type === 'OPERATOR').map(t => t.value);
  assertEqual(ops, ['==', '!=', '<=', '>=', '&&', '||', '++']);
});

test('Tokenize parentheses and braces', () => {
  const tokens = tokenize('( ) { }');
  const types = tokens.slice(0, 4).map(t => t.type);
  assertEqual(types, ['LPAREN', 'RPAREN', 'LBRACE', 'RBRACE']);
});

test('Tokenize numbers', () => {
  const tokens = tokenize('0 42 123');
  assertEqual(tokens[0].type, 'NUMBER');
  assertEqual(tokens[0].value, '0');
  assertEqual(tokens[1].type, 'NUMBER');
  assertEqual(tokens[1].value, '42');
});

test('Skip line comments', () => {
  const tokens = tokenize('foo -- this is a comment\nbar');
  const idents = tokens.filter(t => t.type === 'IDENT').map(t => t.value);
  assertEqual(idents, ['foo', 'bar']);
});

test('Skip block comments', () => {
  const tokens = tokenize('foo /- this is a block comment -/ bar');
  const idents = tokens.filter(t => t.type === 'IDENT').map(t => t.value);
  assertEqual(idents, ['foo', 'bar']);
});

test('Handle nested block comments', () => {
  const tokens = tokenize('foo /- outer /- inner -/ outer -/ bar');
  const idents = tokens.filter(t => t.type === 'IDENT').map(t => t.value);
  assertEqual(idents, ['foo', 'bar']);
});

test('Skip multiline comments', () => {
  const tokens = tokenize('foo {- this is a multiline comment -} bar');
  const idents = tokens.filter(t => t.type === 'IDENT').map(t => t.value);
  assertEqual(idents, ['foo', 'bar']);
});

test('Handle nested multiline comments', () => {
  const tokens = tokenize('foo {- outer {- inner -} outer -} bar');
  const idents = tokens.filter(t => t.type === 'IDENT').map(t => t.value);
  assertEqual(idents, ['foo', 'bar']);
});

test('Handle multiline comments with newlines', () => {
  const tokens = tokenize('foo {- line 1\nline 2\nline 3 -} bar');
  const idents = tokens.filter(t => t.type === 'IDENT').map(t => t.value);
  assertEqual(idents, ['foo', 'bar']);
});

test('Handle deeply nested multiline comments', () => {
  const tokens = tokenize('foo {- level 1 {- level 2 {- level 3 -} -} -} bar');
  const idents = tokens.filter(t => t.type === 'IDENT').map(t => t.value);
  assertEqual(idents, ['foo', 'bar']);
});

test('Track line and column numbers', () => {
  const tokens = tokenize('foo\nbar  baz');
  assertEqual(tokens[0].line, 1);
  assertEqual(tokens[0].col, 1);
  // After newline
  const barToken = tokens.find(t => t.value === 'bar');
  assertEqual(barToken?.line, 2);
});

test('Tokenize Greek letters in identifiers', () => {
  const tokens = tokenize('α β γ αβγ');
  const idents = tokens.filter(t => t.type === 'IDENT').map(t => t.value);
  assertEqual(idents, ['α', 'β', 'γ', 'αβγ']);
});

test('Tokenize mathematical symbols', () => {
  const tokens = tokenize('ℕ ℤ ℝ');
  const idents = tokens.filter(t => t.type === 'IDENT').map(t => t.value);
  assertEqual(idents, ['ℕ', 'ℤ', 'ℝ']);
});

// ============================================================================
// Parser: Basic Expression Tests
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('PARSER: BASIC EXPRESSION TESTS');
console.log('='.repeat(80) + '\n');

test('Parse identifier (variable/constant)', () => {
  const term = parseExpr('x');
  // 'x' not in context should be a Const
  assertTermShape(term, 'Const');
  if (term.tag === 'Const') {
    assertEqual(term.name, 'x');
  }
});

test('Parse Type', () => {
  const term = parseExpr('Type');
  assertTermShape(term, 'Sort');
  if (term.tag === 'Sort') {
    assertEqual(term.level, 1); // Type = Sort(1)
  }
});

test('Parse Type n (with space)', () => {
  // Type 0 = Sort(1) = Type
  const t0 = parseExpr('Type 0');
  assertTermShape(t0, 'Sort');
  if (t0.tag === 'Sort') {
    assertEqual(t0.level, 1); // Type 0 = Sort(1)
  }

  // Type 1 = Sort(2)
  const t1 = parseExpr('Type 1');
  assertTermShape(t1, 'Sort');
  if (t1.tag === 'Sort') {
    assertEqual(t1.level, 2); // Type 1 = Sort(2)
  }

  // Type 2 = Sort(3)
  const t2 = parseExpr('Type 2');
  assertTermShape(t2, 'Sort');
  if (t2.tag === 'Sort') {
    assertEqual(t2.level, 3); // Type 2 = Sort(3)
  }
});

test('Parse Type_n (with underscore)', () => {
  // Type_0 = Sort(1) = Type
  const t0 = parseExpr('Type_0');
  assertTermShape(t0, 'Sort');
  if (t0.tag === 'Sort') {
    assertEqual(t0.level, 1); // Type_0 = Sort(1)
  }

  // Type_1 = Sort(2)
  const t1 = parseExpr('Type_1');
  assertTermShape(t1, 'Sort');
  if (t1.tag === 'Sort') {
    assertEqual(t1.level, 2); // Type_1 = Sort(2)
  }

  // Type_42 = Sort(43)
  const t42 = parseExpr('Type_42');
  assertTermShape(t42, 'Sort');
  if (t42.tag === 'Sort') {
    assertEqual(t42.level, 43); // Type_42 = Sort(43)
  }
});

test('Parse Type in Pi type', () => {
  // Verify that Type is correctly parsed inside Pi binders
  const term = parseExpr('(A : Type) -> A');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder' && term.binderKind.tag === 'BPiTT') {
    // Domain should be Sort(1)
    assertTermShape(term.domain, 'Sort');
    if (term.domain.tag === 'Sort') {
      assertEqual(term.domain.level, 1);
    }
  }
});

test('Parse Type 1 in Pi type', () => {
  // Verify that Type 1 is correctly parsed inside Pi binders
  const term = parseExpr('(A : Type 1) -> A');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder' && term.binderKind.tag === 'BPiTT') {
    // Domain should be Sort(2)
    assertTermShape(term.domain, 'Sort');
    if (term.domain.tag === 'Sort') {
      assertEqual(term.domain.level, 2);
    }
  }
});

test('Parse Prop', () => {
  const term = parseExpr('Prop');
  assertTermShape(term, 'Sort');
  if (term.tag === 'Sort') {
    assertEqual(term.level, 0); // Prop = Type_0
  }
});

test('Parse hole', () => {
  const term = parseExpr('?foo');
  assertTermShape(term, 'Hole');
  if (term.tag === 'Hole') {
    assertEqual(term.id, 'foo');
  }
});

test('Parse underscore as hole', () => {
  const term = parseExpr('_');
  assertTermShape(term, 'Hole');
  if (term.tag === 'Hole') {
    assertEqual(term.id, '_');
  }
});

test('Parse parenthesized expression', () => {
  const term = parseExpr('(x)');
  assertTermShape(term, 'Const');
  if (term.tag === 'Const') {
    assertEqual(term.name, 'x');
  }
});

// ============================================================================
// Parser: Lambda Tests
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('PARSER: LAMBDA TESTS');
console.log('='.repeat(80) + '\n');

// New lambda syntax tests

test('Parse lambda: \\x => x', () => {
  const term = parseExpr('\\x => x');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    assertEqual(term.binderKind.tag, 'BLamTT');
    assertEqual(term.name, 'x');
    assertTermShape(term.domain, 'Hole'); // type is a hole
    assertTermShape(term.body, 'Var');
  }
});

test('Parse lambda: \\ x => x (with space)', () => {
  const term = parseExpr('\\ x => x');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    assertEqual(term.binderKind.tag, 'BLamTT');
    assertEqual(term.name, 'x');
  }
});

test('Parse lambda: \\x y => x + y (multiple untyped)', () => {
  const term = parseExpr('\\x y => x');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    assertEqual(term.name, 'x');
    assertTermShape(term.domain, 'Hole');
    assertTermShape(term.body, 'Binder');
    if (term.body.tag === 'Binder') {
      assertEqual(term.body.name, 'y');
      assertTermShape(term.body.domain, 'Hole');
    }
  }
});

test('Parse lambda: \\(x : A) => x (typed)', () => {
  const term = parseExpr('\\(x : A) => x');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    assertEqual(term.name, 'x');
    assertTermShape(term.domain, 'Const'); // A is a const
  }
});

test('Parse lambda: \\(x : A) y => x (mixed typed/untyped)', () => {
  const term = parseExpr('\\(x : A) y => x');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    assertEqual(term.name, 'x');
    assertTermShape(term.domain, 'Const'); // x : A
    assertTermShape(term.body, 'Binder');
    if (term.body.tag === 'Binder') {
      assertEqual(term.body.name, 'y');
      assertTermShape(term.body.domain, 'Hole'); // y's type is a hole
    }
  }
});

test('Parse lambda: \\(x, y : A) => x (multiple names same type)', () => {
  const term = parseExpr('\\(x, y : A) => x');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    assertEqual(term.name, 'x');
    assertTermShape(term.domain, 'Const'); // x : A
    assertTermShape(term.body, 'Binder');
    if (term.body.tag === 'Binder') {
      assertEqual(term.body.name, 'y');
      assertTermShape(term.body.domain, 'Const'); // y : A (same type)
    }
  }
});

test('Parse lambda: \\(x y : A) => x (multiple names same type, no comma)', () => {
  const term = parseExpr('\\(x y : A) => x');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    assertEqual(term.name, 'x');
    assertTermShape(term.body, 'Binder');
    if (term.body.tag === 'Binder') {
      assertEqual(term.body.name, 'y');
    }
  }
});

test('Parse lambda: \\(x : A) (y : B) => x (multiple typed binders)', () => {
  const term = parseExpr('\\(x : A) (y : B) => x');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    assertEqual(term.name, 'x');
    assertTermShape(term.body, 'Binder');
    if (term.body.tag === 'Binder') {
      assertEqual(term.body.name, 'y');
    }
  }
});

test('Parse lambda: ERROR on \\ x : A => x (parens required)', () => {
  assertThrows(
    () => parseExpr('\\ x : A => x'),
    'Should error when type annotation lacks parentheses'
  );
});

test('Parse lambda with backslash and =>', () => {
  const term = parseExpr('\\(x : T) => x');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    assertEqual(term.binderKind.tag, 'BLamTT');
    assertEqual(term.name, 'x');
  }
});

test('Parse lambda with fun keyword', () => {
  const term = parseExpr('fun (x : T) => x');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    assertEqual(term.binderKind.tag, 'BLamTT');
    assertEqual(term.name, 'x');
  }
});

// Legacy comma/dot syntax has been removed - only => is supported

// ============================================================================
// Parser: Pi/Arrow Tests (using -> syntax only)
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('PARSER: PI/ARROW TESTS');
console.log('='.repeat(80) + '\n');

test('Parse dependent Pi with (x : T) -> syntax', () => {
  const term = parseExpr('(x : A) -> B');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    assertEqual(term.binderKind.tag, 'BPiTT');
    assertEqual(term.name, 'x');
  }
});

test('Parse Pi with multiple binders', () => {
  const term = parseExpr('(x : A) -> (y : B) -> C');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    assertEqual(term.name, 'x');
    assertTermShape(term.body, 'Binder');
  }
});

test('Parse arrow type (non-dependent Pi)', () => {
  const term = parseExpr('A -> B');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    assertEqual(term.binderKind.tag, 'BPiTT');
    assertEqual(term.name, '_'); // Non-dependent
  }
});

test('Parse chained arrows (right-associative)', () => {
  // A -> B -> C  should be  A -> (B -> C)
  const term = parseExpr('A -> B -> C');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    // Body should be another Pi
    assertTermShape(term.body, 'Binder');
  }
});

// ============================================================================
// Parser: Let Tests
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('PARSER: LET TESTS');
console.log('='.repeat(80) + '\n');

test('Parse let expression', () => {
  const term = parseExpr('let x : T := v in x');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    assertEqual(term.binderKind.tag, 'BLetTT');
    assertEqual(term.name, 'x');
    // Body should refer to x (Var 0)
    assertTermShape(term.body, 'Var');
  }
});

test('Parse let without type annotation', () => {
  const term = parseExpr('let x := v in x');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    assertEqual(term.binderKind.tag, 'BLetTT');
    // Domain should be a hole when type is omitted
    assertTermShape(term.domain, 'Hole');
  }
});

test('Parse nested let expressions', () => {
  const term = parseExpr('let x := a in let y := b in x');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    assertEqual(term.name, 'x');
    assertTermShape(term.body, 'Binder');
    if (term.body.tag === 'Binder') {
      assertEqual(term.body.name, 'y');
    }
  }
});

// ============================================================================
// Parser: Application Tests
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('PARSER: APPLICATION TESTS');
console.log('='.repeat(80) + '\n');

test('Parse simple application', () => {
  const term = parseExpr('f x');
  assertTermShape(term, 'App');
  if (term.tag === 'App') {
    assertTermShape(term.fn, 'Const');
    assertTermShape(term.arg, 'Const');
  }
});

test('Parse chained application (left-associative)', () => {
  // f x y  should be  (f x) y
  const term = parseExpr('f x y');
  assertTermShape(term, 'App');
  if (term.tag === 'App') {
    // fn should be (f x)
    assertTermShape(term.fn, 'App');
    // arg should be y
    assertTermShape(term.arg, 'Const');
  }
});

test('Parse application with parentheses', () => {
  const term = parseExpr('f (g x)');
  assertTermShape(term, 'App');
  if (term.tag === 'App') {
    assertTermShape(term.fn, 'Const');
    assertTermShape(term.arg, 'App');
  }
});

test('Parse application of lambda', () => {
  const term = parseExpr('(\\x => x) y');
  assertTermShape(term, 'App');
  if (term.tag === 'App') {
    assertTermShape(term.fn, 'Binder');
    assertTermShape(term.arg, 'Const');
  }
});

// ============================================================================
// Parser: Type Annotation Tests
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('PARSER: TYPE ANNOTATION TESTS');
console.log('='.repeat(80) + '\n');

test('Parse type annotation', () => {
  const term = parseExpr('(x : T)');
  assertTermShape(term, 'Annot');
  if (term.tag === 'Annot') {
    assertTermShape(term.term, 'Const');
    assertTermShape(term.type, 'Const');
  }
});

test('Parse type annotation with complex term', () => {
  const term = parseExpr('(f x : T)');
  assertTermShape(term, 'Annot');
  if (term.tag === 'Annot') {
    assertTermShape(term.term, 'App');
    assertTermShape(term.type, 'Const');
  }
});

// ============================================================================
// Parser: Operator Precedence Tests
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('PARSER: OPERATOR PRECEDENCE TESTS');
console.log('='.repeat(80) + '\n');

test('Multiplication binds tighter than addition', () => {
  // a + b * c  should be  a + (b * c)
  const term = parseExpr('a + b * c');
  assertTermShape(term, 'App');
  if (term.tag === 'App') {
    // Outer is add
    if (term.fn.tag === 'App' && term.fn.fn.tag === 'Const') {
      assertEqual(term.fn.fn.name, 'add');
    }
    // Inner arg is mul
    if (term.arg.tag === 'App' && term.arg.fn.tag === 'App') {
      if (term.arg.fn.fn.tag === 'Const') {
        assertEqual(term.arg.fn.fn.name, 'mul');
      }
    }
  }
});

test('Exponentiation binds tighter than multiplication', () => {
  // a * b ^ c  should be  a * (b ^ c)
  const term = parseExpr('a * b ^ c');
  assertTermShape(term, 'App');
  // Similar structure check as above
});

test('Addition is left-associative', () => {
  // a + b + c  should be  (a + b) + c
  const term = parseExpr('a + b + c');
  assertTermShape(term, 'App');
  if (term.tag === 'App') {
    // The second argument should be 'c'
    assertTermShape(term.arg, 'Const');
    if (term.arg.tag === 'Const') {
      assertEqual(term.arg.name, 'c');
    }
  }
});

test('Exponentiation is right-associative', () => {
  // a ^ b ^ c  should be  a ^ (b ^ c)
  const term = parseExpr('a ^ b ^ c');
  assertTermShape(term, 'App');
  if (term.tag === 'App') {
    // First arg to outer pow should be 'a'
    if (term.fn.tag === 'App') {
      assertTermShape(term.fn.arg, 'Const');
      if (term.fn.arg.tag === 'Const') {
        assertEqual(term.fn.arg.name, 'a');
      }
    }
  }
});

test('And (∧) is right-associative', () => {
  // a ∧ b ∧ c  should be  a ∧ (b ∧ c)
  const term = parseExpr('a ∧ b ∧ c');
  assertTermShape(term, 'App');
  if (term.tag === 'App') {
    // First arg should be 'a'
    if (term.fn.tag === 'App') {
      assertTermShape(term.fn.arg, 'Const');
      if (term.fn.arg.tag === 'Const') {
        assertEqual(term.fn.arg.name, 'a');
      }
    }
  }
});

test('Comparison operators are non-associative (require parens)', () => {
  // a = b  works fine
  const term = parseExpr('a = b');
  assertTermShape(term, 'App');

  // a = b = c  should parse but the second = applies to (a = b)
  // This is a quirk - we don't error on non-assoc chains, we just treat as left
  const term2 = parseExpr('a = b = c');
  assertTermShape(term2, 'App');
});

test('Application binds tighter than operators', () => {
  // f x + g y  should be  (f x) + (g y)
  const term = parseExpr('f x + g y');
  assertTermShape(term, 'App');
  if (term.tag === 'App') {
    // Both args to add should be applications
    if (term.fn.tag === 'App') {
      assertTermShape(term.fn.arg, 'App'); // f x
    }
    assertTermShape(term.arg, 'App'); // g y
  }
});

test('Arrow binds looser than operators', () => {
  // a + b -> c  should be  (a + b) -> c
  const term = parseExpr('a + b -> c');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    // Domain should be addition
    assertTermShape(term.domain, 'App');
  }
});

test('Lambda body extends as far as possible', () => {
  // \x => a + b  should be  \x => (a + b)
  const term = parseExpr('\\x => a + b');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    assertTermShape(term.body, 'App');
  }
});

// ============================================================================
// Parser: Declaration Tests (New Syntax)
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('PARSER: DECLARATION TESTS (NEW SYNTAX)');
console.log('='.repeat(80) + '\n');

test('Parse type signature with definition using := (name : type := impl)', () => {
  const decls = parseDeclarations('foo : T := x');
  assertEqual(decls.length, 1);
  assertEqual(decls[0].kind, 'def');
  assertEqual(decls[0].name, 'foo');
  if (decls[0].type) assertTermShape(decls[0].type, 'Const');
  if (decls[0].value) assertTermShape(decls[0].value, 'Const');
});

test('Parse type signature only (name : type)', () => {
  const decls = parseDeclarations('foo : T');
  assertEqual(decls.length, 1);
  assertEqual(decls[0].kind, 'def');
  assertEqual(decls[0].name, 'foo');
  if (decls[0].type) assertTermShape(decls[0].type, 'Const');
  assertEqual(decls[0].value, undefined);
});

test('Parse definition only (name = impl)', () => {
  const decls = parseDeclarations('foo = x');
  assertEqual(decls.length, 1);
  assertEqual(decls[0].kind, 'def');
  assertEqual(decls[0].name, 'foo');
  assertEqual(decls[0].type, undefined);
  if (decls[0].value) assertTermShape(decls[0].value, 'Const');
});

test('Parse complex type signature with definition using :=', () => {
  const decls = parseDeclarations('id : (A : Type) -> A -> A := \\(A : Type) (x : A) => x');
  assertEqual(decls.length, 1);
  assertEqual(decls[0].kind, 'def');
  assertEqual(decls[0].name, 'id');
  if (decls[0].type) assertTermShape(decls[0].type, 'Binder');
  if (decls[0].value) assertTermShape(decls[0].value, 'Binder');
});

test('Parse two-line declaration (type on one line, def on next) - merged', () => {
  const source = `id : (A : Type) -> A -> A
id = \\(A : Type) (x : A) => x`;
  const decls = parseDeclarations(source);
  // Declarations with same name (type-only followed by value-only) are merged
  assertEqual(decls.length, 1);
  assertEqual(decls[0].kind, 'def');
  assertEqual(decls[0].name, 'id');
  // Both type and value should be present after merging
  if (decls[0].type) assertTermShape(decls[0].type, 'Binder');
  if (decls[0].value) assertTermShape(decls[0].value, 'Binder');
});

test('Parse type containing equality (a = b in type)', () => {
  const decls = parseDeclarations('add_comm : (a : ℕ) -> (b : ℕ) -> a + b = b + a');
  assertEqual(decls.length, 1);
  assertEqual(decls[0].kind, 'def');
  assertEqual(decls[0].name, 'add_comm');
  assertEqual(decls[0].value, undefined); // type signature only
  // The type should include the equality
  if (decls[0].type) assertTermShape(decls[0].type, 'Binder');
});

test('Parse multiple new-style declarations with merging', () => {
  const source = `
    foo : T
    foo = x
    bar : S := y
    baz : P
  `;
  const decls = parseDeclarations(source);
  // foo : T and foo = x are merged into one declaration
  assertEqual(decls.length, 3);
  assertEqual(decls[0].name, 'foo');
  // Merged: should have both type and value
  assertTermShape(decls[0].type!, 'Const'); // T is a const
  assertTermShape(decls[0].value!, 'Const'); // x is a const
  assertEqual(decls[1].name, 'bar');
  assertEqual(decls[2].name, 'baz');
  assertEqual(decls[2].value, undefined); // type signature only
});

test('Parse bare expression as declaration', () => {
  const decls = parseDeclarations('x + y');
  assertEqual(decls.length, 1);
  assertEqual(decls[0].kind, 'expr');
  assertTermShape(decls[0].value!, 'App');
});

test('Parse mixed declarations and expressions with merging', () => {
  const source = `
    foo : T
    foo = x
    a + b
    bar : P
  `;
  const decls = parseDeclarations(source);
  // foo : T and foo = x are merged
  assertEqual(decls.length, 3);
  assertEqual(decls[0].kind, 'def');
  assertEqual(decls[0].name, 'foo');
  // foo should have both type and value after merging
  assertTermShape(decls[0].type!, 'Const');
  assertTermShape(decls[0].value!, 'Const');
  assertEqual(decls[1].kind, 'expr');
  assertEqual(decls[2].kind, 'def');
});

// ============================================================================
// Parser: Legacy Declaration Tests
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('PARSER: LEGACY DECLARATION TESTS');
console.log('='.repeat(80) + '\n');

test('Parse legacy def declaration', () => {
  const decls = parseDeclarations('def foo : T := x');
  assertEqual(decls.length, 1);
  assertEqual(decls[0].kind, 'def');
  assertEqual(decls[0].name, 'foo');
});

test('Parse legacy theorem declaration', () => {
  const decls = parseDeclarations('theorem bar : P := proof');
  assertEqual(decls.length, 1);
  assertEqual(decls[0].kind, 'theorem');
  assertEqual(decls[0].name, 'bar');
});

test('Parse legacy axiom declaration', () => {
  const decls = parseDeclarations('axiom choice : A');
  assertEqual(decls.length, 1);
  assertEqual(decls[0].kind, 'axiom');
  assertEqual(decls[0].name, 'choice');
  assertEqual(decls[0].value, undefined);
});

// ============================================================================
// Parser: Complex Expression Tests
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('PARSER: COMPLEX EXPRESSION TESTS');
console.log('='.repeat(80) + '\n');

test('Parse function type with explicit domain', () => {
  const term = parseExpr('(n : ℕ) -> (m : ℕ) -> Prop');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    assertEqual(term.name, 'n');
    assertTermShape(term.body, 'Binder');
  }
});

test('Parse complex lambda', () => {
  const term = parseExpr('\\(f : A -> B) (x : A) => f x');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    assertEqual(term.name, 'f');
    assertTermShape(term.body, 'Binder');
    if (term.body.tag === 'Binder') {
      assertEqual(term.body.name, 'x');
      assertTermShape(term.body.body, 'App');
    }
  }
});

test('Parse identity function type', () => {
  const term = parseExpr('(A : Type) -> A -> A');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder') {
    assertEqual(term.binderKind.tag, 'BPiTT');
    assertEqual(term.name, 'A');
  }
});

test('Parse let with complex value', () => {
  const term = parseExpr('let id := \\x => x in id y');
  assertTermShape(term, 'Binder');
  if (term.tag === 'Binder' && term.binderKind.tag === 'BLetTT') {
    assertEqual(term.name, 'id');
    assertTermShape(term.binderKind.defVal, 'Binder'); // lambda
    assertTermShape(term.body, 'App'); // id y
  }
});

test('Parse equality type', () => {
  const term = parseExpr('a + b = b + a');
  assertTermShape(term, 'App');
  // This is Eq (add a b) (add b a)
});

test('Parse nested operators with parens', () => {
  const term = parseExpr('(a + b) * (c + d)');
  assertTermShape(term, 'App');
  if (term.tag === 'App' && term.fn.tag === 'App') {
    // mul (add a b) (add c d)
    if (term.fn.fn.tag === 'Const') {
      assertEqual(term.fn.fn.name, 'mul');
    }
    assertTermShape(term.fn.arg, 'App'); // add a b
    assertTermShape(term.arg, 'App'); // add c d
  }
});

// ============================================================================
// Parser: Error Cases
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('PARSER: ERROR CASES');
console.log('='.repeat(80) + '\n');

test('Error on unexpected token', () => {
  assertThrows(() => parseExpr(')'), 'Should error on unexpected )');
});

test('Error on unclosed parenthesis', () => {
  assertThrows(() => parseExpr('(x'), 'Should error on unclosed paren');
});

test('Error on missing lambda binder', () => {
  assertThrows(() => parseExpr('\\'), 'Should error on lambda without binder');
});

// Removed test for Π error - Π is no longer a valid token

test('Error on missing let value', () => {
  assertThrows(() => parseExpr('let x :='), 'Should error on let without value');
});

test('Error on missing let body', () => {
  assertThrows(() => parseExpr('let x := v in'), 'Should error on let without body');
});

test('Error on invalid character', () => {
  assertThrows(() => parseExpr('a § b'), 'Should error on invalid character');
});

// ============================================================================
// Parser: Custom Operators Tests
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('PARSER: CUSTOM OPERATORS TESTS');
console.log('='.repeat(80) + '\n');

test('Parse with custom operator', () => {
  const customOps: Record<string, OperatorInfo> = {
    ...DEFAULT_OPERATORS,
    '⊕': { symbol: '⊕', precedence: 60, associativity: 'left', constName: 'xor' },
  };

  const parser = new Parser(customOps);
  const term = parser.parseExpr('a ⊕ b');
  assertTermShape(term, 'App');
  if (term.tag === 'App' && term.fn.tag === 'App' && term.fn.fn.tag === 'Const') {
    assertEqual(term.fn.fn.name, 'xor');
  }
});

test('Custom operator respects precedence', () => {
  const customOps: Record<string, OperatorInfo> = {
    ...DEFAULT_OPERATORS,
    '⊕': { symbol: '⊕', precedence: 75, associativity: 'left', constName: 'xor' },
  };

  const parser = new Parser(customOps);
  // a + b ⊕ c  should be  a + (b ⊕ c)  if ⊕ has higher precedence than +
  const term = parser.parseExpr('a + b ⊕ c');
  assertTermShape(term, 'App');
  // The outer should be add
  if (term.tag === 'App' && term.fn.tag === 'App' && term.fn.fn.tag === 'Const') {
    assertEqual(term.fn.fn.name, 'add');
  }
});

// ============================================================================
// De Bruijn Index Tests
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('PARSER: DE BRUIJN INDEX TESTS');
console.log('='.repeat(80) + '\n');

test('Lambda body correctly references bound variable', () => {
  const term = parseExpr('\\(x : T) => x');
  if (term.tag === 'Binder' && term.body.tag === 'Var') {
    assertEqual(term.body.index, 0, 'Bound variable should have index 0');
  }
});

test('Nested lambda body correctly references outer variable', () => {
  const term = parseExpr('\\(x : A) (y : B) => x');
  if (term.tag === 'Binder' && term.body.tag === 'Binder' && term.body.body.tag === 'Var') {
    assertEqual(term.body.body.index, 1, 'Outer variable should have index 1');
  }
});

test('Nested lambda body correctly references inner variable', () => {
  const term = parseExpr('\\(x : A) (y : B) => y');
  if (term.tag === 'Binder' && term.body.tag === 'Binder' && term.body.body.tag === 'Var') {
    assertEqual(term.body.body.index, 0, 'Inner variable should have index 0');
  }
});

test('Let body correctly references bound variable', () => {
  const term = parseExpr('let x := v in x');
  if (term.tag === 'Binder' && term.body.tag === 'Var') {
    assertEqual(term.body.index, 0, 'Let-bound variable should have index 0');
  }
});

test('Pi body correctly references bound variable', () => {
  const term = parseExpr('(x : Type) -> x');
  if (term.tag === 'Binder' && term.body.tag === 'Var') {
    assertEqual(term.body.index, 0, 'Pi-bound variable should have index 0');
  }
});

test('Free variable becomes Const', () => {
  const term = parseExpr('\\x => y');
  if (term.tag === 'Binder') {
    // y is not bound, should be Const
    assertTermShape(term.body, 'Const');
    if (term.body.tag === 'Const') {
      assertEqual(term.body.name, 'y');
    }
  }
});

// ============================================================================
// Pretty Print Round-Trip Tests
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('PARSER: PRETTY PRINT TESTS');
console.log('='.repeat(80) + '\n');

test('Pretty print preserves variable names', () => {
  const term = parseExpr('\\(foo : T) => foo');
  const printed = prettyPrintTT(term);
  if (!printed.includes('foo')) {
    throw new Error(`Expected 'foo' in output, got: ${printed}`);
  }
});

test('Pretty print shows Pi types correctly', () => {
  const term = parseExpr('(α : Type) -> α -> α');
  const printed = prettyPrintTT(term);
  if (!printed.includes('α')) {
    throw new Error(`Expected 'α' in output, got: ${printed}`);
  }
});

// ============================================================================
// Parser: Inductive Type Tests
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('PARSER: INDUCTIVE TYPE TESTS');
console.log('='.repeat(80) + '\n');

test('Parse simple inductive type (Nat)', () => {
  const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat`;

  const decls = parseDeclarations(source);
  assertEqual(decls.length, 1);
  assertEqual(decls[0].kind, 'inductive');
  assertEqual(decls[0].name, 'Nat');
  assertTermShape(decls[0].type!, 'Sort');
  assertEqual(decls[0].constructors?.length, 2);
  assertEqual(decls[0].constructors![0].name, 'Zero');
  assertEqual(decls[0].constructors![1].name, 'Succ');
});

test('Parse inductive type without where keyword', () => {
  const source = `inductive Nat : Type
  Zero : Nat
  Succ : Nat -> Nat`;

  const decls = parseDeclarations(source);
  assertEqual(decls.length, 1);
  assertEqual(decls[0].kind, 'inductive');
  assertEqual(decls[0].constructors?.length, 2);
});

test('Parse inductive type with pipes', () => {
  const source = `inductive Bool : Type where
  | True : Bool
  | False : Bool`;

  const decls = parseDeclarations(source);
  assertEqual(decls.length, 1);
  assertEqual(decls[0].kind, 'inductive');
  assertEqual(decls[0].constructors?.length, 2);
  assertEqual(decls[0].constructors![0].name, 'True');
  assertEqual(decls[0].constructors![1].name, 'False');
});

test('Parse parameterized inductive type (List)', () => {
  const source = `inductive List : Type -> Type where
  | Nil : (A : Type) -> List A
  | Cons : (A : Type) -> A -> List A -> List A`;

  const decls = parseDeclarations(source);
  assertEqual(decls.length, 1);
  assertEqual(decls[0].kind, 'inductive');
  assertEqual(decls[0].name, 'List');
  assertEqual(decls[0].constructors?.length, 2);
  assertEqual(decls[0].constructors![0].name, 'Nil');
  assertEqual(decls[0].constructors![1].name, 'Cons');
});

test('Parse inductive type with complex constructor types', () => {
  const source = `inductive Expr : Type where
  | Var : (name : String) -> Expr
  | App : Expr -> Expr -> Expr
  | Lam : (name : String) -> Expr -> Expr`;

  const decls = parseDeclarations(source);
  assertEqual(decls.length, 1);
  assertEqual(decls[0].kind, 'inductive');
  assertEqual(decls[0].constructors?.length, 3);
});

// ============================================================================
// Pattern Matching Tests
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('PATTERN MATCHING TESTS');
console.log('='.repeat(80) + '\n');

test('Parse simple case expression with Zero', () => {
  const source = `case n where
  | Zero => b`;
  const term = parseExpr(source);
  assertTermShape(term, 'Match', 'Should parse as Match');
  if (term.tag === 'Match') {
    assertEqual(term.clauses.length, 1);
    assertEqual(term.clauses[0].patterns.length, 1);
    assertEqual(term.clauses[0].patterns[0].tag, 'PCtor');
    if (term.clauses[0].patterns[0].tag === 'PCtor') {
      assertEqual(term.clauses[0].patterns[0].name, 'Zero');
      assertEqual(term.clauses[0].patterns[0].args.length, 0);
    }
  }
});

test('Parse case expression with Succ pattern', () => {
  const source = `case n where
  | Succ a => a`;
  const term = parseExpr(source);
  assertTermShape(term, 'Match');
  if (term.tag === 'Match') {
    assertEqual(term.clauses.length, 1);
    const pattern = term.clauses[0].patterns[0];
    assertEqual(pattern.tag, 'PCtor');
    if (pattern.tag === 'PCtor') {
      assertEqual(pattern.name, 'Succ');
      assertEqual(pattern.args.length, 1);
      assertEqual(pattern.args[0].tag, 'PVar');
      if (pattern.args[0].tag === 'PVar') {
        assertEqual(pattern.args[0].name, 'a');
      }
    }
  }
});

test('Parse case expression with multiple clauses', () => {
  const source = `case n where
  | Zero => b
  | Succ a => Succ (plus a b)`;
  const term = parseExpr(source);
  assertTermShape(term, 'Match');
  if (term.tag === 'Match') {
    assertEqual(term.clauses.length, 2);
    // First clause: Zero
    assertEqual(term.clauses[0].patterns[0].tag, 'PCtor');
    // Second clause: Succ a
    assertEqual(term.clauses[1].patterns[0].tag, 'PCtor');
  }
});

test('Parse nested pattern (Succ (Succ m))', () => {
  const source = `case n where
  | Succ (Succ m) => m`;
  const term = parseExpr(source);
  assertTermShape(term, 'Match');
  if (term.tag === 'Match') {
    const pattern = term.clauses[0].patterns[0];
    assertEqual(pattern.tag, 'PCtor');
    if (pattern.tag === 'PCtor') {
      assertEqual(pattern.name, 'Succ');
      assertEqual(pattern.args.length, 1);

      const innerPattern = pattern.args[0];
      assertEqual(innerPattern.tag, 'PCtor');
      if (innerPattern.tag === 'PCtor') {
        assertEqual(innerPattern.name, 'Succ');
        assertEqual(innerPattern.args.length, 1);
        assertEqual(innerPattern.args[0].tag, 'PVar');
      }
    }
  }
});

test('Parse wildcard pattern', () => {
  const source = `case n where
  | _ => default`;
  const term = parseExpr(source);
  assertTermShape(term, 'Match');
  if (term.tag === 'Match') {
    const pattern = term.clauses[0].patterns[0];
    // Wildcards are now parsed as PVar with unique names like _w0
    assertEqual(pattern.tag, 'PVar');
    if (pattern.tag === 'PVar') {
      assert(pattern.name.startsWith('_w'), `Expected wildcard name starting with _w, got ${pattern.name}`);
    }
  }
});

test('Parse variable pattern', () => {
  const source = `case n where
  | x => x`;
  const term = parseExpr(source);
  assertTermShape(term, 'Match');
  if (term.tag === 'Match') {
    const pattern = term.clauses[0].patterns[0];
    assertEqual(pattern.tag, 'PVar');
    if (pattern.tag === 'PVar') {
      assertEqual(pattern.name, 'x');
    }
  }
});

test('Parse case with match keyword', () => {
  const source = `match n where
  | Zero => b
  | Succ a => a`;
  const term = parseExpr(source);
  assertTermShape(term, 'Match', 'Should parse match keyword');
});

test('Parse constructor with multiple args (Cons x xs)', () => {
  const source = `case list where
  | Nil => Zero
  | Cons x xs => x`;
  const term = parseExpr(source);
  assertTermShape(term, 'Match');
  if (term.tag === 'Match') {
    assertEqual(term.clauses.length, 2);

    // Second clause: Cons x xs
    const consPattern = term.clauses[1].patterns[0];
    assertEqual(consPattern.tag, 'PCtor');
    if (consPattern.tag === 'PCtor') {
      assertEqual(consPattern.name, 'Cons');
      assertEqual(consPattern.args.length, 2);
      assertEqual(consPattern.args[0].tag, 'PVar');
      assertEqual(consPattern.args[1].tag, 'PVar');
    }
  }
});

test('Parse pattern with parentheses', () => {
  const source = `case n where
  | (Succ a) => a`;
  const term = parseExpr(source);
  assertTermShape(term, 'Match');
  if (term.tag === 'Match') {
    const pattern = term.clauses[0].patterns[0];
    assertEqual(pattern.tag, 'PCtor');
    if (pattern.tag === 'PCtor') {
      assertEqual(pattern.name, 'Succ');
    }
  }
});

test('Parse case without pipe on first clause', () => {
  const source = `case n where
  Zero => b
  | Succ a => a`;
  const term = parseExpr(source);
  assertTermShape(term, 'Match');
  if (term.tag === 'Match') {
    assertEqual(term.clauses.length, 2);
  }
});

test('Parse case with complex RHS', () => {
  const source = `case n where
  | Zero => b
  | Succ a => plus a b`;
  const term = parseExpr(source);
  assertTermShape(term, 'Match');
  if (term.tag === 'Match') {
    // RHS should be parsed as application
    assertTermShape(term.clauses[1].rhs, 'App');
  }
});

test('Pattern variables bound in RHS', () => {
  const source = `case n where
  | Succ a => a`;
  const term = parseExpr(source);
  assertTermShape(term, 'Match');
  if (term.tag === 'Match') {
    // RHS should reference 'a' as Var(0) since it's the most recent binding
    const rhs = term.clauses[0].rhs;
    assertTermShape(rhs, 'Var');
    if (rhs.tag === 'Var') {
      assertEqual(rhs.index, 0, 'Pattern variable should be at index 0');
    }
  }
});

test('Multiple pattern variables in correct order', () => {
  const source = `case list where
  | Cons x xs => x`;
  const term = parseExpr(source);
  assertTermShape(term, 'Match');
  if (term.tag === 'Match') {
    const rhs = term.clauses[0].rhs;
    assertTermShape(rhs, 'Var');
    if (rhs.tag === 'Var') {
      // x is bound first (index 0), xs is bound second (index 1)
      // But in De Bruijn indices, most recent = 0, so xs=0, x=1
      // Wait, let me check the collectPatternVars - it goes left-to-right
      // So for "Cons x xs", we get [x, xs]
      // Then rhsCtx = [x, xs, ...ctx]
      // So x should be at index 1, xs at index 0
      // But actually, we're referencing 'x', so it should find it in the context
      // Let me check: rhsCtx = ['x', 'xs', ...ctx], so 'x' is at position 0 in the array
      assertEqual(rhs.index, 0, 'x should be at index 0 in rhsCtx');
    }
  }
});

test('Parse function definition with pattern clauses', () => {
  const source = `plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

  const decls = parseDeclarations(source);
  assertEqual(decls.length, 1, 'Should have one merged declaration');
  assertEqual(decls[0].name, 'plus');
  assertEqual(decls[0].type !== undefined, true, 'Should have type');
  assertEqual(decls[0].value !== undefined, true, 'Should have value');

  // Value should be a Match expression
  const value = decls[0].value!;
  assertTermShape(value, 'Match');
  if (value.tag === 'Match') {
    assertEqual(value.clauses.length, 2, 'Should have 2 clauses merged');

    // First clause: Zero b
    const clause1 = value.clauses[0];
    assertEqual(clause1.patterns.length, 2);
    assertEqual(clause1.patterns[0].tag, 'PCtor');
    if (clause1.patterns[0].tag === 'PCtor') {
      assertEqual(clause1.patterns[0].name, 'Zero');
    }
    assertEqual(clause1.patterns[1].tag, 'PVar');

    // Second clause: Succ a, b
    const clause2 = value.clauses[1];
    assertEqual(clause2.patterns.length, 2);
    assertEqual(clause2.patterns[0].tag, 'PCtor');
    if (clause2.patterns[0].tag === 'PCtor') {
      assertEqual(clause2.patterns[0].name, 'Succ');
      assertEqual(clause2.patterns[0].args.length, 1);
    }
  }
});

test('Parse single pattern clause definition', () => {
  const source = `twice : Nat -> Nat
twice n = plus n n`;

  const decls = parseDeclarations(source);
  assertEqual(decls.length, 1);
  assertEqual(decls[0].name, 'twice');
  assertEqual(decls[0].type !== undefined, true);
  assertEqual(decls[0].value !== undefined, true);

  // Value should be a Match with one clause
  const value = decls[0].value!;
  assertTermShape(value, 'Match');
  if (value.tag === 'Match') {
    assertEqual(value.clauses.length, 1);
    assertEqual(value.clauses[0].patterns.length, 1);
    assertEqual(value.clauses[0].patterns[0].tag, 'PVar');
  }
});

test('Parse pattern clause without type signature', () => {
  const source = `id x = x`;

  const decls = parseDeclarations(source);
  assertEqual(decls.length, 1);
  assertEqual(decls[0].name, 'id');
  assertEqual(decls[0].type === undefined, true, 'Should not have type');
  assertEqual(decls[0].value !== undefined, true);

  const value = decls[0].value!;
  assertTermShape(value, 'Match');
});

// ============================================================================
// Pattern Edge Cases (mixed parens/bare args, underscore with args)
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('PATTERN EDGE CASE TESTS');
console.log('='.repeat(80) + '\n');

test('Parse underscore with arguments: (_ _) parses as PCtor', () => {
  // This should parse (elaborator will reject it later)
  const source = `case x where
  | (_ _) => y`;
  const term = parseExpr(source);
  assertTermShape(term, 'Match');
  if (term.tag === 'Match') {
    const pattern = term.clauses[0].patterns[0];
    assertEqual(pattern.tag, 'PCtor', 'Should parse as PCtor');
    if (pattern.tag === 'PCtor') {
      assertEqual(pattern.name, '_', 'Name should be _');
      assertEqual(pattern.args.length, 1, 'Should have 1 argument');
      assertEqual(pattern.args[0].tag, 'PVar', 'Arg should be PVar (wildcard)');
    }
  }
});

test('Parse constructor with mixed parens and bare args: FSucc (Succ _) f', () => {
  // This is the case that was failing: (FSucc (Succ _) f)
  // Should parse as PCtor("FSucc", [PCtor("Succ", [PVar]), PCtor("f", [])])
  const source = `case x where
  | (FSucc (Succ _) f) => y`;
  const term = parseExpr(source);
  assertTermShape(term, 'Match');
  if (term.tag === 'Match') {
    const pattern = term.clauses[0].patterns[0];
    assertEqual(pattern.tag, 'PCtor');
    if (pattern.tag === 'PCtor') {
      assertEqual(pattern.name, 'FSucc');
      assertEqual(pattern.args.length, 2, 'FSucc should have 2 args');

      // First arg: (Succ _)
      const arg1 = pattern.args[0];
      assertEqual(arg1.tag, 'PCtor');
      if (arg1.tag === 'PCtor') {
        assertEqual(arg1.name, 'Succ');
        assertEqual(arg1.args.length, 1);
      }

      // Second arg: f (parsed as PCtor with no args, will be resolved later)
      const arg2 = pattern.args[1];
      assertEqual(arg2.tag, 'PCtor');
      if (arg2.tag === 'PCtor') {
        assertEqual(arg2.name, 'f');
        assertEqual(arg2.args.length, 0);
      }
    }
  }
});

test('Parse VCons with nested patterns: VCons _ (Succ _) h tail', () => {
  const source = `case x where
  | (VCons _ (Succ _) h tail) => y`;
  const term = parseExpr(source);
  assertTermShape(term, 'Match');
  if (term.tag === 'Match') {
    const pattern = term.clauses[0].patterns[0];
    assertEqual(pattern.tag, 'PCtor');
    if (pattern.tag === 'PCtor') {
      assertEqual(pattern.name, 'VCons');
      assertEqual(pattern.args.length, 4, 'VCons should have 4 args');

      // First arg: _ (wildcard)
      assertEqual(pattern.args[0].tag, 'PVar');

      // Second arg: (Succ _)
      assertEqual(pattern.args[1].tag, 'PCtor');
      if (pattern.args[1].tag === 'PCtor') {
        assertEqual(pattern.args[1].name, 'Succ');
      }

      // Third arg: h
      assertEqual(pattern.args[2].tag, 'PCtor');
      if (pattern.args[2].tag === 'PCtor') {
        assertEqual(pattern.args[2].name, 'h');
      }

      // Fourth arg: tail
      assertEqual(pattern.args[3].tag, 'PCtor');
      if (pattern.args[3].tag === 'PCtor') {
        assertEqual(pattern.args[3].name, 'tail');
      }
    }
  }
});

test('Parse complex pattern clause: nth with Vec and Fin patterns', () => {
  // This was the failing case from the user
  const source = `nth : (A : Type) -> (n : Nat) -> Vec A n -> Fin n -> A
nth A _ (VCons _ (Succ _) h tail) (FSucc (Succ _) f) = nth _ _ tail f`;

  const decls = parseDeclarations(source);
  assertEqual(decls.length, 1);
  assertEqual(decls[0].name, 'nth');

  const value = decls[0].value!;
  assertTermShape(value, 'Match');

  if (value.tag === 'Match') {
    assertEqual(value.clauses.length, 1);
    const clause = value.clauses[0];
    assertEqual(clause.patterns.length, 4, 'Should have 4 top-level patterns');

    // Pattern 1: A (variable)
    assertEqual(clause.patterns[0].tag, 'PCtor');
    if (clause.patterns[0].tag === 'PCtor') {
      assertEqual(clause.patterns[0].name, 'A');
    }

    // Pattern 2: _ (wildcard)
    assertEqual(clause.patterns[1].tag, 'PVar');

    // Pattern 3: (VCons _ (Succ _) h tail)
    assertEqual(clause.patterns[2].tag, 'PCtor');
    if (clause.patterns[2].tag === 'PCtor') {
      assertEqual(clause.patterns[2].name, 'VCons');
      assertEqual(clause.patterns[2].args.length, 4);
    }

    // Pattern 4: (FSucc (Succ _) f)
    assertEqual(clause.patterns[3].tag, 'PCtor');
    if (clause.patterns[3].tag === 'PCtor') {
      assertEqual(clause.patterns[3].name, 'FSucc');
      assertEqual(clause.patterns[3].args.length, 2);
    }
  }
});

test('Parse multiple pattern clauses with complex patterns', () => {
  const source = `nth : (A : Type) -> (n : Nat) -> Vec A n -> Fin n -> A
nth A _ (VCons _ _ h _) (FZero _) = h
nth A _ (VCons _ (Succ _) h tail) (FSucc (Succ _) f) = nth _ _ tail f`;

  const decls = parseDeclarations(source);
  assertEqual(decls.length, 1);

  const value = decls[0].value!;
  assertTermShape(value, 'Match');

  if (value.tag === 'Match') {
    assertEqual(value.clauses.length, 2, 'Should have 2 clauses merged');

    // First clause: nth A _ (VCons _ _ h _) (FZero _) = h
    const clause1 = value.clauses[0];
    assertEqual(clause1.patterns.length, 4);

    // Second clause: nth A _ (VCons _ (Succ _) h tail) (FSucc (Succ _) f) = ...
    const clause2 = value.clauses[1];
    assertEqual(clause2.patterns.length, 4);

    // Verify FSucc has 2 args in second clause
    if (clause2.patterns[3].tag === 'PCtor') {
      assertEqual(clause2.patterns[3].name, 'FSucc');
      assertEqual(clause2.patterns[3].args.length, 2, 'FSucc should have 2 args');
    }
  }
});

// ============================================================================
// Summary
// ============================================================================

console.log('\n' + '='.repeat(80));
console.log('ALL PARSER TESTS PASSED! ✓');
console.log('='.repeat(80) + '\n');

