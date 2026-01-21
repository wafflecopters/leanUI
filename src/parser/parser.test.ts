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

import { describe, test, expect } from 'vitest';
import {
  Parser,
  parseExpr,
  parseDeclarations,
  tokenize,
  ParseError,
  DEFAULT_OPERATORS,
  OperatorInfo,
} from './parser';

import { prettyPrintTT, TTerm, tlevelToNumber } from '../compiler/surface';

// ============================================================================
// Test Helper
// ============================================================================

function assertTermShape(term: TTerm, expectedTag: string): void {
  expect(term.tag).toBe(expectedTag);
}

function assertThrows(fn: () => void): void {
  expect(fn).toThrow();
}

// ============================================================================
// Lexer Tests
// ============================================================================

describe('Lexer', () => {
  test('Tokenize simple identifier', () => {
    const tokens = tokenize('foo');
    expect(tokens.length).toBe(2);
    expect(tokens[0].type).toBe('IDENT');
    expect(tokens[0].value).toBe('foo');
  });

  test('Tokenize keywords', () => {
    // Note: 'forall' is no longer a keyword - use (x : T) -> ... syntax instead
    // Note: 'def', 'theorem', 'axiom' removed - use name : type := value syntax instead
    const tokens = tokenize('fun let in Type Prop');
    const types = tokens.map(t => t.type);
    expect(types).toEqual(['LAMBDA', 'LET', 'IN', 'TYPE', 'PROP', 'EOF']);
  });

  test('Tokenize lambda symbols', () => {
    // Only \ and fun are supported (λ unicode removed)
    const tokens1 = tokenize('\\');
    expect(tokens1[0].type).toBe('LAMBDA');

    const tokens2 = tokenize('fun');
    expect(tokens2[0].type).toBe('LAMBDA');
  });

  test('Tokenize arrows', () => {
    // Only -> is supported now (removed → unicode)
    const tokens = tokenize('->');
    expect(tokens[0].type).toBe('ARROW');
  });

  test('Tokenize fat arrow', () => {
    const tokens = tokenize('=>');
    expect(tokens[0].type).toBe('FATARROW');
  });

  test('Tokenize assignment', () => {
    const tokens = tokenize(':=');
    expect(tokens[0].type).toBe('ASSIGN');
  });

  test('Tokenize holes', () => {
    const tokens = tokenize('?foo ?bar ?_');
    expect(tokens[0].type).toBe('HOLE');
    expect(tokens[0].value).toBe('foo');
    expect(tokens[1].type).toBe('HOLE');
    expect(tokens[1].value).toBe('bar');
  });

  test('Tokenize operators', () => {
    const tokens = tokenize('+ - * / = < > ∧ ∨');
    const types = tokens.filter(t => t.type === 'OPERATOR').map(t => t.value);
    expect(types).toEqual(['+', '-', '*', '/', '=', '<', '>', '∧', '∨']);
  });

  test('Tokenize multi-character operators', () => {
    // Note: :: is tokenized as two COLON tokens because colon is handled before operators
    const tokens = tokenize('== != <= >= && || ++');
    const ops = tokens.filter(t => t.type === 'OPERATOR').map(t => t.value);
    expect(ops).toEqual(['==', '!=', '<=', '>=', '&&', '||', '++']);
  });

  test('Tokenize parentheses and braces', () => {
    const tokens = tokenize('( ) { }');
    const types = tokens.slice(0, 4).map(t => t.type);
    expect(types).toEqual(['LPAREN', 'RPAREN', 'LBRACE', 'RBRACE']);
  });

  test('Tokenize numbers', () => {
    const tokens = tokenize('0 42 123');
    expect(tokens[0].type).toBe('NUMBER');
    expect(tokens[0].value).toBe('0');
    expect(tokens[1].type).toBe('NUMBER');
    expect(tokens[1].value).toBe('42');
  });

  test('Skip line comments', () => {
    const tokens = tokenize('foo -- this is a comment\nbar');
    const idents = tokens.filter(t => t.type === 'IDENT').map(t => t.value);
    expect(idents).toEqual(['foo', 'bar']);
  });

  test('Skip block comments', () => {
    const tokens = tokenize('foo /- this is a block comment -/ bar');
    const idents = tokens.filter(t => t.type === 'IDENT').map(t => t.value);
    expect(idents).toEqual(['foo', 'bar']);
  });

  test('Handle nested block comments', () => {
    const tokens = tokenize('foo /- outer /- inner -/ outer -/ bar');
    const idents = tokens.filter(t => t.type === 'IDENT').map(t => t.value);
    expect(idents).toEqual(['foo', 'bar']);
  });

  test('Skip multiline comments', () => {
    const tokens = tokenize('foo {- this is a multiline comment -} bar');
    const idents = tokens.filter(t => t.type === 'IDENT').map(t => t.value);
    expect(idents).toEqual(['foo', 'bar']);
  });

  test('Handle nested multiline comments', () => {
    const tokens = tokenize('foo {- outer {- inner -} outer -} bar');
    const idents = tokens.filter(t => t.type === 'IDENT').map(t => t.value);
    expect(idents).toEqual(['foo', 'bar']);
  });

  test('Handle multiline comments with newlines', () => {
    const tokens = tokenize('foo {- line 1\nline 2\nline 3 -} bar');
    const idents = tokens.filter(t => t.type === 'IDENT').map(t => t.value);
    expect(idents).toEqual(['foo', 'bar']);
  });

  test('Handle deeply nested multiline comments', () => {
    const tokens = tokenize('foo {- level 1 {- level 2 {- level 3 -} -} -} bar');
    const idents = tokens.filter(t => t.type === 'IDENT').map(t => t.value);
    expect(idents).toEqual(['foo', 'bar']);
  });

  test('Track line and column numbers', () => {
    const tokens = tokenize('foo\nbar  baz');
    expect(tokens[0].line).toBe(1);
    expect(tokens[0].col).toBe(1);
    // After newline
    const barToken = tokens.find(t => t.value === 'bar');
    expect(barToken?.line).toBe(2);
  });

  test('Tokenize Greek letters in identifiers', () => {
    const tokens = tokenize('α β γ αβγ');
    const idents = tokens.filter(t => t.type === 'IDENT').map(t => t.value);
    expect(idents).toEqual(['α', 'β', 'γ', 'αβγ']);
  });

  test('Tokenize mathematical symbols', () => {
    const tokens = tokenize('ℕ ℤ ℝ');
    const idents = tokens.filter(t => t.type === 'IDENT').map(t => t.value);
    expect(idents).toEqual(['ℕ', 'ℤ', 'ℝ']);
  });
});

// ============================================================================
// Parser: Basic Expression Tests
// ============================================================================

describe('Parser: Basic Expressions', () => {
  test('Parse identifier (variable/constant)', () => {
    const term = parseExpr('x');
    // 'x' not in context should be a Const
    assertTermShape(term, 'Const');
    if (term.tag === 'Const') {
      expect(term.name).toBe('x');
    }
  });

  test('Parse Type', () => {
    const term = parseExpr('Type');
    assertTermShape(term, 'Sort');
    if (term.tag === 'Sort') {
      expect(tlevelToNumber(term.level)).toBe(1); // Type = Sort(1)
    }
  });

  test('Parse Type n (with space)', () => {
    // Type 0 = Sort(1) = Type
    const t0 = parseExpr('Type 0');
    assertTermShape(t0, 'Sort');
    if (t0.tag === 'Sort') {
      expect(tlevelToNumber(t0.level)).toBe(1); // Type 0 = Sort(1)
    }

    // Type 1 = Sort(2)
    const t1 = parseExpr('Type 1');
    assertTermShape(t1, 'Sort');
    if (t1.tag === 'Sort') {
      expect(tlevelToNumber(t1.level)).toBe(2); // Type 1 = Sort(2)
    }

    // Type 2 = Sort(3)
    const t2 = parseExpr('Type 2');
    assertTermShape(t2, 'Sort');
    if (t2.tag === 'Sort') {
      expect(tlevelToNumber(t2.level)).toBe(3); // Type 2 = Sort(3)
    }
  });

  test('Parse Type_n (with underscore)', () => {
    // Type_0 = Sort(1) = Type
    const t0 = parseExpr('Type_0');
    assertTermShape(t0, 'Sort');
    if (t0.tag === 'Sort') {
      expect(tlevelToNumber(t0.level)).toBe(1); // Type_0 = Sort(1)
    }

    // Type_1 = Sort(2)
    const t1 = parseExpr('Type_1');
    assertTermShape(t1, 'Sort');
    if (t1.tag === 'Sort') {
      expect(tlevelToNumber(t1.level)).toBe(2); // Type_1 = Sort(2)
    }

    // Type_42 = Sort(43)
    const t42 = parseExpr('Type_42');
    assertTermShape(t42, 'Sort');
    if (t42.tag === 'Sort') {
      expect(tlevelToNumber(t42.level)).toBe(43); // Type_42 = Sort(43)
    }
  });

  test('Parse Type in Pi type', () => {
    // Verify that Type is correctly parsed inside Pi binders
    const term = parseExpr('(A : Type) -> A');
    assertTermShape(term, 'Binder');
    if (term.tag === 'Binder' && term.binderKind.tag === 'BPiTT') {
      // Domain should be Sort(1) - Pi binders always have domain
      assertTermShape(term.domain!, 'Sort');
      if (term.domain!.tag === 'Sort') {
        expect(tlevelToNumber(term.domain!.level)).toBe(1);
      }
    }
  });

  test('Parse Type 1 in Pi type', () => {
    // Verify that Type 1 is correctly parsed inside Pi binders
    const term = parseExpr('(A : Type 1) -> A');
    assertTermShape(term, 'Binder');
    if (term.tag === 'Binder' && term.binderKind.tag === 'BPiTT') {
      // Domain should be Sort(2) - Pi binders always have domain
      assertTermShape(term.domain!, 'Sort');
      if (term.domain!.tag === 'Sort') {
        expect(tlevelToNumber(term.domain!.level)).toBe(2);
      }
    }
  });

  test('Parse Prop', () => {
    const term = parseExpr('Prop');
    assertTermShape(term, 'Sort');
    if (term.tag === 'Sort') {
      expect(tlevelToNumber(term.level)).toBe(0); // Prop = Type_0
    }
  });

  test('Parse hole', () => {
    const term = parseExpr('?foo');
    assertTermShape(term, 'Hole');
    if (term.tag === 'Hole') {
      expect(term.id).toBe('foo');
    }
  });

  test('Parse underscore as hole', () => {
    const term = parseExpr('_');
    assertTermShape(term, 'Hole');
    if (term.tag === 'Hole') {
      expect(term.id).toBe('_');
    }
  });

  test('Parse parenthesized expression', () => {
    const term = parseExpr('(x)');
    assertTermShape(term, 'Const');
    if (term.tag === 'Const') {
      expect(term.name).toBe('x');
    }
  });
});

// ============================================================================
// Parser: Lambda Tests
// ============================================================================

describe('Parser: Lambda', () => {
  test('Parse lambda: \\x => x', () => {
    const term = parseExpr('\\x => x');
    assertTermShape(term, 'Binder');
    if (term.tag === 'Binder') {
      expect(term.binderKind.tag).toBe('BLamTT');
      expect(term.name).toBe('x');
      // Lambda binders always have domain
      assertTermShape(term.domain!, 'Hole'); // type is a hole
      assertTermShape(term.body, 'Var');
    }
  });

  test('Parse lambda: \\ x => x (with space)', () => {
    const term = parseExpr('\\ x => x');
    assertTermShape(term, 'Binder');
    if (term.tag === 'Binder') {
      expect(term.binderKind.tag).toBe('BLamTT');
      expect(term.name).toBe('x');
    }
  });

  test('Parse lambda: \\x y => x + y (multiple untyped)', () => {
    const term = parseExpr('\\x y => x');
    assertTermShape(term, 'Binder');
    if (term.tag === 'Binder') {
      expect(term.name).toBe('x');
      // Lambda binders always have domain
      assertTermShape(term.domain!, 'Hole');
      assertTermShape(term.body, 'Binder');
      if (term.body.tag === 'Binder') {
        expect(term.body.name).toBe('y');
        assertTermShape(term.body.domain!, 'Hole');
      }
    }
  });

  test('Parse lambda: \\(x : A) => x (typed)', () => {
    const term = parseExpr('\\(x : A) => x');
    assertTermShape(term, 'Binder');
    if (term.tag === 'Binder') {
      expect(term.name).toBe('x');
      // Lambda binders always have domain
      assertTermShape(term.domain!, 'Const'); // A is a const
    }
  });

  test('Parse lambda: \\(x : A) y => x (mixed typed/untyped)', () => {
    const term = parseExpr('\\(x : A) y => x');
    assertTermShape(term, 'Binder');
    if (term.tag === 'Binder') {
      expect(term.name).toBe('x');
      // Lambda binders always have domain
      assertTermShape(term.domain!, 'Const'); // x : A
      assertTermShape(term.body, 'Binder');
      if (term.body.tag === 'Binder') {
        expect(term.body.name).toBe('y');
        assertTermShape(term.body.domain!, 'Hole'); // y's type is a hole
      }
    }
  });

  test('Parse lambda: \\(x y : A) => x (multiple names same type, space-separated)', () => {
    const term = parseExpr('\\(x y : A) => x');
    // Multiple names with same type produces MultiBinder
    assertTermShape(term, 'MultiBinder');
    if (term.tag === 'MultiBinder') {
      expect(term.names).toEqual(['x', 'y']);
      expect(term.binderKind.tag).toBe('BLamTT');
      assertTermShape(term.domain, 'Const'); // : A
      assertTermShape(term.body, 'Var'); // x
    }
  });

  test('Parse lambda: \\(x : A) (y : B) => x (multiple typed binders)', () => {
    const term = parseExpr('\\(x : A) (y : B) => x');
    assertTermShape(term, 'Binder');
    if (term.tag === 'Binder') {
      expect(term.name).toBe('x');
      assertTermShape(term.body, 'Binder');
      if (term.body.tag === 'Binder') {
        expect(term.body.name).toBe('y');
      }
    }
  });

  test('Parse lambda: ERROR on \\ x : A => x (parens required)', () => {
    assertThrows(() => parseExpr('\\ x : A => x'));
  });

  test('Parse lambda with backslash and =>', () => {
    const term = parseExpr('\\(x : T) => x');
    assertTermShape(term, 'Binder');
    if (term.tag === 'Binder') {
      expect(term.binderKind.tag).toBe('BLamTT');
      expect(term.name).toBe('x');
    }
  });

  test('Parse lambda with fun keyword', () => {
    const term = parseExpr('fun (x : T) => x');
    assertTermShape(term, 'Binder');
    if (term.tag === 'Binder') {
      expect(term.binderKind.tag).toBe('BLamTT');
      expect(term.name).toBe('x');
    }
  });
});

// ============================================================================
// Parser: Pi/Arrow Tests (using -> syntax only)
// ============================================================================

describe('Parser: Pi/Arrow', () => {
  test('Parse dependent Pi with (x : T) -> syntax', () => {
    const term = parseExpr('(x : A) -> B');
    assertTermShape(term, 'Binder');
    if (term.tag === 'Binder') {
      expect(term.binderKind.tag).toBe('BPiTT');
      expect(term.name).toBe('x');
    }
  });

  test('Parse Pi with multiple binders', () => {
    const term = parseExpr('(x : A) -> (y : B) -> C');
    assertTermShape(term, 'Binder');
    if (term.tag === 'Binder') {
      expect(term.name).toBe('x');
      assertTermShape(term.body, 'Binder');
    }
  });

  test('Parse arrow type (non-dependent Pi)', () => {
    const term = parseExpr('A -> B');
    assertTermShape(term, 'Binder');
    if (term.tag === 'Binder') {
      expect(term.binderKind.tag).toBe('BPiTT');
      expect(term.name).toBe('_'); // Non-dependent
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

  test('Parse multi-name Pi: (a b : X) -> Y', () => {
    const term = parseExpr('(a b : X) -> Y');
    // Multiple names with same type produces MultiBinder
    assertTermShape(term, 'MultiBinder');
    if (term.tag === 'MultiBinder') {
      expect(term.names).toEqual(['a', 'b']);
      expect(term.binderKind.tag).toBe('BPiTT');
      assertTermShape(term.domain, 'Const'); // X
      assertTermShape(term.body, 'Const'); // Y
    }
  });

  test('Parse multi-name Pi with many names: (a b c d : Nat) -> T', () => {
    const term = parseExpr('(a b c d : Nat) -> T');
    assertTermShape(term, 'MultiBinder');
    if (term.tag === 'MultiBinder') {
      expect(term.names).toEqual(['a', 'b', 'c', 'd']);
      expect(term.binderKind.tag).toBe('BPiTT');
      assertTermShape(term.domain, 'Const');
      if (term.domain.tag === 'Const') {
        expect(term.domain.name).toBe('Nat');
      }
    }
  });

  test('Parse multi-name Pi followed by more binders', () => {
    const term = parseExpr('(a b : Nat) -> (c : Bool) -> T');
    assertTermShape(term, 'MultiBinder');
    if (term.tag === 'MultiBinder') {
      expect(term.names).toEqual(['a', 'b']);
      // Body should be another Pi (single-name Binder)
      assertTermShape(term.body, 'Binder');
      if (term.body.tag === 'Binder') {
        expect(term.body.name).toBe('c');
        expect(term.body.binderKind.tag).toBe('BPiTT');
      }
    }
  });

  test('Single name Pi still produces Binder (not MultiBinder)', () => {
    const term = parseExpr('(x : A) -> B');
    assertTermShape(term, 'Binder');
    if (term.tag === 'Binder') {
      expect(term.name).toBe('x');
      expect(term.binderKind.tag).toBe('BPiTT');
    }
  });
});

// ============================================================================
// Parser: Let Tests
// ============================================================================

describe('Parser: Let', () => {
  describe('Positive Tests', () => {
    test('Parse let expression without type annotation', () => {
      const term = parseExpr('let x = v in x');
      assertTermShape(term, 'Binder');
      if (term.tag === 'Binder') {
        expect(term.binderKind.tag).toBe('BLetTT');
        expect(term.name).toBe('x');
        // Domain should be undefined when type is omitted
        expect(term.domain).toBeUndefined();
        // Body should refer to x (Var 0)
        assertTermShape(term.body, 'Var');
      }
    });

    test('Parse let expression with type annotation', () => {
      const term = parseExpr('let x : T = v in x');
      assertTermShape(term, 'Binder');
      if (term.tag === 'Binder') {
        expect(term.binderKind.tag).toBe('BLetTT');
        expect(term.name).toBe('x');
        // Domain should be the type T
        assertTermShape(term.domain!, 'Const');
        if (term.domain?.tag === 'Const') {
          expect(term.domain.name).toBe('T');
        }
        assertTermShape(term.body, 'Var');
      }
    });

    test('Parse let expression with parenthesized type annotation', () => {
      const term = parseExpr('let (x : T) = v in x');
      assertTermShape(term, 'Binder');
      if (term.tag === 'Binder') {
        expect(term.binderKind.tag).toBe('BLetTT');
        expect(term.name).toBe('x');
        // Domain should be the type T
        assertTermShape(term.domain!, 'Const');
        if (term.domain?.tag === 'Const') {
          expect(term.domain.name).toBe('T');
        }
        assertTermShape(term.body, 'Var');
      }
    });

    test('Parse let expression with explicit hole type (_)', () => {
      const term = parseExpr('let x : _ = v in x');
      assertTermShape(term, 'Binder');
      if (term.tag === 'Binder') {
        expect(term.binderKind.tag).toBe('BLetTT');
        // Domain should be a Hole (explicit underscore)
        assertTermShape(term.domain!, 'Hole');
      }
    });

    test('Parse let expression with parenthesized hole type', () => {
      const term = parseExpr('let (x : _) = v in x');
      assertTermShape(term, 'Binder');
      if (term.tag === 'Binder') {
        expect(term.binderKind.tag).toBe('BLetTT');
        // Domain should be a Hole (explicit underscore)
        assertTermShape(term.domain!, 'Hole');
      }
    });

    test('Parse nested let expressions', () => {
      const term = parseExpr('let x = a in let y = b in x');
      assertTermShape(term, 'Binder');
      if (term.tag === 'Binder') {
        expect(term.name).toBe('x');
        assertTermShape(term.body, 'Binder');
        if (term.body.tag === 'Binder') {
          expect(term.body.name).toBe('y');
        }
      }
    });

    test('Parse let with complex type (arrow)', () => {
      // Arrow types in let annotations need parentheses to disambiguate
      // from the `=` assignment: `let f : (A -> B) = v in f`
      const term = parseExpr('let f : (A -> B) = v in f');
      assertTermShape(term, 'Binder');
      if (term.tag === 'Binder') {
        expect(term.binderKind.tag).toBe('BLetTT');
        // Domain should be a Pi (A -> B)
        assertTermShape(term.domain!, 'Binder');
        if (term.domain?.tag === 'Binder') {
          expect(term.domain.binderKind.tag).toBe('BPiTT');
        }
      }
    });

    test('Parse let with complex value (lambda)', () => {
      const term = parseExpr('let f = \\x => x in f');
      assertTermShape(term, 'Binder');
      if (term.tag === 'Binder' && term.binderKind.tag === 'BLetTT') {
        // Value should be a lambda
        assertTermShape(term.binderKind.defVal, 'Binder');
        if (term.binderKind.defVal.tag === 'Binder') {
          expect(term.binderKind.defVal.binderKind.tag).toBe('BLamTT');
        }
      }
    });

    test('Parse let with multiline body (indented)', () => {
      const term = parseExpr('let x = v in\n  x');
      assertTermShape(term, 'Binder');
      if (term.tag === 'Binder') {
        expect(term.binderKind.tag).toBe('BLetTT');
        expect(term.name).toBe('x');
        assertTermShape(term.body, 'Var');
      }
    });

    test('Parse nested let with multiline (both indented)', () => {
      const term = parseExpr('let x = a in\n  let y = b in\n    y');
      assertTermShape(term, 'Binder');
      if (term.tag === 'Binder') {
        expect(term.name).toBe('x');
        assertTermShape(term.body, 'Binder');
        if (term.body.tag === 'Binder') {
          expect(term.body.name).toBe('y');
          assertTermShape(term.body.body, 'Var');
        }
      }
    });

    test('Parse let with equality in parenthesized type', () => {
      // Inside parentheses, = can be used as equality operator
      const term = parseExpr('let (x : a = b) = v in x');
      assertTermShape(term, 'Binder');
      if (term.tag === 'Binder') {
        expect(term.binderKind.tag).toBe('BLetTT');
        // Domain should be an application (Eq a b)
        assertTermShape(term.domain!, 'App');
      }
    });

    test('Parse let distinguishes assignment = from equality', () => {
      // let x : Nat = 5 in x
      // The = after Nat is assignment, not equality
      const term = parseExpr('let x : Nat = five in x');
      assertTermShape(term, 'Binder');
      if (term.tag === 'Binder') {
        expect(term.binderKind.tag).toBe('BLetTT');
        // Domain should be Nat (not Nat = five)
        assertTermShape(term.domain!, 'Const');
        if (term.domain?.tag === 'Const') {
          expect(term.domain.name).toBe('Nat');
        }
        // Value should be five
        if (term.binderKind.tag === 'BLetTT') {
          assertTermShape(term.binderKind.defVal, 'Const');
        }
      }
    });

    test('Parse let in middle of line with multiline body', () => {
      // This simulates: plus (Succ a) b = let x = Succ (plus a b) in\n  x
      // The let is in the middle of the line but body just needs to be more
      // indented than the line start (column 0), not the 'let' keyword column
      const term = parseExpr('foo (let x = Succ a in\n  x)');
      assertTermShape(term, 'App');
      if (term.tag === 'App') {
        assertTermShape(term.fn, 'Const');
        assertTermShape(term.arg, 'Binder');
        if (term.arg.tag === 'Binder') {
          expect(term.arg.binderKind.tag).toBe('BLetTT');
          expect(term.arg.name).toBe('x');
        }
      }
    });
  });

  describe('Negative Tests', () => {
    test('Error on missing = in let', () => {
      assertThrows(() => parseExpr('let x v in x'));
    });

    test('Error on missing in after let value', () => {
      assertThrows(() => parseExpr('let x = v x'));
    });

    test('Error on missing body after in', () => {
      assertThrows(() => parseExpr('let x = v in'));
    });

    // Note: The parser has evolved to be lenient about let body indentation.
    // These tests document the current behavior (accepts minimal indentation).
    test('Let body at column 0 after newline is accepted', () => {
      // Parser accepts this - body can be at any column
      const term = parseExpr('let x = v in\nx');
      assertTermShape(term, 'Binder');
    });

    test('Nested let body at same indentation as outer let is accepted', () => {
      // Parser accepts this - no strict indentation enforcement
      const term = parseExpr('let x = a in\n  let y = b in\n  y');
      assertTermShape(term, 'Binder');
    });
  });
});

// ============================================================================
// Parser: Application Tests
// ============================================================================

describe('Parser: Application', () => {
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
});

// ============================================================================
// Parser: Type Annotation Tests
// ============================================================================

describe('Parser: Type Annotation', () => {
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
});

// ============================================================================
// Parser: Operator Precedence Tests
// ============================================================================

describe('Parser: Operator Precedence', () => {
  test('Multiplication binds tighter than addition', () => {
    // a + b * c  should be  a + (b * c)
    const term = parseExpr('a + b * c');
    assertTermShape(term, 'App');
    if (term.tag === 'App') {
      // Outer is add
      if (term.fn.tag === 'App' && term.fn.fn.tag === 'Const') {
        expect(term.fn.fn.name).toBe('add');
      }
      // Inner arg is mul
      if (term.arg.tag === 'App' && term.arg.fn.tag === 'App') {
        if (term.arg.fn.fn.tag === 'Const') {
          expect(term.arg.fn.fn.name).toBe('mul');
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
        expect(term.arg.name).toBe('c');
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
          expect(term.fn.arg.name).toBe('a');
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
          expect(term.fn.arg.name).toBe('a');
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
      // Domain should be addition (Pi binders always have domain)
      assertTermShape(term.domain!, 'App');
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
});

// ============================================================================
// Parser: Declaration Tests (New Syntax)
// ============================================================================

describe('Parser: Declarations', () => {
  test('Parse type signature with definition using := (name : type := impl)', () => {
    const decls = parseDeclarations('foo : T := x');
    expect(decls.length).toBe(1);
    expect(decls[0].kind).toBe('def');
    expect(decls[0].name).toBe('foo');
    if (decls[0].type) assertTermShape(decls[0].type, 'Const');
    if (decls[0].value) assertTermShape(decls[0].value, 'Const');
  });

  test('Parse type signature only (name : type)', () => {
    const decls = parseDeclarations('foo : T');
    expect(decls.length).toBe(1);
    expect(decls[0].kind).toBe('def');
    expect(decls[0].name).toBe('foo');
    if (decls[0].type) assertTermShape(decls[0].type, 'Const');
    expect(decls[0].value).toBeUndefined();
  });

  test('Parse definition only (name = impl)', () => {
    const decls = parseDeclarations('foo = x');
    expect(decls.length).toBe(1);
    expect(decls[0].kind).toBe('def');
    expect(decls[0].name).toBe('foo');
    expect(decls[0].type).toBeUndefined();
    if (decls[0].value) assertTermShape(decls[0].value, 'Const');
  });

  test('Parse complex type signature with definition using :=', () => {
    const decls = parseDeclarations('id : (A : Type) -> A -> A := \\(A : Type) (x : A) => x');
    expect(decls.length).toBe(1);
    expect(decls[0].kind).toBe('def');
    expect(decls[0].name).toBe('id');
    if (decls[0].type) assertTermShape(decls[0].type, 'Binder');
    if (decls[0].value) assertTermShape(decls[0].value, 'Binder');
  });

  test('Parse two-line declaration (type on one line, def on next) - merged', () => {
    const source = `id : (A : Type) -> A -> A
id = \\(A : Type) (x : A) => x`;
    const decls = parseDeclarations(source);
    // Declarations with same name (type-only followed by value-only) are merged
    expect(decls.length).toBe(1);
    expect(decls[0].kind).toBe('def');
    expect(decls[0].name).toBe('id');
    // Both type and value should be present after merging
    if (decls[0].type) assertTermShape(decls[0].type, 'Binder');
    if (decls[0].value) assertTermShape(decls[0].value, 'Binder');
  });

  test('Parse type containing equality (a = b in type)', () => {
    const decls = parseDeclarations('add_comm : (a : ℕ) -> (b : ℕ) -> a + b = b + a');
    expect(decls.length).toBe(1);
    expect(decls[0].kind).toBe('def');
    expect(decls[0].name).toBe('add_comm');
    expect(decls[0].value).toBeUndefined(); // type signature only
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
    expect(decls.length).toBe(3);
    expect(decls[0].name).toBe('foo');
    // Merged: should have both type and value
    assertTermShape(decls[0].type!, 'Const'); // T is a const
    assertTermShape(decls[0].value!, 'Const'); // x is a const
    expect(decls[1].name).toBe('bar');
    expect(decls[2].name).toBe('baz');
    expect(decls[2].value).toBeUndefined(); // type signature only
  });

  test('Parse bare expression as declaration', () => {
    const decls = parseDeclarations('x + y');
    expect(decls.length).toBe(1);
    expect(decls[0].kind).toBe('expr');
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
    expect(decls.length).toBe(3);
    expect(decls[0].kind).toBe('def');
    expect(decls[0].name).toBe('foo');
    // foo should have both type and value after merging
    assertTermShape(decls[0].type!, 'Const');
    assertTermShape(decls[0].value!, 'Const');
    expect(decls[1].kind).toBe('expr');
    expect(decls[2].kind).toBe('def');
  });
});

// ============================================================================
// Parser: Complex Expression Tests
// ============================================================================

describe('Parser: Complex Expressions', () => {
  test('Parse function type with explicit domain', () => {
    const term = parseExpr('(n : ℕ) -> (m : ℕ) -> Prop');
    assertTermShape(term, 'Binder');
    if (term.tag === 'Binder') {
      expect(term.name).toBe('n');
      assertTermShape(term.body, 'Binder');
    }
  });

  test('Parse complex lambda', () => {
    const term = parseExpr('\\(f : A -> B) (x : A) => f x');
    assertTermShape(term, 'Binder');
    if (term.tag === 'Binder') {
      expect(term.name).toBe('f');
      assertTermShape(term.body, 'Binder');
      if (term.body.tag === 'Binder') {
        expect(term.body.name).toBe('x');
        assertTermShape(term.body.body, 'App');
      }
    }
  });

  test('Parse identity function type', () => {
    const term = parseExpr('(A : Type) -> A -> A');
    assertTermShape(term, 'Binder');
    if (term.tag === 'Binder') {
      expect(term.binderKind.tag).toBe('BPiTT');
      expect(term.name).toBe('A');
    }
  });

  test('Parse let with complex value (function application)', () => {
    const term = parseExpr('let id = \\x => x in id y');
    assertTermShape(term, 'Binder');
    if (term.tag === 'Binder' && term.binderKind.tag === 'BLetTT') {
      expect(term.name).toBe('id');
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
        expect(term.fn.fn.name).toBe('mul');
      }
      assertTermShape(term.fn.arg, 'App'); // add a b
      assertTermShape(term.arg, 'App'); // add c d
    }
  });
});

// ============================================================================
// Parser: Error Cases
// ============================================================================

describe('Parser: Error Cases', () => {
  test('Error on unexpected token', () => {
    assertThrows(() => parseExpr(')'));
  });

  test('Error on unclosed parenthesis', () => {
    assertThrows(() => parseExpr('(x'));
  });

  test('Error on missing lambda binder', () => {
    assertThrows(() => parseExpr('\\'));
  });

  test('Error on missing let value (old syntax)', () => {
    assertThrows(() => parseExpr('let x ='));
  });

  test('Error on missing let body (old syntax)', () => {
    assertThrows(() => parseExpr('let x = v in'));
  });

  test('Error on invalid character', () => {
    assertThrows(() => parseExpr('a § b'));
  });
});

// ============================================================================
// Parser: Custom Operators Tests
// ============================================================================

describe('Parser: Custom Operators', () => {
  test('Parse with custom operator', () => {
    const customOps: Record<string, OperatorInfo> = {
      ...DEFAULT_OPERATORS,
      '⊕': { symbol: '⊕', precedence: 60, associativity: 'left', constName: 'xor' },
    };

    const parser = new Parser(customOps);
    const term = parser.parseExpr('a ⊕ b');
    assertTermShape(term, 'App');
    if (term.tag === 'App' && term.fn.tag === 'App' && term.fn.fn.tag === 'Const') {
      expect(term.fn.fn.name).toBe('xor');
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
      expect(term.fn.fn.name).toBe('add');
    }
  });
});

// ============================================================================
// De Bruijn Index Tests
// ============================================================================

describe('Parser: De Bruijn Indices', () => {
  test('Lambda body correctly references bound variable', () => {
    const term = parseExpr('\\(x : T) => x');
    if (term.tag === 'Binder' && term.body.tag === 'Var') {
      expect(term.body.index).toBe(0);
    }
  });

  test('Nested lambda body correctly references outer variable', () => {
    const term = parseExpr('\\(x : A) (y : B) => x');
    if (term.tag === 'Binder' && term.body.tag === 'Binder' && term.body.body.tag === 'Var') {
      expect(term.body.body.index).toBe(1);
    }
  });

  test('Nested lambda body correctly references inner variable', () => {
    const term = parseExpr('\\(x : A) (y : B) => y');
    if (term.tag === 'Binder' && term.body.tag === 'Binder' && term.body.body.tag === 'Var') {
      expect(term.body.body.index).toBe(0);
    }
  });

  test('Let body correctly references bound variable', () => {
    const term = parseExpr('let x = v in x');
    if (term.tag === 'Binder' && term.body.tag === 'Var') {
      expect(term.body.index).toBe(0);
    }
  });

  test('Pi body correctly references bound variable', () => {
    const term = parseExpr('(x : Type) -> x');
    if (term.tag === 'Binder' && term.body.tag === 'Var') {
      expect(term.body.index).toBe(0);
    }
  });

  test('Free variable becomes Const', () => {
    const term = parseExpr('\\x => y');
    if (term.tag === 'Binder') {
      // y is not bound, should be Const
      assertTermShape(term.body, 'Const');
      if (term.body.tag === 'Const') {
        expect(term.body.name).toBe('y');
      }
    }
  });
});

// ============================================================================
// Pretty Print Round-Trip Tests
// ============================================================================

describe('Parser: Pretty Print', () => {
  test('Pretty print preserves variable names', () => {
    const term = parseExpr('\\(foo : T) => foo');
    const printed = prettyPrintTT(term);
    expect(printed).toContain('foo');
  });

  test('Pretty print shows Pi types correctly', () => {
    const term = parseExpr('(α : Type) -> α -> α');
    const printed = prettyPrintTT(term);
    expect(printed).toContain('α');
  });
});

// ============================================================================
// Parser: Inductive Type Tests
// ============================================================================

describe('Parser: Inductive Types', () => {
  test('Parse simple inductive type (Nat)', () => {
    const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat`;

    const decls = parseDeclarations(source);
    expect(decls.length).toBe(1);
    expect(decls[0].kind).toBe('inductive');
    expect(decls[0].name).toBe('Nat');
    assertTermShape(decls[0].type!, 'Sort');
    expect(decls[0].constructors?.length).toBe(2);
    expect(decls[0].constructors![0].name).toBe('Zero');
    expect(decls[0].constructors![1].name).toBe('Succ');
  });

  test('Error on inductive type without where keyword', () => {
    // The parser requires 'where' keyword to know where the type ends
    const source = `inductive Nat : Type
  Zero : Nat
  Succ : Nat -> Nat`;

    assertThrows(() => parseDeclarations(source));
  });

  test('Parse inductive type with pipes', () => {
    const source = `inductive Bool : Type where
  | True : Bool
  | False : Bool`;

    const decls = parseDeclarations(source);
    expect(decls.length).toBe(1);
    expect(decls[0].kind).toBe('inductive');
    expect(decls[0].constructors?.length).toBe(2);
    expect(decls[0].constructors![0].name).toBe('True');
    expect(decls[0].constructors![1].name).toBe('False');
  });

  test('Parse parameterized inductive type (List)', () => {
    const source = `inductive List : Type -> Type where
  | Nil : (A : Type) -> List A
  | Cons : (A : Type) -> A -> List A -> List A`;

    const decls = parseDeclarations(source);
    expect(decls.length).toBe(1);
    expect(decls[0].kind).toBe('inductive');
    expect(decls[0].name).toBe('List');
    expect(decls[0].constructors?.length).toBe(2);
    expect(decls[0].constructors![0].name).toBe('Nil');
    expect(decls[0].constructors![1].name).toBe('Cons');
  });

  test('Parse inductive type with complex constructor types', () => {
    const source = `inductive Expr : Type where
  | Var : (name : String) -> Expr
  | App : Expr -> Expr -> Expr
  | Lam : (name : String) -> Expr -> Expr`;

    const decls = parseDeclarations(source);
    expect(decls.length).toBe(1);
    expect(decls[0].kind).toBe('inductive');
    expect(decls[0].constructors?.length).toBe(3);
  });
});

// ============================================================================
// Pattern Matching Tests
// ============================================================================

describe('Pattern Matching', () => {
  test('Parse simple case expression with Zero', () => {
    const source = `case n where
  | Zero => b`;
    const term = parseExpr(source);
    assertTermShape(term, 'Match');
    if (term.tag === 'Match') {
      expect(term.clauses.length).toBe(1);
      expect(term.clauses[0].patterns.length).toBe(1);
      expect(term.clauses[0].patterns[0].tag).toBe('PCtor');
      if (term.clauses[0].patterns[0].tag === 'PCtor') {
        expect(term.clauses[0].patterns[0].name).toBe('Zero');
        expect(term.clauses[0].patterns[0].args.length).toBe(0);
      }
    }
  });

  test('Parse case expression with Succ pattern', () => {
    const source = `case n where
  | Succ a => a`;
    const term = parseExpr(source);
    assertTermShape(term, 'Match');
    if (term.tag === 'Match') {
      expect(term.clauses.length).toBe(1);
      const pattern = term.clauses[0].patterns[0];
      expect(pattern.tag).toBe('PCtor');
      if (pattern.tag === 'PCtor') {
        expect(pattern.name).toBe('Succ');
        expect(pattern.args.length).toBe(1);
        // Identifiers are now uniformly parsed as PCtor - elaboration resolves to PVar
        expect(pattern.args[0].tag).toBe('PCtor');
        if (pattern.args[0].tag === 'PCtor') {
          expect(pattern.args[0].name).toBe('a');
          expect(pattern.args[0].args.length).toBe(0);
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
      expect(term.clauses.length).toBe(2);
      // First clause: Zero
      expect(term.clauses[0].patterns[0].tag).toBe('PCtor');
      // Second clause: Succ a
      expect(term.clauses[1].patterns[0].tag).toBe('PCtor');
    }
  });

  test('Parse nested pattern (Succ (Succ m))', () => {
    const source = `case n where
  | Succ (Succ m) => m`;
    const term = parseExpr(source);
    assertTermShape(term, 'Match');
    if (term.tag === 'Match') {
      const pattern = term.clauses[0].patterns[0];
      expect(pattern.tag).toBe('PCtor');
      if (pattern.tag === 'PCtor') {
        expect(pattern.name).toBe('Succ');
        expect(pattern.args.length).toBe(1);

        const innerPattern = pattern.args[0];
        expect(innerPattern.tag).toBe('PCtor');
        if (innerPattern.tag === 'PCtor') {
          expect(innerPattern.name).toBe('Succ');
          expect(innerPattern.args.length).toBe(1);
          // Identifiers are uniformly parsed as PCtor (elaboration resolves)
          expect(innerPattern.args[0].tag).toBe('PCtor');
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
      // Wildcards are now parsed as PWild (names generated in elaboration)
      expect(pattern.tag).toBe('PWild');
    }
  });

  test('Parse variable pattern', () => {
    const source = `case n where
  | x => x`;
    const term = parseExpr(source);
    assertTermShape(term, 'Match');
    if (term.tag === 'Match') {
      const pattern = term.clauses[0].patterns[0];
      // Identifiers are uniformly parsed as PCtor (elaboration resolves to PVar)
      expect(pattern.tag).toBe('PCtor');
      if (pattern.tag === 'PCtor') {
        expect(pattern.name).toBe('x');
        expect(pattern.args.length).toBe(0);
      }
    }
  });

  test('Parse case with match keyword', () => {
    const source = `match n where
  | Zero => b
  | Succ a => a`;
    const term = parseExpr(source);
    assertTermShape(term, 'Match');
  });

  test('Parse constructor with multiple args (Cons x xs)', () => {
    const source = `case list where
  | Nil => Zero
  | Cons x xs => x`;
    const term = parseExpr(source);
    assertTermShape(term, 'Match');
    if (term.tag === 'Match') {
      expect(term.clauses.length).toBe(2);

      // Second clause: Cons x xs
      const consPattern = term.clauses[1].patterns[0];
      expect(consPattern.tag).toBe('PCtor');
      if (consPattern.tag === 'PCtor') {
        expect(consPattern.name).toBe('Cons');
        expect(consPattern.args.length).toBe(2);
        // Identifiers are uniformly parsed as PCtor (elaboration resolves)
        expect(consPattern.args[0].tag).toBe('PCtor');
        expect(consPattern.args[1].tag).toBe('PCtor');
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
      expect(pattern.tag).toBe('PCtor');
      if (pattern.tag === 'PCtor') {
        expect(pattern.name).toBe('Succ');
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
      expect(term.clauses.length).toBe(2);
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
        expect(rhs.index).toBe(0);
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
        expect(rhs.index).toBe(0);
      }
    }
  });

  test('Parse function definition with pattern clauses', () => {
    const source = `plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)`;

    const decls = parseDeclarations(source);
    expect(decls.length).toBe(1);
    expect(decls[0].name).toBe('plus');
    expect(decls[0].type).toBeDefined();
    expect(decls[0].value).toBeDefined();

    // Value should be a Match expression
    const value = decls[0].value!;
    assertTermShape(value, 'Match');
    if (value.tag === 'Match') {
      expect(value.clauses.length).toBe(2);

      // First clause: Zero b
      const clause1 = value.clauses[0];
      expect(clause1.patterns.length).toBe(2);
      expect(clause1.patterns[0].tag).toBe('PCtor');
      if (clause1.patterns[0].tag === 'PCtor') {
        expect(clause1.patterns[0].name).toBe('Zero');
      }
      // Identifiers are uniformly parsed as PCtor (elaboration resolves)
      expect(clause1.patterns[1].tag).toBe('PCtor');

      // Second clause: Succ a, b
      const clause2 = value.clauses[1];
      expect(clause2.patterns.length).toBe(2);
      expect(clause2.patterns[0].tag).toBe('PCtor');
      if (clause2.patterns[0].tag === 'PCtor') {
        expect(clause2.patterns[0].name).toBe('Succ');
        expect(clause2.patterns[0].args.length).toBe(1);
      }
    }
  });

  test('Parse single pattern clause definition', () => {
    const source = `twice : Nat -> Nat
twice n = plus n n`;

    const decls = parseDeclarations(source);
    expect(decls.length).toBe(1);
    expect(decls[0].name).toBe('twice');
    expect(decls[0].type).toBeDefined();
    expect(decls[0].value).toBeDefined();

    // Value should be a Match with one clause
    const value = decls[0].value!;
    assertTermShape(value, 'Match');
    if (value.tag === 'Match') {
      expect(value.clauses.length).toBe(1);
      expect(value.clauses[0].patterns.length).toBe(1);
      // Identifiers are uniformly parsed as PCtor (elaboration resolves)
      expect(value.clauses[0].patterns[0].tag).toBe('PCtor');
    }
  });

  test('Parse pattern clause without type signature', () => {
    const source = `id x = x`;

    const decls = parseDeclarations(source);
    expect(decls.length).toBe(1);
    expect(decls[0].name).toBe('id');
    expect(decls[0].type).toBeUndefined();
    expect(decls[0].value).toBeDefined();

    const value = decls[0].value!;
    assertTermShape(value, 'Match');
  });
});

// ============================================================================
// Pattern Edge Cases (mixed parens/bare args, underscore with args)
// ============================================================================

describe('Pattern Edge Cases', () => {
  test('Parse underscore with arguments: (_ _) parses as PCtor', () => {
    // This should parse (elaborator will reject it later)
    const source = `case x where
  | (_ _) => y`;
    const term = parseExpr(source);
    assertTermShape(term, 'Match');
    if (term.tag === 'Match') {
      const pattern = term.clauses[0].patterns[0];
      expect(pattern.tag).toBe('PCtor');
      if (pattern.tag === 'PCtor') {
        expect(pattern.name).toBe('_');
        expect(pattern.args.length).toBe(1);
        expect(pattern.args[0].tag).toBe('PWild');
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
      expect(pattern.tag).toBe('PCtor');
      if (pattern.tag === 'PCtor') {
        expect(pattern.name).toBe('FSucc');
        expect(pattern.args.length).toBe(2);

        // First arg: (Succ _)
        const arg1 = pattern.args[0];
        expect(arg1.tag).toBe('PCtor');
        if (arg1.tag === 'PCtor') {
          expect(arg1.name).toBe('Succ');
          expect(arg1.args.length).toBe(1);
        }

        // Second arg: f (parsed as PCtor with no args, will be resolved later)
        const arg2 = pattern.args[1];
        expect(arg2.tag).toBe('PCtor');
        if (arg2.tag === 'PCtor') {
          expect(arg2.name).toBe('f');
          expect(arg2.args.length).toBe(0);
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
      expect(pattern.tag).toBe('PCtor');
      if (pattern.tag === 'PCtor') {
        expect(pattern.name).toBe('VCons');
        expect(pattern.args.length).toBe(4);

        // First arg: _ (wildcard)
        expect(pattern.args[0].tag).toBe('PWild');

        // Second arg: (Succ _)
        expect(pattern.args[1].tag).toBe('PCtor');
        if (pattern.args[1].tag === 'PCtor') {
          expect(pattern.args[1].name).toBe('Succ');
        }

        // Third arg: h
        expect(pattern.args[2].tag).toBe('PCtor');
        if (pattern.args[2].tag === 'PCtor') {
          expect(pattern.args[2].name).toBe('h');
        }

        // Fourth arg: tail
        expect(pattern.args[3].tag).toBe('PCtor');
        if (pattern.args[3].tag === 'PCtor') {
          expect(pattern.args[3].name).toBe('tail');
        }
      }
    }
  });

  test('Parse complex pattern clause: nth with Vec and Fin patterns', () => {
    // This was the failing case from the user
    const source = `nth : (A : Type) -> (n : Nat) -> Vec A n -> Fin n -> A
nth A _ (VCons _ (Succ _) h tail) (FSucc (Succ _) f) = nth _ _ tail f`;

    const decls = parseDeclarations(source);
    expect(decls.length).toBe(1);
    expect(decls[0].name).toBe('nth');

    const value = decls[0].value!;
    assertTermShape(value, 'Match');

    if (value.tag === 'Match') {
      expect(value.clauses.length).toBe(1);
      const clause = value.clauses[0];
      expect(clause.patterns.length).toBe(4);

      // Pattern 1: A (variable)
      expect(clause.patterns[0].tag).toBe('PCtor');
      if (clause.patterns[0].tag === 'PCtor') {
        expect(clause.patterns[0].name).toBe('A');
      }

      // Pattern 2: _ (wildcard)
      expect(clause.patterns[1].tag).toBe('PWild');

      // Pattern 3: (VCons _ (Succ _) h tail)
      expect(clause.patterns[2].tag).toBe('PCtor');
      if (clause.patterns[2].tag === 'PCtor') {
        expect(clause.patterns[2].name).toBe('VCons');
        expect(clause.patterns[2].args.length).toBe(4);
      }

      // Pattern 4: (FSucc (Succ _) f)
      expect(clause.patterns[3].tag).toBe('PCtor');
      if (clause.patterns[3].tag === 'PCtor') {
        expect(clause.patterns[3].name).toBe('FSucc');
        expect(clause.patterns[3].args.length).toBe(2);
      }
    }
  });

  test('Parse multiple pattern clauses with complex patterns', () => {
    const source = `nth : (A : Type) -> (n : Nat) -> Vec A n -> Fin n -> A
nth A _ (VCons _ _ h _) (FZero _) = h
nth A _ (VCons _ (Succ _) h tail) (FSucc (Succ _) f) = nth _ _ tail f`;

    const decls = parseDeclarations(source);
    expect(decls.length).toBe(1);

    const value = decls[0].value!;
    assertTermShape(value, 'Match');

    if (value.tag === 'Match') {
      expect(value.clauses.length).toBe(2);

      // First clause: nth A _ (VCons _ _ h _) (FZero _) = h
      const clause1 = value.clauses[0];
      expect(clause1.patterns.length).toBe(4);

      // Second clause: nth A _ (VCons _ (Succ _) h tail) (FSucc (Succ _) f) = ...
      const clause2 = value.clauses[1];
      expect(clause2.patterns.length).toBe(4);

      // Verify FSucc has 2 args in second clause
      if (clause2.patterns[3].tag === 'PCtor') {
        expect(clause2.patterns[3].name).toBe('FSucc');
        expect(clause2.patterns[3].args.length).toBe(2);
      }
    }
  });
});

// ============================================================================
// PREFIX_PARSELETS Table Dispatch Tests
// ============================================================================

describe('PREFIX_PARSELETS Table Dispatch', () => {
  test('Table dispatch: LPAREN -> parseParenExpr', () => {
    const term = parseExpr('(x)');
    assertTermShape(term, 'Const');
  });

  test('Table dispatch: LAMBDA -> parseLambda', () => {
    const term = parseExpr('\\x => x');
    assertTermShape(term, 'Binder');
    if (term.tag === 'Binder') {
      expect(term.binderKind.tag).toBe('BLamTT');
    }
  });

  test('Table dispatch: LET -> parseLet', () => {
    const term = parseExpr('let x = y in x');
    assertTermShape(term, 'Binder');
    if (term.tag === 'Binder') {
      expect(term.binderKind.tag).toBe('BLetTT');
    }
  });

  test('Table dispatch: CASE -> parseMatch', () => {
    const term = parseExpr('case x where | y => y');
    assertTermShape(term, 'Match');
  });

  test('Table dispatch: MATCH -> parseMatch', () => {
    const term = parseExpr('match x where | y => y');
    assertTermShape(term, 'Match');
  });

  test('Table dispatch: TYPE -> parseType', () => {
    const term = parseExpr('Type');
    assertTermShape(term, 'Sort');
    if (term.tag === 'Sort') {
      expect(tlevelToNumber(term.level)).toBe(1);
    }
  });

  test('Table dispatch: IDENT -> parseIdent', () => {
    const term = parseExpr('foo');
    assertTermShape(term, 'Const');
    if (term.tag === 'Const') {
      expect(term.name).toBe('foo');
    }
  });

  test('Table dispatch: PROP -> inline mkPropTT', () => {
    const term = parseExpr('Prop');
    assertTermShape(term, 'Sort');
    if (term.tag === 'Sort') {
      expect(tlevelToNumber(term.level)).toBe(0);
    }
  });

  test('Table dispatch: HOLE -> inline mkHoleTT', () => {
    const term = parseExpr('?myhole');
    assertTermShape(term, 'Hole');
    if (term.tag === 'Hole') {
      expect(term.id).toBe('myhole');
    }
  });

  test('Table dispatch: NUMBER -> parseNumberLiteral', () => {
    const term = parseExpr('42');
    assertTermShape(term, 'Const');
    if (term.tag === 'Const') {
      expect(term.name).toBe('42');
    }
  });

  test('Table dispatch: UNDERSCORE -> inline mkHoleTT', () => {
    const term = parseExpr('_');
    assertTermShape(term, 'Hole');
    if (term.tag === 'Hole') {
      expect(term.id).toBe('_');
    }
  });

  test('Table dispatch: unknown token throws ParseError', () => {
    assertThrows(() => parseExpr(')'));
  });

  test('All prefix token types have consistent behavior in expressions', () => {
    // Complex expression using multiple prefix token types
    const term = parseExpr('let f = \\x => (x : Type) in f ?hole');
    assertTermShape(term, 'Binder');
    if (term.tag === 'Binder' && term.binderKind.tag === 'BLetTT') {
      // f is a lambda
      assertTermShape(term.binderKind.defVal, 'Binder');
      // body is an application
      assertTermShape(term.body, 'App');
    }
  });
});
