/**
 * Unit tests for semantic token extraction
 * Verifies that token positions are valid for the source text
 */

import { describe, test, expect } from 'vitest';
import { compileTTFromText, extractSemanticTokens, SemanticToken } from './compile';

/**
 * Validate that all semantic tokens have valid positions for the source
 */
function validateSemanticTokens(source: string, tokens: SemanticToken[]): void {
  const lines = source.split('\n');

  for (const token of tokens) {
    // Check line is within bounds (1-based)
    if (token.line < 1 || token.line > lines.length) {
      throw new Error(
        `Invalid token: line ${token.line} out of bounds (1-${lines.length})\n` +
        `Token type: ${token.type}`
      );
    }

    const lineText = lines[token.line - 1];

    // Check column is within bounds (1-based)
    if (token.column < 1 || token.column > lineText.length + 1) {
      throw new Error(
        `Invalid token: column ${token.column} out of bounds (1-${lineText.length + 1})\n` +
        `Line ${token.line}: "${lineText}"\n` +
        `Token type: ${token.type}`
      );
    }

    // Check length doesn't exceed line length
    if (token.column + token.length - 1 > lineText.length + 1) {
      throw new Error(
        `Invalid token: length ${token.length} from column ${token.column} exceeds line ${token.line}\n` +
        `Line content: "${lineText}" (length ${lineText.length})\n` +
        `Token type: ${token.type}`
      );
    }
  }
}

describe('Semantic Token Extraction', () => {
  describe('Single block', () => {
    test('simple definition', () => {
      const source = `x : Nat`;
      const result = compileTTFromText(source);
      const tokens = extractSemanticTokens(result);

      validateSemanticTokens(source, tokens);
      expect(tokens.length).toBeGreaterThan(0);
    });

    test('inductive type', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat`;
      const result = compileTTFromText(source);
      const tokens = extractSemanticTokens(result);

      validateSemanticTokens(source, tokens);
      // Should have tokens for: Nat (definition), Type, Zero, Nat (in Zero type), Succ, Nat (3x in Succ type)
      expect(tokens.length).toBeGreaterThanOrEqual(3);
    });

    test('record type', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Point where
  constructor MkPoint
  x : Nat
  y : Nat`;
      const result = compileTTFromText(source);
      const tokens = extractSemanticTokens(result);

      validateSemanticTokens(source, tokens);

      // Check for record-specific tokens
      // Constructor name (MkPoint) should be constName
      const mkPointToken = tokens.find(t => t.type === 'constName' && t.line === 6);
      expect(mkPointToken).toBeDefined();

      // Field names (x, y) should be termName
      const xFieldToken = tokens.find(t => t.type === 'termName' && t.line === 7);
      const yFieldToken = tokens.find(t => t.type === 'termName' && t.line === 8);
      expect(xFieldToken).toBeDefined();
      expect(yFieldToken).toBeDefined();
    });

    test('function with named parameter', () => {
      const source = `id : { A : Type } -> A -> A
id {A} x = x`;
      const result = compileTTFromText(source);
      const tokens = extractSemanticTokens(result);

      validateSemanticTokens(source, tokens);
    });
  });

  describe('Multiple blocks - position adjustment', () => {
    test('two definitions separated by blank line', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

x : Nat
x = Zero`;
      const result = compileTTFromText(source);
      const tokens = extractSemanticTokens(result);

      validateSemanticTokens(source, tokens);

      // Check that tokens exist on lines from both blocks
      const tokensOnLine5 = tokens.filter(t => t.line === 5);
      const tokensOnLine6 = tokens.filter(t => t.line === 6);
      expect(tokensOnLine5.length + tokensOnLine6.length).toBeGreaterThan(0);
    });

    test('three blocks with definitions', () => {
      const source = `inductive Bool : Type where
  True : Bool
  False : Bool

inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

not : Bool -> Bool
not True = False
not False = True`;
      const result = compileTTFromText(source);
      const tokens = extractSemanticTokens(result);

      validateSemanticTokens(source, tokens);

      // Tokens should span multiple line ranges
      const minLine = Math.min(...tokens.map(t => t.line));
      const maxLine = Math.max(...tokens.map(t => t.line));
      expect(minLine).toBe(1);
      expect(maxLine).toBeGreaterThanOrEqual(10);
    });

    test('named arguments in second block', () => {
      const source = `id : { A : Type } -> A -> A
id {A} x = x

useId : { T : Type } -> T -> T
useId {T} x = id { A := T } x`;
      const result = compileTTFromText(source);
      const tokens = extractSemanticTokens(result);

      validateSemanticTokens(source, tokens);

      // Should have tokens on lines 4 and 5
      const tokensOnLine4 = tokens.filter(t => t.line === 4);
      const tokensOnLine5 = tokens.filter(t => t.line === 5);
      expect(tokensOnLine4.length + tokensOnLine5.length).toBeGreaterThan(0);
    });
  });

  describe('Edge cases', () => {
    test('long type signature on single line', () => {
      const source = `compose : { A : Type } -> { B : Type } -> { C : Type } -> (B -> C) -> (A -> B) -> A -> C
compose {A} {B} {C} g f x = g (f x)`;
      const result = compileTTFromText(source);
      const tokens = extractSemanticTokens(result);

      validateSemanticTokens(source, tokens);
    });

    test('declaration with lambda', () => {
      const source = `f = \\x => x`;
      const result = compileTTFromText(source);
      const tokens = extractSemanticTokens(result);

      validateSemanticTokens(source, tokens);
    });

    test('with-clause semantic tokens', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat
inductive Bool : Type where
  True : Bool
  False : Bool

isZero : Nat -> Bool
isZero n with n
  | Zero => True
  | Succ _ => False`;
      const result = compileTTFromText(source);
      const tokens = extractSemanticTokens(result);

      validateSemanticTokens(source, tokens);

      // Should have tokens on the with-clause lines (9, 10, 11)
      const tokensOnLine9 = tokens.filter(t => t.line === 9);
      const tokensOnLine10 = tokens.filter(t => t.line === 10);
      const tokensOnLine11 = tokens.filter(t => t.line === 11);

      // Line 9 (isZero n with n): should have termName for 'isZero', patternVar for 'n'
      expect(tokensOnLine9.length).toBeGreaterThan(0);

      // Line 10 (| Zero => True): should have constName for 'Zero' and 'True'
      const line10ConstTokens = tokensOnLine10.filter(t => t.type === 'constName');
      expect(line10ConstTokens.length).toBeGreaterThanOrEqual(1); // at least Zero or True

      // Line 11 (| Succ _ => False): should have constName for 'Succ' and 'False'
      const line11ConstTokens = tokensOnLine11.filter(t => t.type === 'constName');
      expect(line11ConstTokens.length).toBeGreaterThanOrEqual(1); // at least Succ or False
    });

    test('nested with-clause semantic tokens', () => {
      const source = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat
inductive Bool : Type where
  True : Bool
  False : Bool

classify : Nat -> Nat -> Bool
classify m n with m
  | Zero with n
    | Zero => True
    | Succ _ => False
  | Succ _ => True`;
      const result = compileTTFromText(source);
      const tokens = extractSemanticTokens(result);

      validateSemanticTokens(source, tokens);

      // Lines 10-13 are in with-clauses — should have some tokens
      const withLineTokens = tokens.filter(t => t.line >= 10 && t.line <= 13);
      expect(withLineTokens.length).toBeGreaterThan(0);
    });

    test('blank lines before inductive with named binders', () => {
      // This is the user's exact scenario - blank lines at the start
      // should not cause semantic token positions to be wrong
      const source = `

inductive Vec : {A : Type} -> Nat -> Type where
  VNil : {A: Type} -> Vec A Zero
  VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)`;
      const result = compileTTFromText(source);
      const tokens = extractSemanticTokens(result);

      validateSemanticTokens(source, tokens);

      // The inductive starts on line 3, so all tokens should be on line 3 or later
      const minLine = Math.min(...tokens.map(t => t.line));
      expect(minLine).toBeGreaterThanOrEqual(3);

      // Check that we have namedBrace tokens (for the { } in {A : Type})
      const braceTokens = tokens.filter(t => t.type === 'namedBrace');
      expect(braceTokens.length).toBeGreaterThan(0);

      // All brace tokens should be on line 3 or later
      for (const token of braceTokens) {
        expect(token.line).toBeGreaterThanOrEqual(3);
      }
    });

    test('erw tactic args get semantic tokens', () => {
      const source = `inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

trans : {A : Type} -> {x y z : A} -> Equal x y -> Equal y z -> Equal x z
trans refl refl = refl

cong : {A B : Type} -> {x y : A} -> (f : A -> B) -> Equal x y -> Equal (f x) (f y)
cong f refl = refl

inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)

plusZero : (n : Nat) -> Equal (plus n Zero) n := by
  intros n
  erw (trans refl refl)`;
      const result = compileTTFromText(source);
      const tokens = extractSemanticTokens(result);

      validateSemanticTokens(source, tokens);

      // The erw tactic is on the last line — should have tokens for 'trans', 'refl' args
      const lastLine = source.split('\n').length;
      const erwLineTokens = tokens.filter(t => t.line === lastLine);

      // Should have tacticName for 'erw' plus tokens for the term args (trans, refl, refl)
      const tacticTokens = erwLineTokens.filter(t => t.type === 'tacticName');
      expect(tacticTokens.length).toBe(1);

      const termTokens = erwLineTokens.filter(t => t.type === 'termName' || t.type === 'constName');
      // trans and refl should be highlighted
      expect(termTokens.length).toBeGreaterThanOrEqual(1);
    });
  });
});
