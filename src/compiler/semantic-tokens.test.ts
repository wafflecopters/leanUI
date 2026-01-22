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
  });
});
