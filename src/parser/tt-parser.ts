/**
 * TT Language Parser
 *
 * A parser for the Typed Terms language using a Pratt parser for proper
 * operator precedence and associativity handling.
 *
 * Syntax supported:
 * - Sorts: Type, Prop, Type_0, Type_1, ...
 * - Variables/Constants: identifiers (x, foo, myVar)
 * - Holes: ?name
 * - Lambda: \x => body  or  \x y => body  or  \(x : T) => body
 *           \(x, y : T) => body  for multiple binders with same type
 * - Pi/Forall: (x : T) -> body  (dependent function type)
 * - Arrow (non-dependent): A -> B
 * - Let: let x : T := val in body
 * - Application: f x y  (left-associative)
 * - Annotation: (term : type)
 * - Parentheses: (expr)
 * - Infix operators: user-defined with configurable precedence and associativity
 *
 * Declaration syntax:
 * - Type signature: name : type
 * - Definition: name = impl
 * - Combined: name : type followed by name = impl (on next line)
 * - Inductive types: inductive Name : Type where | Ctor1 : T1 | Ctor2 : T2
 * - Legacy: def/theorem/axiom keywords still supported
 */

import { TTerm, mkVar, mkPi, mkLambda, mkLet, mkApp, mkConst, mkHole, mkProp, mkType, TPattern, TClause } from '../types/tt-core';
import { groupByIndentation, parseBlock } from './indentation-grouper';
import {
  SourceMap,
  SourcePos,
  SourceRange,
  IndexPath,
  IndexPathSegment,
  createSourcePos,
  createSourceRange,
  serializeIndexPath
} from '../types/source-position';

// ============================================================================
// Token Types
// ============================================================================

export type TokenType =
  | 'IDENT'        // identifier
  | 'HOLE'         // ?name
  | 'NUMBER'       // numeric literal (for Type_n)
  | 'LPAREN'       // (
  | 'RPAREN'       // )
  | 'LBRACE'       // {
  | 'RBRACE'       // }
  | 'COLON'        // :
  | 'COMMA'        // ,
  | 'DOT'          // .
  | 'ARROW'        // ->
  | 'FATARROW'     // =>
  | 'LAMBDA'       // λ or \ or fun
  // PI token removed - use (x : T) -> ... syntax instead
  | 'LET'          // let
  | 'IN'           // in
  | 'ASSIGN'       // :=
  | 'TYPE'         // Type
  | 'PROP'         // Prop
  | 'UNDERSCORE'   // _
  | 'OPERATOR'     // infix/prefix operators
  | 'EOF'          // end of input
  | 'NEWLINE'      // newline (for separating declarations)
  | 'DEF'          // def keyword
  | 'THEOREM'      // theorem keyword
  | 'AXIOM'        // axiom keyword
  | 'SEMICOLON'    // ;
  | 'INDUCTIVE'    // inductive keyword
  | 'WHERE'        // where keyword
  | 'PIPE'         // |
  | 'CASE'         // case keyword
  | 'MATCH';       // match keyword

export interface Token {
  type: TokenType;
  value: string;
  pos: number;
  line: number;
  col: number;
}

// ============================================================================
// Operator Registry
// ============================================================================

export type Associativity = 'left' | 'right' | 'none';

export interface OperatorInfo {
  symbol: string;
  precedence: number;
  associativity: Associativity;
  // If provided, this is the name of the constant to use
  constName?: string;
}

/**
 * Default operator registry with common mathematical operators.
 */
export const DEFAULT_OPERATORS: Record<string, OperatorInfo> = {
  // Arithmetic (higher precedence binds tighter)
  '+': { symbol: '+', precedence: 65, associativity: 'left', constName: 'add' },
  '-': { symbol: '-', precedence: 65, associativity: 'left', constName: 'sub' },
  '*': { symbol: '*', precedence: 70, associativity: 'left', constName: 'mul' },
  '/': { symbol: '/', precedence: 70, associativity: 'left', constName: 'div' },
  '^': { symbol: '^', precedence: 80, associativity: 'right', constName: 'pow' },

  // Comparison
  '=': { symbol: '=', precedence: 50, associativity: 'none', constName: 'Eq' },
  '==': { symbol: '==', precedence: 50, associativity: 'none', constName: 'eq' },
  '≠': { symbol: '≠', precedence: 50, associativity: 'none', constName: 'ne' },
  '!=': { symbol: '!=', precedence: 50, associativity: 'none', constName: 'ne' },
  '<': { symbol: '<', precedence: 50, associativity: 'none', constName: 'lt' },
  '>': { symbol: '>', precedence: 50, associativity: 'none', constName: 'gt' },
  '≤': { symbol: '≤', precedence: 50, associativity: 'none', constName: 'le' },
  '<=': { symbol: '<=', precedence: 50, associativity: 'none', constName: 'le' },
  '≥': { symbol: '≥', precedence: 50, associativity: 'none', constName: 'ge' },
  '>=': { symbol: '>=', precedence: 50, associativity: 'none', constName: 'ge' },

  // Logical
  '∧': { symbol: '∧', precedence: 35, associativity: 'right', constName: 'And' },
  '&&': { symbol: '&&', precedence: 35, associativity: 'right', constName: 'And' },
  '∨': { symbol: '∨', precedence: 30, associativity: 'right', constName: 'Or' },
  '||': { symbol: '||', precedence: 30, associativity: 'right', constName: 'Or' },

  // Function composition
  '∘': { symbol: '∘', precedence: 90, associativity: 'right', constName: 'comp' },

  // List/String
  '++': { symbol: '++', precedence: 55, associativity: 'right', constName: 'append' },
  '::': { symbol: '::', precedence: 67, associativity: 'right', constName: 'cons' },
};

// Arrow is special - handled separately from user operators
const ARROW_PRECEDENCE = 25; // Low precedence, right-associative

// Application has a high precedence
const APPLICATION_PRECEDENCE = 100;

// ============================================================================
// Lexer
// ============================================================================

export class Lexer {
  private pos = 0;
  private line = 1;
  private col = 1;
  private tokens: Token[] = [];

  constructor(
    private input: string,
    private operators: Record<string, OperatorInfo> = DEFAULT_OPERATORS
  ) { }

  tokenize(): Token[] {
    this.tokens = [];
    this.pos = 0;
    this.line = 1;
    this.col = 1;

    while (this.pos < this.input.length) {
      this.skipWhitespaceAndComments();
      if (this.pos >= this.input.length) break;

      const token = this.nextToken();
      if (token) {
        this.tokens.push(token);
      }
    }

    this.tokens.push({ type: 'EOF', value: '', pos: this.pos, line: this.line, col: this.col });
    return this.tokens;
  }

  private skipWhitespaceAndComments(): void {
    while (this.pos < this.input.length) {
      const ch = this.input[this.pos];

      // Handle newlines separately to track for declaration separation
      if (ch === '\n') {
        // Add newline token for declaration separation
        this.tokens.push({ type: 'NEWLINE', value: '\n', pos: this.pos, line: this.line, col: this.col });
        this.pos++;
        this.line++;
        this.col = 1;
        continue;
      }

      // Skip other whitespace
      if (ch === ' ' || ch === '\t' || ch === '\r') {
        this.pos++;
        this.col++;
        continue;
      }

      // Skip line comments (-- ...)
      if (ch === '-' && this.input[this.pos + 1] === '-') {
        while (this.pos < this.input.length && this.input[this.pos] !== '\n') {
          this.pos++;
        }
        continue;
      }

      // Skip block comments (/- ... -/)
      if (ch === '/' && this.input[this.pos + 1] === '-') {
        this.pos += 2;
        this.col += 2;
        let depth = 1;
        while (this.pos < this.input.length && depth > 0) {
          if (this.input[this.pos] === '/' && this.input[this.pos + 1] === '-') {
            depth++;
            this.pos += 2;
            this.col += 2;
          } else if (this.input[this.pos] === '-' && this.input[this.pos + 1] === '/') {
            depth--;
            this.pos += 2;
            this.col += 2;
          } else if (this.input[this.pos] === '\n') {
            this.pos++;
            this.line++;
            this.col = 1;
          } else {
            this.pos++;
            this.col++;
          }
        }
        continue;
      }

      // Skip multiline comments ({- ... -})
      if (ch === '{' && this.input[this.pos + 1] === '-') {
        this.pos += 2;
        this.col += 2;
        let depth = 1;
        while (this.pos < this.input.length && depth > 0) {
          if (this.input[this.pos] === '{' && this.input[this.pos + 1] === '-') {
            depth++;
            this.pos += 2;
            this.col += 2;
          } else if (this.input[this.pos] === '-' && this.input[this.pos + 1] === '}') {
            depth--;
            this.pos += 2;
            this.col += 2;
          } else if (this.input[this.pos] === '\n') {
            this.pos++;
            this.line++;
            this.col = 1;
          } else {
            this.pos++;
            this.col++;
          }
        }
        continue;
      }

      break;
    }
  }

  private nextToken(): Token | null {
    const startPos = this.pos;
    const startLine = this.line;
    const startCol = this.col;
    const ch = this.input[this.pos];

    // Single character tokens (but check for || before |)
    switch (ch) {
      case '(':
        this.pos++; this.col++;
        return { type: 'LPAREN', value: '(', pos: startPos, line: startLine, col: startCol };
      case ')':
        this.pos++; this.col++;
        return { type: 'RPAREN', value: ')', pos: startPos, line: startLine, col: startCol };
      case '{':
        this.pos++; this.col++;
        return { type: 'LBRACE', value: '{', pos: startPos, line: startLine, col: startCol };
      case '}':
        this.pos++; this.col++;
        return { type: 'RBRACE', value: '}', pos: startPos, line: startLine, col: startCol };
      case ',':
        this.pos++; this.col++;
        return { type: 'COMMA', value: ',', pos: startPos, line: startLine, col: startCol };
      case '.':
        this.pos++; this.col++;
        return { type: 'DOT', value: '.', pos: startPos, line: startLine, col: startCol };
      case ';':
        this.pos++; this.col++;
        return { type: 'SEMICOLON', value: ';', pos: startPos, line: startLine, col: startCol };
      case '|':
        // Check for || operator first
        if (this.input[this.pos + 1] === '|') {
          // Don't tokenize as PIPE, fall through to operator handling
          break;
        }
        this.pos++; this.col++;
        return { type: 'PIPE', value: '|', pos: startPos, line: startLine, col: startCol };
      case '_':
        // Check if it's just underscore or part of an identifier
        if (!this.isIdentChar(this.input[this.pos + 1])) {
          this.pos++; this.col++;
          return { type: 'UNDERSCORE', value: '_', pos: startPos, line: startLine, col: startCol };
        }
        break;
    }

    // Lambda: \ or fun (removed λ unicode support)
    if (ch === '\\') {
      this.pos++; this.col++;
      return { type: 'LAMBDA', value: ch, pos: startPos, line: startLine, col: startCol };
    }

    // Arrow: -> only (removed support for → unicode and Π)
    if (ch === '-' && this.input[this.pos + 1] === '>') {
      this.pos += 2; this.col += 2;
      return { type: 'ARROW', value: '->', pos: startPos, line: startLine, col: startCol };
    }

    // Fat arrow: =>
    if (ch === '=' && this.input[this.pos + 1] === '>') {
      this.pos += 2; this.col += 2;
      return { type: 'FATARROW', value: '=>', pos: startPos, line: startLine, col: startCol };
    }

    // Assignment: :=
    if (ch === ':' && this.input[this.pos + 1] === '=') {
      this.pos += 2; this.col += 2;
      return { type: 'ASSIGN', value: ':=', pos: startPos, line: startLine, col: startCol };
    }

    // Colon
    if (ch === ':') {
      this.pos++; this.col++;
      return { type: 'COLON', value: ':', pos: startPos, line: startLine, col: startCol };
    }

    // Hole: ?name
    if (ch === '?') {
      this.pos++; this.col++;
      const name = this.readWhile(c => this.isIdentChar(c));
      return { type: 'HOLE', value: name || '_', pos: startPos, line: startLine, col: startCol };
    }

    // Numbers
    if (this.isDigit(ch)) {
      const num = this.readWhile(c => this.isDigit(c));
      return { type: 'NUMBER', value: num, pos: startPos, line: startLine, col: startCol };
    }

    // Identifiers and keywords
    if (this.isIdentStart(ch)) {
      const ident = this.readWhile(c => this.isIdentChar(c));

      // Check for keywords
      switch (ident) {
        case 'fun':
          return { type: 'LAMBDA', value: 'fun', pos: startPos, line: startLine, col: startCol };
        // Removed 'forall' - use (x : T) -> ... syntax instead
        case 'let':
          return { type: 'LET', value: 'let', pos: startPos, line: startLine, col: startCol };
        case 'in':
          return { type: 'IN', value: 'in', pos: startPos, line: startLine, col: startCol };
        case 'Type':
          return { type: 'TYPE', value: 'Type', pos: startPos, line: startLine, col: startCol };
        case 'Prop':
          return { type: 'PROP', value: 'Prop', pos: startPos, line: startLine, col: startCol };
        case 'def':
          return { type: 'DEF', value: 'def', pos: startPos, line: startLine, col: startCol };
        case 'theorem':
          return { type: 'THEOREM', value: 'theorem', pos: startPos, line: startLine, col: startCol };
        case 'axiom':
          return { type: 'AXIOM', value: 'axiom', pos: startPos, line: startLine, col: startCol };
        case 'inductive':
          return { type: 'INDUCTIVE', value: 'inductive', pos: startPos, line: startLine, col: startCol };
        case 'where':
          return { type: 'WHERE', value: 'where', pos: startPos, line: startLine, col: startCol };
        case 'case':
          return { type: 'CASE', value: 'case', pos: startPos, line: startLine, col: startCol };
        case 'match':
          return { type: 'MATCH', value: 'match', pos: startPos, line: startLine, col: startCol };
        default:
          // Check for Type_n pattern (e.g., Type_0, Type_1, Type_42)
          if (ident.startsWith('Type_')) {
            const suffix = ident.substring(5);
            // Verify suffix is all digits
            if (/^\d+$/.test(suffix)) {
              return { type: 'TYPE', value: ident, pos: startPos, line: startLine, col: startCol };
            }
          }
          return { type: 'IDENT', value: ident, pos: startPos, line: startLine, col: startCol };
      }
    }

    // Check for multi-character operators (must come before single char operator check)
    const twoChar = this.input.slice(this.pos, this.pos + 2);
    if (this.operators[twoChar]) {
      this.pos += 2; this.col += 2;
      return { type: 'OPERATOR', value: twoChar, pos: startPos, line: startLine, col: startCol };
    }

    // Check for single-character operators
    if (this.operators[ch]) {
      this.pos++; this.col++;
      return { type: 'OPERATOR', value: ch, pos: startPos, line: startLine, col: startCol };
    }

    // Unknown character - throw error
    throw new ParseError(`Unexpected character: '${ch}'`, startLine, startCol);
  }

  private readWhile(predicate: (ch: string) => boolean): string {
    let result = '';
    while (this.pos < this.input.length && predicate(this.input[this.pos])) {
      result += this.input[this.pos];
      this.pos++;
      this.col++;
    }
    return result;
  }

  private isDigit(ch: string): boolean {
    return ch >= '0' && ch <= '9';
  }

  private isIdentStart(ch: string): boolean {
    return (ch >= 'a' && ch <= 'z') ||
      (ch >= 'A' && ch <= 'Z') ||
      ch === '_' ||
      // Greek letters
      (ch >= 'α' && ch <= 'ω') ||
      (ch >= 'Α' && ch <= 'Ω') ||
      // Mathematical symbols that can start identifiers
      ch === 'ℕ' || ch === 'ℤ' || ch === 'ℚ' || ch === 'ℝ' || ch === 'ℂ';
  }

  private isIdentChar(ch: string): boolean {
    return this.isIdentStart(ch) || this.isDigit(ch) || ch === '\'' || ch === '₀' || ch === '₁' || ch === '₂';
  }
}

// ============================================================================
// Parse Error
// ============================================================================

export class ParseError extends Error {
  constructor(message: string, public line: number, public col: number) {
    super(`Parse error at line ${line}, col ${col}: ${message}`);
    this.name = 'ParseError';
  }
}

/**
 * Container for multiple parse errors
 */
export class ParseErrors extends Error {
  constructor(public errors: ParseError[]) {
    super(`${errors.length} parse error${errors.length !== 1 ? 's' : ''}`);
    this.name = 'ParseErrors';
  }
}

// ============================================================================
// Parser
// ============================================================================

/**
 * Context for name resolution during parsing.
 * Maps variable names to their De Bruijn indices.
 */
type NameContext = string[];

/**
 * Result of parsing a top-level declaration.
 */
export interface ParsedDeclaration {
  kind: 'def' | 'theorem' | 'axiom' | 'expr' | 'inductive';
  name?: string;
  type?: TTerm;
  value?: TTerm;
  constructors?: Array<{ name: string; type: TTerm }>;
}

/**
 * Result of parsing a declaration with source position tracking.
 */
export interface ParsedDeclarationWithSource {
  decl: ParsedDeclaration;
  sourceMap: SourceMap;
}

/**
 * Pratt parser for the TT language.
 */
export class Parser {
  private tokens: Token[] = [];
  private pos = 0;
  private currentSourceMap: SourceMap = new Map();
  private currentPath: IndexPath = [];

  constructor(
    private operators: Record<string, OperatorInfo> = DEFAULT_OPERATORS
  ) { }

  /**
   * Prefix all paths in the source map that start with `basePath` by adding `suffix`.
   * This is used when we parse a term and then discover it's part of a larger structure.
   * For example, when parsing `Na -> Nat`, we parse `Na` at path `p`, then discover
   * it's the domain of a Pi, so we need to update it to `p.domain`.
   */
  private prefixSourceMapPaths(basePath: IndexPath, suffix: IndexPathSegment): void {
    const basePathStr = serializeIndexPath(basePath);
    const newEntries = new Map<string, SourceRange>();

    for (const [pathStr, range] of this.currentSourceMap) {
      // Check if this path starts with basePath
      if (pathStr === basePathStr || pathStr.startsWith(basePathStr + '.') || pathStr.startsWith(basePathStr + '[')) {
        // Extract the part after basePath
        const remainder = pathStr === basePathStr ? '' : pathStr.substring(basePathStr.length);
        // Insert suffix after basePath
        const newPath = [...basePath, suffix];
        const newPathStr = serializeIndexPath(newPath) + remainder;
        newEntries.set(newPathStr, range);
      } else {
        // Keep as-is
        newEntries.set(pathStr, range);
      }
    }

    this.currentSourceMap = newEntries;
  }

  /**
   * Parse a single expression from source code.
   */
  parseExpr(source: string): TTerm {
    const lexer = new Lexer(source, this.operators);
    this.tokens = lexer.tokenize();
    // Filter out newlines for expression parsing
    this.tokens = this.tokens.filter(t => t.type !== 'NEWLINE');
    this.pos = 0;

    const result = this.expr(0, []);

    if (this.current().type !== 'EOF') {
      throw new ParseError(
        `Unexpected token: ${this.current().value}`,
        this.current().line,
        this.current().col
      );
    }

    return result;
  }

  /**
   * Parse multiple top-level declarations from source code.
   *
   * Handles Lean-style declaration pairs where type signature and definition
   * are on separate lines:
   *   name : type
   *   name = value
   *
   * These are merged into a single declaration with both type and value.
   *
   * Error recovery: If a parse error occurs, we skip to the next line and
   * continue parsing to collect as many errors as possible.
   */
  parseDeclarations(source: string): ParsedDeclaration[] {
    const lexer = new Lexer(source, this.operators);
    this.tokens = lexer.tokenize();
    this.pos = 0;

    const declarations: ParsedDeclaration[] = [];
    const errors: ParseError[] = [];

    while (this.current().type !== 'EOF') {
      this.skipNewlines();
      if (this.current().type === 'EOF') break;

      try {
        const decl = this.parseDeclaration(declarations);
        if (decl) {
          // Check if this declaration can be merged with the previous one
          const prev = declarations[declarations.length - 1];

          // Case 1: Merge type signature with definition
          // prev has type but no value, current has same name and value but no type
          if (prev &&
              prev.name &&
              decl.name === prev.name &&
              prev.type && !prev.value &&
              decl.value && !decl.type) {
            // Merge: add value to previous declaration
            prev.value = decl.value;
          }
          // Case 2: Merge multiple pattern clauses
          // Both have the same name, both have Match expressions as values
          else if (prev &&
                   prev.name &&
                   decl.name === prev.name &&
                   prev.value?.tag === 'Match' &&
                   decl.value?.tag === 'Match') {
            // Merge clauses from decl into prev
            prev.value.clauses.push(...decl.value.clauses);
          }
          else {
            declarations.push(decl);
          }
        }
      } catch (e) {
        if (e instanceof ParseError) {
          errors.push(e);
          // Skip to the next line to continue parsing
          this.skipToNextLine();
        } else {
          // Re-throw non-parse errors
          throw e;
        }
      }
    }

    // If we collected any errors, throw them all
    if (errors.length > 0) {
      throw new ParseErrors(errors);
    }

    return declarations;
  }

  /**
   * Parse multiple top-level declarations with source position tracking.
   *
   * This is similar to parseDeclarations but also returns source maps
   * for each declaration, enabling error messages to reference exact
   * source locations.
   *
   * Returns an array of {decl, sourceMap} objects, one per successfully
   * parsed declaration.
   */
  parseDeclarationsWithSource(source: string, prevDeclarations?: ParsedDeclaration[]): ParsedDeclarationWithSource[] {
    const lexer = new Lexer(source, this.operators);
    this.tokens = lexer.tokenize();
    this.pos = 0;

    const results: ParsedDeclarationWithSource[] = [];
    const errors: ParseError[] = [];

    // Combine previous declarations with current results for pattern matching detection
    const allPrevDecls = [...(prevDeclarations || [])];

    while (this.current().type !== 'EOF') {
      this.skipNewlines();
      if (this.current().type === 'EOF') break;

      // Reset source map for each declaration
      this.currentSourceMap = new Map();
      this.currentPath = [];

      try {
        // Pass both previous declarations AND current results
        const decl = this.parseDeclaration([...allPrevDecls, ...results.map(r => r.decl)]);
        if (decl) {
          // Check if this declaration can be merged with the previous one
          const prev = results[results.length - 1];

          // Case 1: Merge type signature with definition
          if (prev &&
              prev.decl.name &&
              decl.name === prev.decl.name &&
              prev.decl.type && !prev.decl.value &&
              decl.value && !decl.type) {
            // Merge: add value to previous declaration
            // Also merge the source maps
            prev.decl.value = decl.value;
            // Copy all entries from current source map to previous
            for (const [key, range] of this.currentSourceMap) {
              prev.sourceMap.set(key, range);
            }
          }
          // Case 2: Merge multiple pattern clauses
          else if (prev &&
                   prev.decl.name &&
                   decl.name === prev.decl.name &&
                   prev.decl.value?.tag === 'Match' &&
                   decl.value?.tag === 'Match') {
            // The new clause will be appended, so its index is the current length
            const newClauseIndex = prev.decl.value.clauses.length;

            // Merge clauses
            prev.decl.value.clauses.push(...decl.value.clauses);

            // Merge source maps, adjusting clause indices
            // Paths like "value.clauses[0].rhs..." need to become "value.clauses[N].rhs..."
            for (const [key, range] of this.currentSourceMap) {
              // Replace "value.clauses[0]" with "value.clauses[N]"
              const adjustedKey = key.replace(
                /^value\.clauses\[0\]/,
                `value.clauses[${newClauseIndex}]`
              );
              prev.sourceMap.set(adjustedKey, range);
            }
          }
          else {
            // New declaration - save it with its source map
            results.push({
              decl,
              sourceMap: new Map(this.currentSourceMap)
            });
          }
        }
      } catch (e) {
        if (e instanceof ParseError) {
          errors.push(e);
          // Skip to the next line to continue parsing
          this.skipToNextLine();
        } else {
          // Re-throw non-parse errors
          throw e;
        }
      }
    }

    // If we collected any errors, throw them all
    if (errors.length > 0) {
      throw new ParseErrors(errors);
    }

    return results;
  }

  /**
   * Skip tokens until we reach a newline or EOF.
   * Used for error recovery.
   */
  private skipToNextLine(): void {
    while (this.current().type !== 'EOF' && this.current().type !== 'NEWLINE') {
      this.advance();
    }
    // Skip the newline itself
    if (this.current().type === 'NEWLINE') {
      this.advance();
    }
  }

  private skipNewlines(): void {
    while (this.current().type === 'NEWLINE') {
      this.advance();
    }
  }

  private parseDeclaration(prevDeclarations?: ParsedDeclaration[]): ParsedDeclaration | null {
    const current = this.current();

    // Inductive: inductive name : type where constructors
    if (current.type === 'INDUCTIVE') {
      return this.parseInductiveDeclaration();
    }

    // Legacy: def name : type := value
    if (current.type === 'DEF') {
      return this.parseLegacyDefDeclaration();
    }

    // Legacy: theorem name : type := value
    if (current.type === 'THEOREM') {
      return this.parseLegacyTheoremDeclaration();
    }

    // Legacy: axiom name : type
    if (current.type === 'AXIOM') {
      return this.parseLegacyAxiomDeclaration();
    }

    // New syntax: name : type  or  name = impl
    if (current.type === 'IDENT') {
      return this.parseNamedDeclaration(prevDeclarations);
    }

    // Otherwise it's a bare expression
    const expr = this.expr(0, []);
    return { kind: 'expr', value: expr };
  }

  /**
   * Parse new-style declaration:
   * - name : type (type signature only)
   * - name = impl (definition only, type will be inferred - only at line start)
   * - name pattern1 pattern2 = rhs (pattern clause definition)
   *
   * For same-line type+definition, use := to avoid ambiguity with equality type:
   * - name : type := impl
   */
  private parseNamedDeclaration(prevDeclarations?: ParsedDeclaration[]): ParsedDeclaration {
    const nameToken = this.expect('IDENT');
    const name = nameToken.value;

    // Skip any newlines after the name (e.g., between blocks)
    this.skipNewlines();

    // Check what follows the name
    const next = this.current();

    // name : type
    if (next.type === 'COLON') {
      this.advance(); // consume ':'
      // Parse the full type expression (including = as equality operator)
      // Track source positions with path "type"
      const typePath: IndexPath = [{ kind: 'field', name: 'type' }];
      const type = this.expr(0, [], typePath);

      // Only := works for same-line definition (to avoid ambiguity with = in types)
      if (this.current().type === 'ASSIGN') {
        this.advance(); // consume ':='
        const valuePath: IndexPath = [{ kind: 'field', name: 'value' }];
        const value = this.expr(0, [], valuePath);
        return { kind: 'def', name, type, value };
      }

      // Type signature only
      return { kind: 'def', name, type };
    }

    // name = impl (definition at line start, without type annotation)
    // Check this BEFORE pattern clause detection to handle:
    //   foo : Type 1
    //   foo = Type   <-- this is a simple definition, not a pattern clause
    if (next.type === 'OPERATOR' && next.value === '=') {
      this.advance(); // consume '='
      const value = this.expr(0, []);
      return { kind: 'def', name, value };
    }

    // name := impl (definition without type annotation, using :=)
    if (next.type === 'ASSIGN') {
      this.advance(); // consume ':='
      const value = this.expr(0, []);
      return { kind: 'def', name, value };
    }

    // Check if this is a pattern clause: name pattern1 pattern2 = rhs
    // We know it's a pattern clause if:
    // 1. We've already seen a type signature for this name, OR
    // 2. The next token can start a pattern (IDENT, UNDERSCORE, LPAREN)
    const hasSeenSignature = prevDeclarations?.some(d => d.name === name && d.type);

    if (hasSeenSignature || this.canStartPattern(next)) {
      return this.parsePatternClauseDefinition(name);
    }

    // Not a declaration pattern, backtrack and parse as expression
    this.pos--; // backtrack to before the identifier
    const expr = this.expr(0, []);
    return { kind: 'expr', value: expr };
  }

  /**
   * Parse pattern clause definition:
   *   plus Zero b = b
   *   plus (Succ a) b = Succ (plus a b)
   *
   * This is syntactic sugar that will be converted to a Match expression.
   * For now, we just parse a single clause and return it.
   * Multiple clauses will be merged by parseDeclarations.
   */
  private parsePatternClauseDefinition(funcName: string): ParsedDeclaration {
    // Track the start of the clause for source position tracking
    const clauseStartPos = this.getCurrentPos();

    // Build base path for patterns: value.clauses[0].patterns[i]
    const clausePath: IndexPath = [
      { kind: 'field', name: 'value' },
      { kind: 'field', name: 'clauses' },
      { kind: 'array', index: 0 }
    ];

    // Parse patterns until we hit '='
    // Each pattern is atomic (no constructor application without parens)
    const patterns: TPattern[] = [];

    while (this.canStartPattern(this.current())) {
      const patternIndex = patterns.length;
      const patternPath: IndexPath = [
        ...clausePath,
        { kind: 'field', name: 'patterns' },
        { kind: 'array', index: patternIndex }
      ];
      patterns.push(this.parsePatternAtomWithSource(patternPath));
    }

    if (patterns.length === 0) {
      throw new ParseError(
        `Expected at least one pattern in pattern clause for '${funcName}'`,
        this.current().line,
        this.current().col
      );
    }

    // Expect '='
    if (this.current().type !== 'OPERATOR' || this.current().value !== '=') {
      throw new ParseError(
        `Expected '=' in pattern clause, got ${this.current().type} '${this.current().value}'`,
        this.current().line,
        this.current().col
      );
    }
    this.advance(); // consume '='

    // Parse RHS with pattern variables bound
    // Pattern vars are collected left-to-right, depth-first. But in De Bruijn,
    // index 0 is the most recently bound variable (the last one collected).
    // So we reverse the list to match the type-checker's context ordering.
    const patternVars = patterns.flatMap(p => this.collectPatternVars(p));
    const rhsCtx = [...patternVars].reverse();

    // Track source positions with path value.clauses[0].rhs
    // (We use index 0 here, but it will be adjusted during merging if needed)
    const rhsPath: IndexPath = [...clausePath, { kind: 'field', name: 'rhs' }];

    const rhs = this.expr(0, rhsCtx, rhsPath);

    // Track the clause itself in the source map (from first pattern to end of RHS)
    const clauseEndPos = this.getPrevEndPos();
    const clauseKey = serializeIndexPath(clausePath);
    this.currentSourceMap.set(clauseKey, createSourceRange(clauseStartPos, clauseEndPos));

    // Create a Match expression as a placeholder
    // This will be merged with other clauses and wrapped in lambdas later
    return {
      kind: 'def',
      name: funcName,
      value: {
        tag: 'Match',
        // Placeholder scrutinee - will be fixed during elaboration/desugaring
        scrutinee: mkHole('_scrutinee', mkHole('_scrutinee_type', mkProp())),
        clauses: [{
          patterns,
          rhs
        }]
      }
    };
  }

  private parseLegacyDefDeclaration(): ParsedDeclaration {
    this.expect('DEF');
    const nameToken = this.expect('IDENT');
    this.expect('COLON');
    const type = this.expr(0, []);
    this.expect('ASSIGN');
    const value = this.expr(0, []);

    return {
      kind: 'def',
      name: nameToken.value,
      type,
      value
    };
  }

  private parseLegacyTheoremDeclaration(): ParsedDeclaration {
    this.expect('THEOREM');
    const nameToken = this.expect('IDENT');
    this.expect('COLON');
    const type = this.expr(0, []);
    this.expect('ASSIGN');
    const value = this.expr(0, []);

    return {
      kind: 'theorem',
      name: nameToken.value,
      type,
      value
    };
  }

  private parseLegacyAxiomDeclaration(): ParsedDeclaration {
    this.expect('AXIOM');
    const nameToken = this.expect('IDENT');
    this.expect('COLON');
    const type = this.expr(0, []);

    return {
      kind: 'axiom',
      name: nameToken.value,
      type
    };
  }

  /**
   * Parse inductive type declaration:
   * inductive Name : Type where
   *   | Constructor1 : Type1
   *   | Constructor2 : Type2
   *   ...
   *
   * Or without 'where' keyword:
   * inductive Name : Type
   *   Constructor1 : Type1
   *   Constructor2 : Type2
   */
  private parseInductiveDeclaration(): ParsedDeclaration {
    this.expect('INDUCTIVE');
    const nameToken = this.expect('IDENT');
    this.expect('COLON');

    // Parse type, but stop at 'where' keyword
    // The type can span multiple lines, so we only stop at WHERE
    // Track source positions with path 'type'
    const typePath: IndexPath = [{ kind: 'field', name: 'type' }];
    const type = this.exprUntil(0, [], ['WHERE'], typePath);

    // Skip any newlines before 'where'
    this.skipNewlines();

    // Expect 'where' keyword (it's required to know where the type ends)
    this.expect('WHERE');

    // Skip newlines before constructors
    this.skipNewlines();

    // Parse constructors
    const constructors: Array<{ name: string; type: TTerm }> = [];
    let ctorIndex = 0;

    while (this.current().type !== 'EOF') {
      // Check for pipe or identifier (constructors can start with either)
      const current = this.current();

      // Stop if we hit something that's not a constructor
      if (current.type !== 'PIPE' && current.type !== 'IDENT') {
        break;
      }

      // Optional pipe before constructor
      if (current.type === 'PIPE') {
        this.advance();
      }

      // Parse constructor: name : type
      if (this.current().type !== 'IDENT') {
        break; // No more constructors
      }

      const ctorName = this.expect('IDENT').value;
      this.expect('COLON');

      // Build path for this constructor's type: constructors[ctorIndex].type
      const ctorPath: IndexPath = [
        { kind: 'field', name: 'constructors' },
        { kind: 'array', index: ctorIndex },
        { kind: 'field', name: 'type' }
      ];
      const ctorType = this.expr(0, [], ctorPath);

      constructors.push({ name: ctorName, type: ctorType });
      ctorIndex++;

      // Skip newlines between constructors
      this.skipNewlines();
    }

    return {
      kind: 'inductive',
      name: nameToken.value,
      type,
      constructors
    };
  }

  /**
   * Parse expression but stop when encountering any of the specified token types.
   * This is useful for parsing expressions in contexts where certain keywords
   * act as terminators (e.g., 'where' in inductive declarations).
   */
  private exprUntil(minPrec: number, ctx: NameContext, stopTokens: TokenType[], path: IndexPath = []): TTerm {
    // Capture start position for recording the full expression range
    const startToken = this.current();

    let left = this.parsePrefix(ctx, path);

    while (true) {
      // Skip newlines within the expression (allow multiline expressions)
      while (this.current().type === 'NEWLINE') {
        this.advance();
      }

      const token = this.current();

      // Stop if we hit a terminating token
      if (stopTokens.includes(token.type)) {
        break;
      }

      // Check for arrow (right-associative, low precedence)
      if (token.type === 'ARROW') {
        if (ARROW_PRECEDENCE < minPrec) break;
        this.advance();

        // Update left side to be at 'domain' path
        this.prefixSourceMapPaths(path, { kind: 'field', name: 'domain' });

        const arrowCtx = ['_', ...ctx];
        const bodyPath = [...path, { kind: 'field' as const, name: 'body' }];
        const right = this.exprUntil(ARROW_PRECEDENCE, arrowCtx, stopTokens, bodyPath);
        left = mkPi(left, right, '_');
        continue;
      }

      // Check for infix operators
      if (token.type === 'OPERATOR') {
        const opInfo = this.operators[token.value];
        if (!opInfo || opInfo.precedence < minPrec) break;

        this.advance();

        let rightPrec = opInfo.precedence;
        if (opInfo.associativity === 'left') {
          rightPrec = opInfo.precedence + 1;
        } else if (opInfo.associativity === 'none') {
          rightPrec = opInfo.precedence + 1;
        }

        const right = this.exprUntil(rightPrec, ctx, stopTokens);

        const opConst = mkConst(opInfo.constName || token.value, mkHole('op_type', mkProp()));
        left = mkApp(mkApp(opConst, left), right);
        continue;
      }

      // Check for application (juxtaposition)
      if (this.canStartAtom(token)) {
        if (APPLICATION_PRECEDENCE < minPrec) break;

        // Before moving paths, record the current application's range at path.
        // This is crucial for intermediate applications: when we have "f y x",
        // after parsing "f y" we need to record that "f y" spans path
        // BEFORE we shift things down to make room for x.
        // This entry will get moved to path.fn by prefixSourceMapPaths below.
        if (path.length > 0 && this.pos > 0) {
          const prevToken = this.tokens[this.pos - 1];
          this.recordRange(path, startToken, prevToken);
        }

        // The left side (function) has already been parsed at `path`.
        // Now we need to update it to be at `path.fn` and parse the arg at `path.arg`.
        this.prefixSourceMapPaths(path, { kind: 'field', name: 'fn' });

        const argPath = [...path, { kind: 'field' as const, name: 'arg' }];
        const arg = this.parsePrefix(ctx, argPath);
        left = mkApp(left, arg);
        continue;
      }

      break;
    }

    return left;
  }

  /**
   * Main Pratt parser expression handler.
   * @param minPrec Minimum precedence to continue parsing
   * @param ctx Name context for De Bruijn index resolution
   */
  private expr(minPrec: number, ctx: NameContext, path: IndexPath = []): TTerm {
    // Capture start position for recording the full expression range
    const startToken = this.current();

    // Parse the initial prefix expression
    // Note: We parse with the base path, then adjust if it becomes part of a larger structure
    let left = this.parsePrefix(ctx, path);

    while (true) {
      const token = this.current();

      // Check for arrow (right-associative, low precedence)
      if (token.type === 'ARROW') {
        if (ARROW_PRECEDENCE < minPrec) break;
        this.advance();
        // Right-associative: parse RHS with same precedence
        // IMPORTANT: We need to extend the context with the anonymous binder
        // so that De Bruijn indices in the RHS are correctly shifted
        const arrowCtx = ['_', ...ctx];

        // The left side (domain) has already been parsed at `path`.
        // Now we need to update all those positions to be under `path.domain`.
        this.prefixSourceMapPaths(path, { kind: 'field', name: 'domain' });

        // Parse body with extended path for position tracking
        const bodyPath = [...path, { kind: 'field' as const, name: 'body' }];
        const right = this.expr(ARROW_PRECEDENCE, arrowCtx, bodyPath);

        // Non-dependent arrow: Π (_: left) . right
        left = mkPi(left, right, '_');
        continue;
      }

      // Check for infix operators
      if (token.type === 'OPERATOR') {
        const opInfo = this.operators[token.value];
        if (!opInfo || opInfo.precedence < minPrec) break;

        this.advance();

        // Calculate right precedence based on associativity
        let rightPrec = opInfo.precedence;
        if (opInfo.associativity === 'left') {
          rightPrec = opInfo.precedence + 1;
        } else if (opInfo.associativity === 'none') {
          rightPrec = opInfo.precedence + 1;
        }
        // right-associative uses same precedence

        const right = this.expr(rightPrec, ctx, path);

        // Create binary application: op left right
        const opConst = mkConst(opInfo.constName || token.value, mkHole('op_type', mkProp()));
        left = mkApp(mkApp(opConst, left), right);
        continue;
      }

      // Check for application (juxtaposition)
      if (this.canStartAtom(token)) {
        if (APPLICATION_PRECEDENCE < minPrec) break;

        // Before moving paths, record the current application's range at path.
        // This is crucial for intermediate applications: when we have "f y x",
        // after parsing "f y" we need to record that "f y" spans path
        // BEFORE we shift things down to make room for x.
        // This entry will get moved to path.fn by prefixSourceMapPaths below.
        if (path.length > 0 && this.pos > 0) {
          const prevToken = this.tokens[this.pos - 1];
          this.recordRange(path, startToken, prevToken);
        }

        // The left side (function) has already been parsed at `path`.
        // Now we need to update it to be at `path.fn` and parse the arg at `path.arg`.
        this.prefixSourceMapPaths(path, { kind: 'field', name: 'fn' });

        const argPath = [...path, { kind: 'field' as const, name: 'arg' }];
        const arg = this.parsePrefix(ctx, argPath);
        left = mkApp(left, arg);
        continue;
      }

      break;
    }

    // Record the full expression range for this path
    // Use the previous token as the end (the last token we consumed)
    if (path.length > 0 && this.pos > 0) {
      const endToken = this.tokens[this.pos - 1];
      this.recordRange(path, startToken, endToken);
    }

    return left;
  }

  /**
   * Parse prefix expressions and atoms.
   */
  private parsePrefix(ctx: NameContext, path: IndexPath = []): TTerm {
    const token = this.current();

    switch (token.type) {
      case 'LPAREN':
        return this.parseParenExpr(ctx, path);

      case 'LAMBDA':
        return this.parseLambda(ctx, path);

      // PI token removed - use (x : T) -> ... syntax instead

      case 'LET':
        return this.parseLet(ctx, path);

      case 'CASE':
      case 'MATCH':
        return this.parseMatch(ctx, path);

      case 'TYPE':
        return this.parseType(path);

      case 'PROP':
        this.advance();
        return mkProp();

      case 'HOLE':
        this.advance();
        return mkHole(token.value, mkHole('hole_type', mkProp()));

      case 'IDENT':
        return this.parseIdent(ctx, path);

      case 'NUMBER':
        this.advance();
        return this.parseNumberLiteral(token.value);

      case 'UNDERSCORE':
        this.advance();
        return mkHole('_', mkHole('underscore_type', mkProp()));

      default:
        throw new ParseError(
          `Unexpected token: ${token.type} '${token.value}'`,
          token.line,
          token.col
        );
    }
  }

  /**
   * Parse parenthesized expression, which could be:
   * - Simple grouping: (expr)
   * - Type annotation: (expr : type)
   * - Pi binder: (x : A) → B
   */
  private parseParenExpr(ctx: NameContext, path: IndexPath = []): TTerm {
    this.expect('LPAREN');

    // Check if this is a binder: (x : T)
    const startPos = this.pos;

    if (this.current().type === 'IDENT' || this.current().type === 'UNDERSCORE') {
      const nameToken = this.current();
      this.advance();

      if (this.current().type === 'COLON') {
        // This is (x : T) - could be annotation or Pi binder
        this.advance();
        const type = this.expr(0, ctx, path);
        this.expect('RPAREN');

        // Check if followed by arrow - then it's a Pi type
        if (this.current().type === 'ARROW') {
          this.advance();
          const name = nameToken.type === 'UNDERSCORE' ? '_' : nameToken.value;
          const newCtx = [name, ...ctx];
          const body = this.expr(ARROW_PRECEDENCE, newCtx);
          return mkPi(type, body, name);
        }

        // Otherwise it's a type annotation or just a parenthesized typed variable
        // If we parsed (x : T) and there's no arrow, treat it as annotation if x is a term
        // For simplicity, we'll treat single-identifier (x : T) as a typed reference
        // This is tricky - let's assume it's annotation where x is looked up in context
        const name = nameToken.type === 'UNDERSCORE' ? '_' : nameToken.value;
        const idx = ctx.indexOf(name);
        const term = idx >= 0 ? mkVar(idx) : mkConst(name, mkHole('const_type', mkProp()));
        return { tag: 'Annot', term, type };
      } else {
        // Not a binder - backtrack and parse as expression
        this.pos = startPos;
      }
    }

    // Regular parenthesized expression
    const expr = this.expr(0, ctx, path);

    // Check for type annotation
    if (this.current().type === 'COLON') {
      this.advance();
      const type = this.expr(0, ctx, path);
      this.expect('RPAREN');
      return { tag: 'Annot', term: expr, type };
    }

    this.expect('RPAREN');
    return expr;
  }

  /**
   * Parse lambda with new syntax:
   *   \x => body                    -- x's type is a hole
   *   \ x => body                   -- same
   *   \x y => body                  -- multiple untyped binders
   *   \(x : A) => body              -- typed binder
   *   \(x : A) y => body            -- mixed
   *   \(x, y : A) => body           -- multiple names with same type
   *   \(x : A) (y : B) => body      -- multiple typed binders
   *
   * NOT allowed: \ x : A => body    -- parens required for typed binders
   */
  private parseLambda(ctx: NameContext, path: IndexPath = []): TTerm {
    const startToken = this.current();
    this.expect('LAMBDA');

    // Parse binders until we see =>
    // Each binder will have a startToken for position tracking
    const binders: Array<{ name: string; type: TTerm; startToken: Token }> = [];

    while (true) {
      const current = this.current();
      const binderStartToken = current;

      // Stop if we hit the body separator (only => is allowed)
      if (current.type === 'FATARROW') {
        break;
      }

      if (current.type === 'LPAREN') {
        // Typed binder(s): (x : T) or (x, y : T) or (x y : T)
        this.advance();

        // Collect names until we see ':'
        const names: string[] = [];
        while (this.current().type === 'IDENT' || this.current().type === 'UNDERSCORE') {
          const name = this.current().type === 'UNDERSCORE' ? '_' : this.current().value;
          names.push(name);
          this.advance();

          // Allow comma between names: (x, y : T)
          if (this.current().type === 'COMMA') {
            this.advance();
          }
        }

        if (names.length === 0) {
          throw new ParseError('Expected at least one name in binder', this.current().line, this.current().col);
        }

        this.expect('COLON');
        // Parse type - we'll record its position when building the nested lambdas
        const type = this.expr(0, ctx);
        this.expect('RPAREN');

        // Add all names with the same type
        for (const name of names) {
          binders.push({ name, type, startToken: binderStartToken });
          ctx = [name, ...ctx];
        }
      } else if (current.type === 'IDENT' || current.type === 'UNDERSCORE') {
        // Untyped binder: just a name, type will be a hole
        const name = current.type === 'UNDERSCORE' ? '_' : current.value;

        // Peek ahead to check if this is "x : T" without parens (NOT allowed)
        this.advance();
        if (this.current().type === 'COLON') {
          throw new ParseError(
            `Type annotation requires parentheses: use (${name} : T) instead of ${name} : T`,
            this.current().line,
            this.current().col
          );
        }

        binders.push({ name, type: mkHole(`${name}_type`, mkProp()), startToken: binderStartToken });
        ctx = [name, ...ctx];
      } else {
        break;
      }
    }

    if (binders.length === 0) {
      throw new ParseError('Expected at least one binder after λ', this.current().line, this.current().col);
    }

    // Expect =>, then consume it
    if (this.current().type === 'FATARROW') {
      this.advance();
    } else {
      throw new ParseError(
        `Expected '=>' after lambda binders, got ${this.current().type}`,
        this.current().line,
        this.current().col
      );
    }

    // Build the path to the innermost body
    // For \x y => body, the body is at path.body.body
    let bodyPath = path;
    for (let i = 0; i < binders.length; i++) {
      bodyPath = [...bodyPath, { kind: 'field' as const, name: 'body' }];
    }

    // Parse body with the innermost body path
    const body = this.expr(0, ctx, bodyPath);

    // Build nested lambdas from right to left, recording positions
    let result = body;
    let currentPath = bodyPath;

    for (let i = binders.length - 1; i >= 0; i--) {
      result = mkLambda(binders[i].type, result, binders[i].name);

      // Move path up one level (remove the last .body)
      currentPath = currentPath.slice(0, -1);

      // Record the lambda at this path
      if (currentPath.length > 0 || path.length === 0) {
        const endToken = this.tokens[this.pos - 1];
        this.recordRange(currentPath.length > 0 ? currentPath : path, binders[i].startToken, endToken);
      }
    }

    // Record the full lambda expression
    if (path.length > 0) {
      const endToken = this.tokens[this.pos - 1];
      this.recordRange(path, startToken, endToken);
    }

    return result;
  }

  // parsePi removed - use (x : T) -> ... syntax instead

  /**
   * Parse let: let x : T := val in body
   */
  private parseLet(ctx: NameContext, path: IndexPath = []): TTerm {
    const startToken = this.current();
    this.expect('LET');
    const name = this.current().type === 'UNDERSCORE' ? '_' : this.expect('IDENT').value;
    if (this.current().type === 'UNDERSCORE') this.advance();

    // Type annotation is optional
    let type: TTerm;
    if (this.current().type === 'COLON') {
      this.advance();
      const domainPath = [...path, { kind: 'field' as const, name: 'domain' }];
      type = this.expr(0, ctx, domainPath);
    } else {
      type = mkHole(`${name}_type`, mkProp());
    }

    this.expect('ASSIGN');
    const defValPath = [...path, { kind: 'field' as const, name: 'binderKind' }, { kind: 'field' as const, name: 'defVal' }];
    const value = this.expr(0, ctx, defValPath);
    this.expect('IN');

    const newCtx = [name, ...ctx];
    const bodyPath = [...path, { kind: 'field' as const, name: 'body' }];
    const body = this.expr(0, newCtx, bodyPath);

    // Record full let expression
    if (path.length > 0) {
      const endToken = this.tokens[this.pos - 1];
      this.recordRange(path, startToken, endToken);
    }

    return mkLet(name, type, value, body);
  }

  /**
   * Parse pattern:
   *   Zero              → PCtor("Zero", [])
   *   Succ n            → PCtor("Succ", [PVar("n")])
   *   Succ (Succ m)     → PCtor("Succ", [PCtor("Succ", [PVar("m")])])
   *   _                 → PWild
   *   x                 → PVar("x")
   */
  private parsePattern(): TPattern {
    const token = this.current();

    // Wildcard pattern: _
    if (token.type === 'UNDERSCORE') {
      this.advance();
      return { tag: 'PWild' };
    }

    // Constructor or variable pattern
    if (token.type === 'IDENT') {
      const name = token.value;
      this.advance();

      // Check if this is a constructor application (has arguments in parens)
      if (this.current().type === 'LPAREN') {
        // Parse constructor arguments: Ctor (pat1) (pat2) or Ctor(pat1, pat2)
        const args: TPattern[] = [];

        while (this.current().type === 'LPAREN') {
          this.advance(); // consume '('
          args.push(this.parsePattern());
          this.expect('RPAREN');
        }

        return { tag: 'PCtor', name, args };
      }

      // Check if followed by another pattern (application without parens)
      // e.g., "Succ n" or "Cons x xs"
      if (this.canStartPattern(this.current())) {
        // This is a constructor with arguments (no parens)
        const args: TPattern[] = [];
        while (this.canStartPattern(this.current())) {
          args.push(this.parsePatternAtom());
        }
        return { tag: 'PCtor', name, args };
      }

      // Check if uppercase (constructor) or lowercase (variable)
      // Convention: uppercase = constructor, lowercase = variable
      const isConstructor = name[0] === name[0].toUpperCase();

      if (isConstructor) {
        return { tag: 'PCtor', name, args: [] };
      } else {
        return { tag: 'PVar', name };
      }
    }

    // Parenthesized pattern
    if (token.type === 'LPAREN') {
      this.advance();
      const pattern = this.parsePattern();
      this.expect('RPAREN');
      return pattern;
    }

    throw new ParseError(
      `Expected pattern, got ${token.type} '${token.value}'`,
      token.line,
      token.col
    );
  }

  /**
   * Parse an atomic pattern (for use in constructor arguments)
   */
  private parsePatternAtom(): TPattern {
    const token = this.current();

    if (token.type === 'UNDERSCORE') {
      this.advance();
      return { tag: 'PWild' };
    }

    if (token.type === 'IDENT') {
      const name = token.value;
      this.advance();

      // Atomic patterns are either variables or nullary constructors
      const isConstructor = name[0] === name[0].toUpperCase();
      if (isConstructor) {
        return { tag: 'PCtor', name, args: [] };
      } else {
        return { tag: 'PVar', name };
      }
    }

    if (token.type === 'LPAREN') {
      this.advance();
      const pattern = this.parsePattern();
      this.expect('RPAREN');
      return pattern;
    }

    throw new ParseError(
      `Expected atomic pattern, got ${token.type} '${token.value}'`,
      token.line,
      token.col
    );
  }

  /**
   * Parse an atomic pattern with source position tracking.
   * Records the source range in the source map at the given path.
   */
  private parsePatternAtomWithSource(path: IndexPath): TPattern {
    const startToken = this.current();

    if (startToken.type === 'UNDERSCORE') {
      this.advance();
      this.recordRange(path, startToken, startToken);
      return { tag: 'PWild' };
    }

    if (startToken.type === 'IDENT') {
      const name = startToken.value;
      this.advance();

      // Atomic patterns are either variables or nullary constructors
      const isConstructor = name[0] === name[0].toUpperCase();
      this.recordRange(path, startToken, startToken);
      if (isConstructor) {
        return { tag: 'PCtor', name, args: [] };
      } else {
        return { tag: 'PVar', name };
      }
    }

    if (startToken.type === 'LPAREN') {
      this.advance();
      const pattern = this.parsePatternWithSource(path);
      const endToken = this.current();
      this.expect('RPAREN');
      // Record from '(' to ')' inclusive
      this.recordRange(path, startToken, endToken);
      return pattern;
    }

    throw new ParseError(
      `Expected atomic pattern, got ${startToken.type} '${startToken.value}'`,
      startToken.line,
      startToken.col
    );
  }

  /**
   * Parse a pattern with source position tracking.
   * This handles constructor patterns like "Succ n" or "Cons x xs".
   */
  private parsePatternWithSource(path: IndexPath): TPattern {
    const startToken = this.current();

    // Wildcard pattern: _
    if (startToken.type === 'UNDERSCORE') {
      this.advance();
      this.recordRange(path, startToken, startToken);
      return { tag: 'PWild' };
    }

    // Constructor or variable pattern
    if (startToken.type === 'IDENT') {
      const name = startToken.value;
      this.advance();

      // Check if this is a constructor application (has arguments in parens)
      if (this.current().type === 'LPAREN') {
        // Parse constructor arguments: Ctor (pat1) (pat2) or Ctor(pat1, pat2)
        const args: TPattern[] = [];

        while (this.current().type === 'LPAREN') {
          this.advance(); // consume '('
          const argPath: IndexPath = [...path, { kind: 'field', name: 'args' }, { kind: 'array', index: args.length }];
          args.push(this.parsePatternWithSource(argPath));
          this.expect('RPAREN');
        }

        const endToken = this.tokens[this.pos - 1];
        this.recordRange(path, startToken, endToken);
        return { tag: 'PCtor', name, args };
      }

      // Check if followed by another pattern (application without parens)
      // e.g., "Succ n" or "Cons x xs"
      if (this.canStartPattern(this.current())) {
        // Record the constructor name itself at path.name
        const namePath: IndexPath = [...path, { kind: 'field', name: 'name' }];
        this.recordRange(namePath, startToken, startToken);

        // This is a constructor with arguments (no parens)
        const args: TPattern[] = [];
        while (this.canStartPattern(this.current())) {
          const argPath: IndexPath = [...path, { kind: 'field', name: 'args' }, { kind: 'array', index: args.length }];
          args.push(this.parsePatternAtomWithSource(argPath));
        }
        const endToken = this.tokens[this.pos - 1];
        this.recordRange(path, startToken, endToken);
        return { tag: 'PCtor', name, args };
      }

      // Check if uppercase (constructor) or lowercase (variable)
      // Convention: uppercase = constructor, lowercase = variable
      const isConstructor = name[0] === name[0].toUpperCase();

      this.recordRange(path, startToken, startToken);
      if (isConstructor) {
        return { tag: 'PCtor', name, args: [] };
      } else {
        return { tag: 'PVar', name };
      }
    }

    // Parenthesized pattern
    if (startToken.type === 'LPAREN') {
      this.advance();
      const pattern = this.parsePatternWithSource(path);
      const endToken = this.current();
      this.expect('RPAREN');
      this.recordRange(path, startToken, endToken);
      return pattern;
    }

    throw new ParseError(
      `Expected pattern, got ${startToken.type} '${startToken.value}'`,
      startToken.line,
      startToken.col
    );
  }

  /**
   * Check if token can start a pattern
   */
  private canStartPattern(token: Token): boolean {
    return token.type === 'IDENT' ||
           token.type === 'UNDERSCORE' ||
           token.type === 'LPAREN';
  }

  /**
   * Parse match/case expression:
   *
   * Syntax 1 (case with where):
   *   case n where
   *     | Zero => body1
   *     | Succ m => body2
   *
   * Syntax 2 (match with):
   *   match n with
   *     | Zero => body1
   *     | Succ m => body2
   *
   * For now, we use 'case' with 'where' to avoid conflicts with 'with' keyword
   */
  private parseMatch(ctx: NameContext, path: IndexPath = []): TTerm {
    const startToken = this.current();

    // Consume 'case' or 'match'
    const keyword = this.current().value;
    this.advance();

    // Parse scrutinee
    const scrutineePath = [...path, { kind: 'field' as const, name: 'scrutinee' }];
    const scrutinee = this.expr(0, ctx, scrutineePath);

    // Expect 'where' (for case) or 'with' (for match, not yet supported)
    if (this.current().type === 'WHERE') {
      this.advance();
    } else {
      throw new ParseError(
        `Expected 'where' after ${keyword} scrutinee`,
        this.current().line,
        this.current().col
      );
    }

    // Skip newlines before clauses
    this.skipNewlines();

    // Parse clauses
    const clauses: TClause[] = [];

    let clauseIndex = 0;
    while (this.current().type === 'PIPE' || this.canStartPattern(this.current())) {
      // Optional pipe
      if (this.current().type === 'PIPE') {
        this.advance();
      }

      // Parse patterns (for now, just one pattern per clause)
      const pattern = this.parsePattern();

      // Expect '=>'
      this.expect('FATARROW');

      // Parse RHS in a context where pattern variables are bound
      // For now, we'll use a simplified approach: collect pattern vars and add to context
      const patternVars = this.collectPatternVars(pattern);
      const rhsCtx = [...patternVars, ...ctx];
      const rhsPath = [...path, { kind: 'field' as const, name: 'clauses' }, { kind: 'array' as const, index: clauseIndex }, { kind: 'field' as const, name: 'rhs' }];
      const rhs = this.expr(0, rhsCtx, rhsPath);

      clauses.push({
        patterns: [pattern],
        rhs
      });

      clauseIndex++;

      // Skip newlines between clauses
      this.skipNewlines();

      // Stop if we hit something that can't start a clause
      if (this.current().type !== 'PIPE' && !this.canStartPattern(this.current())) {
        break;
      }
    }

    if (clauses.length === 0) {
      throw new ParseError(
        'Expected at least one clause in case expression',
        this.current().line,
        this.current().col
      );
    }

    // Record full match expression
    if (path.length > 0) {
      const endToken = this.tokens[this.pos - 1];
      this.recordRange(path, startToken, endToken);
    }

    return {
      tag: 'Match',
      scrutinee,
      clauses
    };
  }

  /**
   * Collect all variable names bound by a pattern (in left-to-right, depth-first order).
   *
   * IMPORTANT: Wildcards also bind a variable named '_' to match the type-checker's
   * behavior. This ensures De Bruijn indices in the RHS correctly reference pattern
   * positions, even when wildcards are present.
   *
   * For example, in `head _ default (Nil _) = default`:
   * - Pattern 1: `_` → binds `_`
   * - Pattern 2: `default` → binds `default`
   * - Pattern 3: `(Nil _)` → the inner `_` binds `_`
   * So the context is ['_', 'default', '_'], and `default` in the RHS is Var(1).
   */
  private collectPatternVars(pattern: TPattern): string[] {
    switch (pattern.tag) {
      case 'PVar':
        return [pattern.name];
      case 'PCtor':
        // For no-arg patterns that might be type variables (uppercase single letters
        // like A, B, T), we need to bind them. But for actual constructors like Zero,
        // we shouldn't bind them.
        //
        // Heuristic: single uppercase letters are likely type variables.
        // Multi-character uppercase names are likely constructors.
        // This isn't perfect but handles common cases.
        if (pattern.args.length === 0) {
          const name = pattern.name;
          const isSingleUppercase = name.length === 1 && name === name.toUpperCase();
          if (isSingleUppercase) {
            return [name];
          }
          // Multi-character or lowercase: don't bind (it's a constructor)
          return [];
        }
        // For constructors with arguments, collect from all arguments left to right
        return pattern.args.flatMap(arg => this.collectPatternVars(arg));
      case 'PWild':
        // Wildcards bind a variable named '_' for De Bruijn index consistency
        return ['_'];
    }
  }

  /**
   * Parse Type or Type n
   *
   * Syntax:
   * - Type      → Sort(1)
   * - Type 0    → Sort(1)  (Type 0 = Type)
   * - Type 1    → Sort(2)
   * - Type n    → Sort(n+1) for any literal integer n
   *
   * Note: Type_n syntax is handled in the lexer, which recognizes
   * Type_0, Type_1, etc. as TYPE tokens with level information.
   */
  private parseType(path: IndexPath = []): TTerm {
    const startToken = this.current();
    const typeToken = this.expect('TYPE');

    let result: TTerm;

    // Check if the TYPE token has a level suffix (from Type_n in lexer)
    // The lexer stores this in the token value as "Type_n"
    if (typeToken.value.startsWith('Type_')) {
      const levelStr = typeToken.value.substring(5);
      const level = parseInt(levelStr, 10);
      if (!isNaN(level)) {
        result = mkType(level + 1);  // Type_n = Sort(n+1)
      } else {
        result = mkType(1);
      }
    } else if (this.current().type === 'NUMBER') {
      // Check for "Type n" syntax (space followed by number)
      const level = parseInt(this.current().value, 10);
      this.advance();
      result = mkType(level + 1);  // Type n = Sort(n+1)
    } else {
      // Just "Type" means Sort(1)
      result = mkType(1);
    }

    // Record position for Type
    if (path.length > 0) {
      const endToken = this.tokens[this.pos - 1];
      this.recordRange(path, startToken, endToken);
    }

    return result;
  }

  /**
   * Parse identifier (variable or constant reference)
   */
  private parseIdent(ctx: NameContext, path: IndexPath = []): TTerm {
    const startToken = this.current();
    const token = this.expect('IDENT');
    const name = token.value;

    // Record source range for this identifier (from start to end of the token)
    if (path.length > 0) {
      const startPos = createSourcePos(startToken.line, startToken.col, startToken.pos);
      // End position is after the token
      const endCol = startToken.col + startToken.value.length;
      const endCharPos = startToken.pos + startToken.value.length;
      const endPos = createSourcePos(startToken.line, endCol, endCharPos);
      const range = createSourceRange(startPos, endPos);
      const key = serializeIndexPath(path);
      this.currentSourceMap.set(key, range);
    }

    // Look up in context for De Bruijn index
    const idx = ctx.indexOf(name);
    if (idx >= 0) {
      return mkVar(idx);
    }

    // Not in context - treat as constant
    return mkConst(name, mkHole(`${name}_type`, mkProp()));
  }

  /**
   * Parse a number literal - returns a Nat-like constant
   */
  private parseNumberLiteral(value: string): TTerm {
    // For now, represent numbers as constants
    // In a full implementation, we'd build Nat.succ chains
    return mkConst(value, mkConst('ℕ', mkType(0)));
  }

  /**
   * Check if a token can start an atom (for application detection)
   */
  private canStartAtom(token: Token): boolean {
    return token.type === 'LPAREN' ||
      token.type === 'IDENT' ||
      token.type === 'HOLE' ||
      token.type === 'TYPE' ||
      token.type === 'PROP' ||
      token.type === 'NUMBER' ||
      token.type === 'UNDERSCORE';
  }

  // ============================================================================
  // Token Helpers
  // ============================================================================

  private current(): Token {
    return this.tokens[this.pos] || { type: 'EOF', value: '', pos: -1, line: -1, col: -1 };
  }

  private advance(): Token {
    const token = this.current();
    this.pos++;
    return token;
  }

  private expect(type: TokenType): Token {
    const token = this.current();
    if (token.type !== type) {
      throw new ParseError(
        `Expected ${type} but got ${token.type} '${token.value}'`,
        token.line,
        token.col
      );
    }
    return this.advance();
  }

  // ============================================================================
  // Source Position Tracking Helpers
  // ============================================================================

  /**
   * Record a source range for the given index path.
   *
   * @param path - The index path identifying the AST node
   * @param start - The starting token
   * @param end - The ending token (exclusive)
   */
  private recordRange(path: IndexPath, start: Token, end: Token): void {
    const startPos = createSourcePos(start.line, start.col, start.pos);
    // End position is AFTER the end token (exclusive), so add the token's length
    const endCol = end.col + end.value.length;
    const endCharPos = end.pos + end.value.length;
    const endPos = createSourcePos(end.line, endCol, endCharPos);
    const range = createSourceRange(startPos, endPos);
    const key = serializeIndexPath(path);
    this.currentSourceMap.set(key, range);
  }

  /**
   * Get the current token's position.
   */
  private getCurrentPos(): SourcePos {
    const token = this.current();
    return createSourcePos(token.line, token.col, token.pos);
  }

  /**
   * Get the position just after the previous token.
   * This is useful for recording the end position of a parsed construct.
   */
  private getPrevEndPos(): SourcePos {
    if (this.pos === 0) {
      return createSourcePos(1, 1, 0);
    }
    const prevToken = this.tokens[this.pos - 1];
    // End position is after the token, so add its length
    const endCol = prevToken.col + prevToken.value.length;
    const endPos = prevToken.pos + prevToken.value.length;
    return createSourcePos(prevToken.line, endCol, endPos);
  }
}

// ============================================================================
// Convenience Functions
// ============================================================================

/**
 * Parse a single expression with default operators.
 */
export function parseExpr(source: string, operators?: Record<string, OperatorInfo>): TTerm {
  const parser = new Parser(operators);
  return parser.parseExpr(source);
}

/**
 * Parse multiple declarations with default operators.
 */
export function parseDeclarations(source: string, operators?: Record<string, OperatorInfo>): ParsedDeclaration[] {
  const parser = new Parser(operators);
  return parser.parseDeclarations(source);
}

/**
 * Tokenize source code (for debugging).
 */
export function tokenize(source: string, operators?: Record<string, OperatorInfo>): Token[] {
  const lexer = new Lexer(source, operators);
  return lexer.tokenize();
}

