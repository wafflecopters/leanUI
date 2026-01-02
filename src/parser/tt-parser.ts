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

import { TTerm, mkVar, mkPi, mkLambda, mkLet, mkApp, mkConst, mkHole, mkProp, mkType } from '../types/tt-core';

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
  | 'PIPE';        // |

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
 * Pratt parser for the TT language.
 */
export class Parser {
  private tokens: Token[] = [];
  private pos = 0;

  constructor(
    private operators: Record<string, OperatorInfo> = DEFAULT_OPERATORS
  ) { }

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
        const decl = this.parseDeclaration();
        if (decl) {
          // Check if this declaration can be merged with the previous one
          // Merge if: previous has type but no value, current has same name and value but no type
          const prev = declarations[declarations.length - 1];
          if (prev &&
              prev.name &&
              decl.name === prev.name &&
              prev.type && !prev.value &&
              decl.value && !decl.type) {
            // Merge: add value to previous declaration
            prev.value = decl.value;
          } else {
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

  private parseDeclaration(): ParsedDeclaration | null {
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
      return this.parseNamedDeclaration();
    }

    // Otherwise it's a bare expression
    const expr = this.expr(0, []);
    return { kind: 'expr', value: expr };
  }

  /**
   * Parse new-style declaration:
   * - name : type (type signature only)
   * - name = impl (definition only, type will be inferred - only at line start)
   * 
   * For same-line type+definition, use := to avoid ambiguity with equality type:
   * - name : type := impl
   */
  private parseNamedDeclaration(): ParsedDeclaration {
    const nameToken = this.expect('IDENT');
    const name = nameToken.value;

    // Check what follows the name
    const next = this.current();

    // name : type
    if (next.type === 'COLON') {
      this.advance(); // consume ':'
      // Parse the full type expression (including = as equality operator)
      const type = this.expr(0, []);

      // Only := works for same-line definition (to avoid ambiguity with = in types)
      if (this.current().type === 'ASSIGN') {
        this.advance(); // consume ':='
        const value = this.expr(0, []);
        return { kind: 'def', name, type, value };
      }

      // Type signature only
      return { kind: 'def', name, type };
    }

    // name = impl (definition at line start, without type annotation)
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

    // Not a declaration pattern, backtrack and parse as expression
    this.pos--; // backtrack to before the identifier
    const expr = this.expr(0, []);
    return { kind: 'expr', value: expr };
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
    const type = this.expr(0, []);

    // Optional 'where' keyword
    if (this.current().type === 'WHERE') {
      this.advance();
    }

    // Skip newlines before constructors
    this.skipNewlines();

    // Parse constructors
    const constructors: Array<{ name: string; type: TTerm }> = [];

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
      const ctorType = this.expr(0, []);

      constructors.push({ name: ctorName, type: ctorType });

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
   * Main Pratt parser expression handler.
   * @param minPrec Minimum precedence to continue parsing
   * @param ctx Name context for De Bruijn index resolution
   */
  private expr(minPrec: number, ctx: NameContext): TTerm {
    let left = this.parsePrefix(ctx);

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
        const right = this.expr(ARROW_PRECEDENCE, arrowCtx);
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

        const right = this.expr(rightPrec, ctx);

        // Create binary application: op left right
        const opConst = mkConst(opInfo.constName || token.value, mkHole('op_type', mkProp()));
        left = mkApp(mkApp(opConst, left), right);
        continue;
      }

      // Check for application (juxtaposition)
      if (this.canStartAtom(token)) {
        if (APPLICATION_PRECEDENCE < minPrec) break;
        const arg = this.parsePrefix(ctx);
        left = mkApp(left, arg);
        continue;
      }

      break;
    }

    return left;
  }

  /**
   * Parse prefix expressions and atoms.
   */
  private parsePrefix(ctx: NameContext): TTerm {
    const token = this.current();

    switch (token.type) {
      case 'LPAREN':
        return this.parseParenExpr(ctx);

      case 'LAMBDA':
        return this.parseLambda(ctx);

      // PI token removed - use (x : T) -> ... syntax instead

      case 'LET':
        return this.parseLet(ctx);

      case 'TYPE':
        return this.parseType();

      case 'PROP':
        this.advance();
        return mkProp();

      case 'HOLE':
        this.advance();
        return mkHole(token.value, mkHole('hole_type', mkProp()));

      case 'IDENT':
        return this.parseIdent(ctx);

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
  private parseParenExpr(ctx: NameContext): TTerm {
    this.expect('LPAREN');

    // Check if this is a binder: (x : T)
    const startPos = this.pos;

    if (this.current().type === 'IDENT' || this.current().type === 'UNDERSCORE') {
      const nameToken = this.current();
      this.advance();

      if (this.current().type === 'COLON') {
        // This is (x : T) - could be annotation or Pi binder
        this.advance();
        const type = this.expr(0, ctx);
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
    const expr = this.expr(0, ctx);

    // Check for type annotation
    if (this.current().type === 'COLON') {
      this.advance();
      const type = this.expr(0, ctx);
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
  private parseLambda(ctx: NameContext): TTerm {
    this.expect('LAMBDA');

    // Parse binders until we see =>
    const binders: Array<{ name: string; type: TTerm }> = [];

    while (true) {
      const current = this.current();

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
        const type = this.expr(0, ctx);
        this.expect('RPAREN');

        // Add all names with the same type
        for (const name of names) {
          binders.push({ name, type });
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

        binders.push({ name, type: mkHole(`${name}_type`, mkProp()) });
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

    // Parse body
    const body = this.expr(0, ctx);

    // Build nested lambdas from right to left
    let result = body;
    for (let i = binders.length - 1; i >= 0; i--) {
      result = mkLambda(binders[i].type, result, binders[i].name);
    }

    return result;
  }

  // parsePi removed - use (x : T) -> ... syntax instead

  /**
   * Parse let: let x : T := val in body
   */
  private parseLet(ctx: NameContext): TTerm {
    this.expect('LET');
    const name = this.current().type === 'UNDERSCORE' ? '_' : this.expect('IDENT').value;
    if (this.current().type === 'UNDERSCORE') this.advance();

    // Type annotation is optional
    let type: TTerm;
    if (this.current().type === 'COLON') {
      this.advance();
      type = this.expr(0, ctx);
    } else {
      type = mkHole(`${name}_type`, mkProp());
    }

    this.expect('ASSIGN');
    const value = this.expr(0, ctx);
    this.expect('IN');

    const newCtx = [name, ...ctx];
    const body = this.expr(0, newCtx);

    return mkLet(name, type, value, body);
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
  private parseType(): TTerm {
    const typeToken = this.expect('TYPE');

    // Check if the TYPE token has a level suffix (from Type_n in lexer)
    // The lexer stores this in the token value as "Type_n"
    if (typeToken.value.startsWith('Type_')) {
      const levelStr = typeToken.value.substring(5);
      const level = parseInt(levelStr, 10);
      if (!isNaN(level)) {
        return mkType(level + 1);  // Type_n = Sort(n+1)
      }
    }

    // Check for "Type n" syntax (space followed by number)
    if (this.current().type === 'NUMBER') {
      const level = parseInt(this.current().value, 10);
      this.advance();
      return mkType(level + 1);  // Type n = Sort(n+1)
    }

    // Just "Type" means Sort(1)
    return mkType(1);
  }

  /**
   * Parse identifier (variable or constant reference)
   */
  private parseIdent(ctx: NameContext): TTerm {
    const token = this.expect('IDENT');
    const name = token.value;

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

