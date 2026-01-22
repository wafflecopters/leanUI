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
 * - Let: let x = val in body  or  let x : T = val in body  or  let (x : T) = val in body
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
 */

import { TTerm, mkVarTT, mkPiTT, mkLambdaTT, mkLetTT, mkAppTT, mkConstTT, mkHoleTT, mkPropTT, mkTypeTT, mkSortTT, mkULevelTT, TPattern, TClause, TLevel, mkLNumTT, mkLNameTT, mkLSuccTT, mkLMaxTT, mkLIMaxTT } from '../compiler/surface';
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
  | 'ULEVEL'       // ULevel - the type of universe levels
  | 'USUCC'        // USucc - successor of universe level
  | 'UMAX'         // UMax - maximum of two universe levels
  | 'UIMAX'        // UIMax - impredicative max of two universe levels
  | 'UNDERSCORE'   // _
  | 'OPERATOR'     // infix/prefix operators
  | 'EOF'          // end of input
  | 'NEWLINE'      // newline (for separating declarations)
  | 'SEMICOLON'    // ;
  | 'INDUCTIVE'    // inductive keyword
  | 'WHERE'        // where keyword
  | 'PIPE'         // |
  | 'CASE'         // case keyword
  | 'MATCH'        // match keyword
  | 'ABSURD';      // #absurd marker for absurd cases

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
// Grammar: Prefix Parselets
// ============================================================================

/**
 * Prefix parselet - handles tokens that can start an expression.
 *
 * Grammar (prefix expressions):
 *   atom ::= '(' expr ')'              -- grouping / annotation / pi binder
 *          | '\' binder+ '=>' expr     -- lambda
 *          | 'let' IDENT ... 'in' expr -- let binding
 *          | 'case' expr 'where' ...   -- pattern match
 *          | 'Type' NUMBER?            -- type universe
 *          | 'Prop'                    -- prop universe
 *          | '?' IDENT?                -- hole
 *          | IDENT                     -- variable / constant
 *          | NUMBER                    -- numeric literal
 *          | '_'                       -- wildcard hole
 */
type PrefixParselet = (parser: Parser, token: Token, ctx: NameContext, path: IndexPath) => TTerm;

/**
 * Registry of prefix parselets indexed by token type.
 * Each entry defines how to parse an expression starting with that token.
 */
const PREFIX_PARSELETS: Partial<Record<TokenType, PrefixParselet>> = {
  'LPAREN': (p, _t, ctx, path) => p['parseParenExpr'](ctx, path),
  'LBRACE': (p, _t, ctx, path) => p['parseBraceExpr'](ctx, path),
  'LAMBDA': (p, _t, ctx, path) => p['parseLambda'](ctx, path),
  'LET': (p, _t, ctx, path) => p['parseLet'](ctx, path),
  'CASE': (p, _t, ctx, path) => p['parseMatch'](ctx, path),
  'MATCH': (p, _t, ctx, path) => p['parseMatch'](ctx, path),
  'TYPE': (p, _t, _ctx, path) => p['parseType'](path),
  'IDENT': (p, _t, ctx, path) => p['parseIdent'](ctx, path),

  // Simple tokens that don't need helper methods
  'PROP': (p) => {
    p['advance']();
    return mkPropTT();
  },
  // ULevel is the type of universe levels
  'ULEVEL': (p) => {
    p['advance']();
    return mkULevelTT();
  },
  'HOLE': (p, t, _ctx, path) => {
    p['advance']();
    // Record source position for the hole (add 1 for the '?' prefix not in token.value)
    p['recordTokenSourcePositionWithLength'](t, path, t.value.length + 1);
    return mkHoleTT(t.value, mkHoleTT('hole_type', mkPropTT()));
  },
  'NUMBER': (p, t) => {
    p['advance']();
    return p['parseNumberLiteral'](t.value);
  },
  'UNDERSCORE': (p, t, _ctx, path) => {
    p['advance']();
    // Record source position for the underscore
    p['recordTokenSourcePosition'](t, path);
    return mkHoleTT('_', mkHoleTT('underscore_type', mkPropTT()));
  },
  'ABSURD': (p, t, _ctx, path) => {
    p['advance']();
    // Record source position for the absurd marker
    p['recordTokenSourcePosition'](t, path);
    return { tag: 'AbsurdMarker' } as TTerm;
  },
};

/**
 * Set of token types that can start an atom (prefix expression).
 * Derived from PREFIX_PARSELETS for consistency.
 */
const ATOM_STARTER_TOKENS: Set<TokenType> = new Set(
  Object.keys(PREFIX_PARSELETS) as TokenType[]
);

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

    // Absurd marker: #absurd
    if (ch === '#') {
      this.pos++; this.col++;
      const name = this.readWhile(c => this.isIdentChar(c));
      if (name === 'absurd') {
        return { type: 'ABSURD', value: '#absurd', pos: startPos, line: startLine, col: startCol };
      }
      // Unknown # syntax - error (for now, treat as unknown token)
      throw new Error(`Unknown syntax: #${name} at line ${startLine}, column ${startCol}`);
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
        case 'ULevel':
          return { type: 'ULEVEL', value: 'ULevel', pos: startPos, line: startLine, col: startCol };
        case 'USucc':
          return { type: 'USUCC', value: 'USucc', pos: startPos, line: startLine, col: startCol };
        case 'UMax':
          return { type: 'UMAX', value: 'UMax', pos: startPos, line: startLine, col: startCol };
        case 'UIMax':
          return { type: 'UIMAX', value: 'UIMax', pos: startPos, line: startLine, col: startCol };
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
  kind: 'def' | 'expr' | 'inductive';
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
            // BUT preserve the original 'name' entry (from type signature line)
            // AND record the clause's term name at a separate path for highlighting
            for (const [key, range] of this.currentSourceMap) {
              if (key === 'name') {
                if (prev.sourceMap.has('name')) {
                  // Record the term name on this clause line at value.clauses[0].defName
                  prev.sourceMap.set('value.clauses[0].defName', range);
                  continue; // Keep the original declaration name location
                }
              }
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
              if (key === 'name') {
                // Record the term name on this clause line at value.clauses[N].defName
                prev.sourceMap.set(`value.clauses[${newClauseIndex}].defName`, range);
                continue; // Don't overwrite the declaration name from the first line
              }
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

    // Named declaration: name : type  or  name = impl
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

    // Record source range for the term name
    const namePath: IndexPath = [{ kind: 'field', name: 'name' }];
    this.recordRange(namePath, nameToken, nameToken);

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
      const valuePath: IndexPath = [{ kind: 'field', name: 'value' }];
      const value = this.expr(0, [], valuePath);
      return { kind: 'def', name, value };
    }

    // name := impl (definition without type annotation, using :=)
    if (next.type === 'ASSIGN') {
      this.advance(); // consume ':='
      const valuePath: IndexPath = [{ kind: 'field', name: 'value' }];
      const value = this.expr(0, [], valuePath);
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
        scrutinee: mkHoleTT('_scrutinee', mkHoleTT('_scrutinee_type', mkPropTT())),
        clauses: [{
          patterns,
          rhs
        }]
      }
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

    // Record source range for the inductive type name
    const namePath: IndexPath = [{ kind: 'field', name: 'name' }];
    this.recordRange(namePath, nameToken, nameToken);

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

      const ctorNameToken = this.expect('IDENT');
      const ctorName = ctorNameToken.value;

      // Record source range for the constructor name: constructors[ctorIndex].name
      const ctorNamePath: IndexPath = [
        { kind: 'field', name: 'constructors' },
        { kind: 'array', index: ctorIndex },
        { kind: 'field', name: 'name' }
      ];
      this.recordRange(ctorNamePath, ctorNameToken, ctorNameToken);

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
        left = mkPiTT(left, right, '_');
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

        const opConst = mkConstTT(opInfo.constName || token.value);
        left = mkAppTT(mkAppTT(opConst, left), right);
        continue;
      }

      // Check for named argument application: { name := value }
      if (token.type === 'LBRACE') {
        const lookAhead = this.peekNamedArgOrBinder();
        if (lookAhead === 'named-arg') {
          if (APPLICATION_PRECEDENCE < minPrec) break;

          if (path.length > 0 && this.pos > 0) {
            const prevToken = this.tokens[this.pos - 1];
            this.recordRange(path, startToken, prevToken);
          }
          this.prefixSourceMapPaths(path, { kind: 'field', name: 'fn' });

          const { name: argName, value: argValue } = this.parseNamedArgument(ctx, path);
          left = mkAppTT(left, argValue, argName);
          continue;
        }
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
        left = mkAppTT(left, arg);
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

    // Track whether we've done any infix/application work that extends the expression
    // If we just parse a prefix and break immediately, the prefix already recorded its range
    let didInfixWork = false;

    while (true) {
      const token = this.current();

      // Check for arrow (right-associative, low precedence)
      if (token.type === 'ARROW') {
        if (ARROW_PRECEDENCE < minPrec) break;
        didInfixWork = true;
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
        left = mkPiTT(left, right, '_');
        continue;
      }

      // Check for infix operators
      if (token.type === 'OPERATOR') {
        const opInfo = this.operators[token.value];
        if (!opInfo || opInfo.precedence < minPrec) break;

        didInfixWork = true;
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
        const opConst = mkConstTT(opInfo.constName || token.value);
        left = mkAppTT(mkAppTT(opConst, left), right);
        continue;
      }

      // Check for named argument application: { name := value }
      if (token.type === 'LBRACE') {
        // Look ahead to distinguish { name := value } from { name : Type } ->
        const lookAhead = this.peekNamedArgOrBinder();
        if (lookAhead === 'named-arg') {
          if (APPLICATION_PRECEDENCE < minPrec) break;
          didInfixWork = true;

          // Record range before modifying paths
          if (path.length > 0 && this.pos > 0) {
            const prevToken = this.tokens[this.pos - 1];
            this.recordRange(path, startToken, prevToken);
          }
          this.prefixSourceMapPaths(path, { kind: 'field', name: 'fn' });

          // Parse { name := value }
          const { name: argName, value: argValue } = this.parseNamedArgument(ctx, path);
          left = mkAppTT(left, argValue, argName);
          continue;
        }
        // If it's a named binder, fall through to application handling
        // which will fail appropriately (can't apply to a Pi type)
      }

      // Check for application (juxtaposition)
      if (this.canStartAtom(token)) {
        if (APPLICATION_PRECEDENCE < minPrec) break;

        didInfixWork = true;

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
        left = mkAppTT(left, arg);
        continue;
      }

      break;
    }

    // Record the full expression range for this path - but only if we did infix work
    // If we just parsed a prefix expression (possibly in parens), it already recorded its range
    // and we don't want to overwrite it with the paren range
    if (didInfixWork && path.length > 0 && this.pos > 0) {
      const endToken = this.tokens[this.pos - 1];
      this.recordRange(path, startToken, endToken);
    }

    return left;
  }

  /**
   * Look ahead to determine if { ... } is a named argument ({ name := value })
   * or a named binder ({ name : Type } ->).
   * Returns 'named-arg' or 'named-binder'.
   */
  private peekNamedArgOrBinder(): 'named-arg' | 'named-binder' {
    // Save position
    const savedPos = this.pos;

    // Skip past '{'
    this.advance();

    // Skip identifiers (could be multiple for multi-binder)
    while (this.current().type === 'IDENT' || this.current().type === 'UNDERSCORE') {
      this.advance();
    }

    // Check what follows the identifier(s)
    const nextToken = this.current();
    const result = nextToken.type === 'ASSIGN' ? 'named-arg' : 'named-binder';

    // Restore position
    this.pos = savedPos;
    return result;
  }

  /**
   * Parse a named argument: { name := value }
   * Assumes we're positioned at the opening brace.
   */
  private parseNamedArgument(ctx: NameContext, path: IndexPath): { name: string; value: TTerm } {
    // Record open brace position for syntax highlighting
    const openBraceToken = this.current();
    this.expect('LBRACE');
    const argPath = [...path, { kind: 'field' as const, name: 'arg' }];
    const openBracePath = [...argPath, { kind: 'field' as const, name: 'openBrace' }];
    this.recordRange(openBracePath, openBraceToken, openBraceToken);

    const nameToken = this.current();
    if (nameToken.type !== 'IDENT') {
      throw new ParseError(
        'Expected identifier in named argument',
        nameToken.line,
        nameToken.col
      );
    }
    const name = nameToken.value;
    this.advance();

    this.expect('ASSIGN'); // ':='

    const value = this.expr(0, ctx, argPath);

    // Record close brace position for syntax highlighting
    const closeBraceToken = this.current();
    this.expect('RBRACE');
    const closeBracePath = [...argPath, { kind: 'field' as const, name: 'closeBrace' }];
    this.recordRange(closeBracePath, closeBraceToken, closeBraceToken);

    return { name, value };
  }

  /**
   * Parse prefix expressions and atoms.
   * Uses the PREFIX_PARSELETS table for dispatch.
   */
  private parsePrefix(ctx: NameContext, path: IndexPath = []): TTerm {
    const token = this.current();
    const parselet = PREFIX_PARSELETS[token.type];

    if (parselet) {
      return parselet(this, token, ctx, path);
    }

    throw new ParseError(
      `Unexpected token: ${token.type} '${token.value}'`,
      token.line,
      token.col
    );
  }

  /**
   * Parse parenthesized expression, which could be:
   * - Simple grouping: (expr)
   * - Type annotation: (expr : type)
   * - Pi binder: (x : A) → B
   */
  private parseParenExpr(ctx: NameContext, path: IndexPath = []): TTerm {
    this.expect('LPAREN');

    // Check if this is a binder: (x : T) or (x y z : T) for Pi
    const startPos = this.pos;

    if (this.current().type === 'IDENT' || this.current().type === 'UNDERSCORE') {
      // Collect all names (space-separated) until we see ':'
      const nameTokens: Token[] = [];

      while (this.current().type === 'IDENT' || this.current().type === 'UNDERSCORE') {
        nameTokens.push(this.current());
        this.advance();
      }

      if (this.current().type === 'COLON' && nameTokens.length > 0) {
        // This is (x : T) or (x y : T) - could be annotation or Pi binder
        // For multiple names, it MUST be a Pi, so we need to see '->' after
        // For single name, could be either annotation or Pi

        if (nameTokens.length > 1) {
          // Multiple names - must be a Pi binder: (a b c : T) -> ...
          this.advance(); // consume ':'
          const domainPath = [...path, { kind: 'field' as const, name: 'domain' }];
          const type = this.expr(0, ctx, domainPath);
          this.expect('RPAREN');

          if (this.current().type === 'ARROW') {
            this.advance();
            const names = nameTokens.map(t => t.type === 'UNDERSCORE' ? '_' : t.value);

            // Extend context with all names
            let newCtx = ctx;
            for (const name of names) {
              newCtx = [name, ...newCtx];
            }

            // Parse the body at path.body
            const bodyPath = [...path, { kind: 'field' as const, name: 'body' }];
            const body = this.expr(ARROW_PRECEDENCE, newCtx, bodyPath);

            // Multiple names - use MultiBinder
            return {
              tag: 'MultiBinder',
              names,
              binderKind: { tag: 'BPiTT' },
              domain: type,
              body
            };
          } else {
            // No arrow after multiple identifiers + colon + type + rparen
            // This means it was actually (expr : type) where expr is an application
            // e.g., (f x : T) is the application (f x) annotated with type T
            // Backtrack and parse as regular expression
            this.pos = startPos;
          }
        } else {
          // Single name - could be annotation or Pi binder
          this.advance(); // consume ':'
          const domainPath = [...path, { kind: 'field' as const, name: 'domain' }];
          const type = this.expr(0, ctx, domainPath);
          this.expect('RPAREN');

          // Check if followed by arrow - then it's a Pi type
          if (this.current().type === 'ARROW') {
            this.advance();
            const name = nameTokens[0].type === 'UNDERSCORE' ? '_' : nameTokens[0].value;

            // Extend context with the name
            const newCtx = [name, ...ctx];

            // Parse the body at path.body
            const bodyPath = [...path, { kind: 'field' as const, name: 'body' }];
            const body = this.expr(ARROW_PRECEDENCE, newCtx, bodyPath);

            // Single name - use regular Binder
            const namePath = [...path, { kind: 'field' as const, name: 'name' }];
            this.recordRange(namePath, nameTokens[0], nameTokens[0]);
            return mkPiTT(type, body, name);
          }

          // Otherwise it's a type annotation
          const name = nameTokens[0].type === 'UNDERSCORE' ? '_' : nameTokens[0].value;
          const idx = ctx.indexOf(name);
          const term = idx >= 0 ? mkVarTT(idx) : mkConstTT(name);
          return { tag: 'Annot', term, type };
        }
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
   * Parse brace expression for named binders:
   *   { A : Type } -> B       -- named single binder
   *   { A B : Type } -> B     -- named multi-binder
   *
   * Named binders are used for named arguments that can be passed by name at call sites.
   */
  private parseBraceExpr(ctx: NameContext, path: IndexPath = []): TTerm {
    // Capture the opening brace for syntax highlighting
    const openBraceToken = this.current();
    this.expect('LBRACE');
    const openBracePath = [...path, { kind: 'field' as const, name: 'openBrace' }];
    this.recordRange(openBracePath, openBraceToken, openBraceToken);

    // Collect all names (space-separated) until we see ':'
    const nameTokens: Token[] = [];
    while (this.current().type === 'IDENT' || this.current().type === 'UNDERSCORE') {
      nameTokens.push(this.current());
      this.advance();
    }

    if (nameTokens.length === 0) {
      throw new ParseError(
        'Expected at least one name in named binder',
        this.current().line,
        this.current().col
      );
    }

    this.expect('COLON');
    const domainPath = [...path, { kind: 'field' as const, name: 'domain' }];
    const type = this.expr(0, ctx, domainPath);

    // Capture the closing brace for syntax highlighting
    const closeBraceToken = this.current();
    this.expect('RBRACE');
    const closeBracePath = [...path, { kind: 'field' as const, name: 'closeBrace' }];
    this.recordRange(closeBracePath, closeBraceToken, closeBraceToken);

    // Named binders must be followed by '->'
    if (this.current().type !== 'ARROW') {
      throw new ParseError(
        'Named binder { ... } must be followed by ->',
        this.current().line,
        this.current().col
      );
    }
    this.advance(); // consume '->'

    const names = nameTokens.map(t => t.type === 'UNDERSCORE' ? '_' : t.value);

    // Extend context with all names
    let newCtx = ctx;
    for (const name of names) {
      newCtx = [name, ...newCtx];
    }

    // Parse the body
    const bodyPath = [...path, { kind: 'field' as const, name: 'body' }];
    const body = this.expr(ARROW_PRECEDENCE, newCtx, bodyPath);

    if (names.length === 1) {
      // Single name - use regular Binder with named: true
      const namePath = [...path, { kind: 'field' as const, name: 'name' }];
      this.recordRange(namePath, nameTokens[0], nameTokens[0]);
      return mkPiTT(type, body, names[0], /* named */ true);
    } else {
      // Multiple names - use MultiBinder with named: true
      return {
        tag: 'MultiBinder',
        names,
        binderKind: { tag: 'BPiTT' },
        domain: type,
        body,
        named: true
      };
    }
  }

  /**
   * Parse lambda with new syntax:
   *   \x => body                    -- x's type is a hole
   *   \ x => body                   -- same
   *   \x y => body                  -- multiple untyped binders
   *   \(x : A) => body              -- typed binder
   *   \(x : A) y => body            -- mixed
   *   \(x y : A) => body            -- multiple names with same type (space-separated)
   *   \(x : A) (y : B) => body      -- multiple typed binders
   *
   * NOT allowed: \ x : A => body    -- parens required for typed binders
   */
  private parseLambda(ctx: NameContext, path: IndexPath = []): TTerm {
    const startToken = this.current();
    this.expect('LAMBDA');

    // Parse binder groups until we see =>
    // Each group can be a single untyped name, or a typed group with multiple names
    type BinderGroup =
      | { kind: 'single'; name: string; type: TTerm; nameToken: Token }
      | { kind: 'multi'; names: string[]; type: TTerm; nameTokens: Token[] };
    const groups: BinderGroup[] = [];

    while (true) {
      const current = this.current();

      // Stop if we hit the body separator (only => is allowed)
      if (current.type === 'FATARROW') {
        break;
      }

      if (current.type === 'LPAREN') {
        // Typed binder(s): (x : T) or (x y : T) - space-separated names
        this.advance();

        // Collect names and their tokens until we see ':'
        const nameTokens: Token[] = [];
        while (this.current().type === 'IDENT' || this.current().type === 'UNDERSCORE') {
          nameTokens.push(this.current());
          this.advance();
        }

        if (nameTokens.length === 0) {
          throw new ParseError('Expected at least one name in binder', this.current().line, this.current().col);
        }

        this.expect('COLON');
        // Parse type
        const type = this.expr(0, ctx);
        this.expect('RPAREN');

        const names = nameTokens.map(t => t.type === 'UNDERSCORE' ? '_' : t.value);

        // Extend context with all names
        for (const name of names) {
          ctx = [name, ...ctx];
        }

        if (names.length === 1) {
          groups.push({ kind: 'single', name: names[0], type, nameToken: nameTokens[0] });
        } else {
          groups.push({ kind: 'multi', names, type, nameTokens });
        }
      } else if (current.type === 'IDENT' || current.type === 'UNDERSCORE') {
        // Untyped binder: just a name, type will be a hole
        const nameToken = current;
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

        groups.push({ kind: 'single', name, type: mkHoleTT(`${name}_type`, mkPropTT()), nameToken });
        ctx = [name, ...ctx];
      } else {
        break;
      }
    }

    if (groups.length === 0) {
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

    // Count total number of binders for path calculation
    const totalBinders = groups.reduce(
      (acc, g) => acc + (g.kind === 'single' ? 1 : g.names.length),
      0
    );

    // Build the path to the innermost body
    let bodyPath = path;
    for (let i = 0; i < totalBinders; i++) {
      bodyPath = [...bodyPath, { kind: 'field' as const, name: 'body' }];
    }

    // Parse body with the innermost body path
    const body = this.expr(0, ctx, bodyPath);

    // Build nested lambdas/multi-binders from right to left
    let result: TTerm = body;
    let currentPath = bodyPath;

    for (let i = groups.length - 1; i >= 0; i--) {
      const group = groups[i];

      if (group.kind === 'single') {
        result = mkLambdaTT(group.type, result, group.name);

        // Move path up one level (remove the last .body)
        currentPath = currentPath.slice(0, -1);

        // Record the binder name at this path
        const binderPath = currentPath.length > 0 ? currentPath : path;
        const namePath = [...binderPath, { kind: 'field' as const, name: 'name' }];
        this.recordRange(namePath, group.nameToken, group.nameToken);
      } else {
        // Multi-name group - produce MultiBinder
        result = {
          tag: 'MultiBinder',
          names: group.names,
          binderKind: { tag: 'BLamTT' },
          domain: group.type,
          body: result
        };

        // Move path up by the number of names (remove .body for each)
        for (let j = 0; j < group.names.length; j++) {
          currentPath = currentPath.slice(0, -1);
        }
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
   * Parse let expression.
   *
   * Syntax variants:
   *   let x = val in body           -- no type annotation
   *   let x : T = val in body       -- with type annotation
   *   let (x : T) = val in body     -- parenthesized type annotation
   *   let (x : _) = val in body     -- explicit hole type
   *   let x : _ = val in body       -- explicit hole type
   *
   * When the body follows 'in' on a new line, it must be indented beyond 'let'.
   */
  private parseLet(ctx: NameContext, path: IndexPath = []): TTerm {
    const startToken = this.current();
    // Track the starting column of the line containing 'let' for indentation checking
    // This handles cases like: plus (Succ a) b = let x = ... in\n  x
    // where the body just needs to be more indented than the line start, not the 'let' keyword
    const letLineStartCol = this.getLineStartCol(startToken.line);
    this.expect('LET');

    let name: string;
    let nameToken: Token;
    let type: TTerm | undefined = undefined;

    if (this.current().type === 'LPAREN') {
      // Parenthesized form: let (x : T) = val in body
      this.advance();
      nameToken = this.current();
      name = nameToken.type === 'UNDERSCORE' ? '_' : this.expect('IDENT').value;
      if (nameToken.type === 'UNDERSCORE') this.advance();

      this.expect('COLON');
      const domainPath = [...path, { kind: 'field' as const, name: 'domain' }];
      // Inside parens, can parse full expression including = operator
      type = this.expr(0, ctx, domainPath);
      this.expect('RPAREN');
    } else {
      // Non-parenthesized: let x = val or let x : T = val
      nameToken = this.current();
      name = nameToken.type === 'UNDERSCORE' ? '_' : this.expect('IDENT').value;
      if (nameToken.type === 'UNDERSCORE') this.advance();

      // Optional type annotation
      if (this.current().type === 'COLON') {
        this.advance();
        const domainPath = [...path, { kind: 'field' as const, name: 'domain' }];
        // Parse type with precedence > 50 to stop before '=' operator (precedence 50)
        // This way 'let x : Nat = 5 in x' parses type as 'Nat', not 'Nat = 5'
        type = this.expr(51, ctx, domainPath);
      }
    }

    // Record the binder name's source range
    const namePath = [...path, { kind: 'field' as const, name: 'name' }];
    this.recordRange(namePath, nameToken, nameToken);

    // Expect '=' (as OPERATOR token with value '=')
    if (this.current().type !== 'OPERATOR' || this.current().value !== '=') {
      throw new ParseError(
        `Expected '=' in let expression, got '${this.current().type === 'OPERATOR' ? this.current().value : this.current().type}'`,
        this.current().line,
        this.current().col
      );
    }
    this.advance();

    // Parse the value being bound
    const defValPath = [...path, { kind: 'field' as const, name: 'binderKind' }, { kind: 'field' as const, name: 'defVal' }];
    const value = this.expr(0, ctx, defValPath);

    // Expect 'in'
    this.expect('IN');

    // Handle indentation: if there's a newline after 'in', body must be indented
    if (this.current().type === 'NEWLINE') {
      this.advance(); // consume the newline
      // Skip any additional newlines
      while (this.current().type === 'NEWLINE') {
        this.advance();
      }
      // The body must be indented beyond the start of the line containing 'let'
      if (this.current().col <= letLineStartCol) {
        throw new ParseError(
          `Body of let expression must be indented beyond line start (column ${letLineStartCol}), found at column ${this.current().col}`,
          this.current().line,
          this.current().col
        );
      }
    }

    // Parse body with name in context
    const newCtx = [name, ...ctx];
    const bodyPath = [...path, { kind: 'field' as const, name: 'body' }];
    const body = this.expr(0, newCtx, bodyPath);

    // Record full let expression
    if (path.length > 0) {
      const endToken = this.tokens[this.pos - 1];
      this.recordRange(path, startToken, endToken);
    }

    return mkLetTT(name, type, value, body);
  }

  /**
   * Parse pattern:
   *   Zero              → PCtor("Zero", [])
   *   Succ n            → PCtor("Succ", [PVar("n")])
   *   Succ (Succ m)     → PCtor("Succ", [PCtor("Succ", [PVar("m")])])
   *   _                 → PWild
   *   _ x               → PCtor("_", [PWild]) - will be rejected by elaborator
   *   x                 → PVar("x")
   */
  private parsePattern(): TPattern {
    const token = this.current();

    // Wildcard pattern: _ → PWild (names are generated during elaboration)
    // BUT if _ is followed by arguments, it's treated as a PCtor (which elaboration will reject)
    if (token.type === 'UNDERSCORE') {
      this.advance();

      // Check if followed by another pattern (application without parens)
      if (this.canStartPattern(this.current())) {
        const args: TPattern[] = [];
        while (this.canStartPattern(this.current())) {
          args.push(this.parsePatternAtom());
        }
        return { tag: 'PCtor', name: '_', args };
      }

      return { tag: 'PWild' };
    }

    // Constructor or variable pattern
    if (token.type === 'IDENT') {
      const name = token.value;
      this.advance();

      // Check if followed by pattern arguments (either parenthesized or bare)
      // This handles: "Ctor (arg1) arg2", "Ctor arg1 arg2", "Ctor (arg1) (arg2)", etc.
      if (this.canStartPattern(this.current())) {
        const args: TPattern[] = [];
        while (this.canStartPattern(this.current())) {
          args.push(this.parsePatternAtom());
        }
        return { tag: 'PCtor', name, args };
      }

      // All identifiers are parsed uniformly - elaboration will resolve
      // whether it's a constructor or variable based on context lookup
      return { tag: 'PCtor', name, args: [] };
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

    // Named pattern: {name} or {_}
    if (token.type === 'LBRACE') {
      this.advance();
      const innerToken = this.current();

      if (innerToken.type === 'IDENT') {
        const name = innerToken.value;
        this.advance();
        this.expect('RBRACE');
        return { tag: 'PVar', name, named: true };
      } else if (innerToken.type === 'UNDERSCORE') {
        this.advance();
        this.expect('RBRACE');
        return { tag: 'PWild', named: true };
      } else {
        throw new ParseError(
          'Expected identifier or _ in named pattern',
          innerToken.line,
          innerToken.col
        );
      }
    }

    if (token.type === 'UNDERSCORE') {
      this.advance();
      return { tag: 'PWild' };
    }

    if (token.type === 'IDENT') {
      const name = token.value;
      this.advance();

      // All identifiers are parsed uniformly - elaboration will resolve
      // whether it's a constructor or variable based on context lookup
      return { tag: 'PCtor', name, args: [] };
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

    // Named pattern: {name} or {_}
    if (startToken.type === 'LBRACE') {
      // Record open brace position
      const openBracePath = [...path, { kind: 'field' as const, name: 'openBrace' }];
      this.recordRange(openBracePath, startToken, startToken);
      this.advance();
      const innerToken = this.current();

      if (innerToken.type === 'IDENT') {
        const name = innerToken.value;
        this.advance();
        const endToken = this.current();
        // Record close brace position
        const closeBracePath = [...path, { kind: 'field' as const, name: 'closeBrace' }];
        this.recordRange(closeBracePath, endToken, endToken);
        this.expect('RBRACE');
        this.recordRange(path, startToken, endToken);
        return { tag: 'PVar', name, named: true };
      } else if (innerToken.type === 'UNDERSCORE') {
        this.advance();
        const endToken = this.current();
        // Record close brace position
        const closeBracePath = [...path, { kind: 'field' as const, name: 'closeBrace' }];
        this.recordRange(closeBracePath, endToken, endToken);
        this.expect('RBRACE');
        this.recordRange(path, startToken, endToken);
        return { tag: 'PWild', named: true };
      } else {
        throw new ParseError(
          'Expected identifier or _ in named pattern',
          innerToken.line,
          innerToken.col
        );
      }
    }

    if (startToken.type === 'UNDERSCORE') {
      this.advance();
      this.recordRange(path, startToken, startToken);
      return { tag: 'PWild' };
    }

    if (startToken.type === 'IDENT') {
      const name = startToken.value;
      this.advance();

      // All identifiers are parsed uniformly - elaboration will resolve
      // whether it's a constructor or variable based on context lookup
      this.recordRange(path, startToken, startToken);
      return { tag: 'PCtor', name, args: [] };
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

    // Wildcard pattern: _ → PWild (names are generated during elaboration)
    // BUT if _ is followed by arguments, it's treated as a PCtor (which elaboration will reject)
    if (startToken.type === 'UNDERSCORE') {
      this.advance();

      // Check if followed by another pattern (application without parens)
      // e.g., "_ x" would be PCtor("_", [PWild])
      if (this.canStartPattern(this.current())) {
        // Record the constructor name itself at path.name
        const namePath: IndexPath = [...path, { kind: 'field', name: 'name' }];
        this.recordRange(namePath, startToken, startToken);

        // This is _ with arguments (no parens)
        const args: TPattern[] = [];
        while (this.canStartPattern(this.current())) {
          const argPath: IndexPath = [...path, { kind: 'field', name: 'args' }, { kind: 'array', index: args.length }];
          args.push(this.parsePatternAtomWithSource(argPath));
        }
        const endToken = this.tokens[this.pos - 1];
        this.recordRange(path, startToken, endToken);
        return { tag: 'PCtor', name: '_', args };
      }

      this.recordRange(path, startToken, startToken);
      return { tag: 'PWild' };
    }

    // Constructor or variable pattern
    if (startToken.type === 'IDENT') {
      const name = startToken.value;
      this.advance();

      // Check if followed by pattern arguments (either parenthesized or bare)
      // This handles: "Ctor (arg1) arg2", "Ctor arg1 arg2", "Ctor (arg1) (arg2)", etc.
      if (this.canStartPattern(this.current())) {
        // Record the constructor name itself at path.name
        const namePath: IndexPath = [...path, { kind: 'field', name: 'name' }];
        this.recordRange(namePath, startToken, startToken);

        // Parse all arguments (mixing parenthesized and bare is allowed)
        const args: TPattern[] = [];
        while (this.canStartPattern(this.current())) {
          const argPath: IndexPath = [...path, { kind: 'field', name: 'args' }, { kind: 'array', index: args.length }];
          args.push(this.parsePatternAtomWithSource(argPath));
        }
        const endToken = this.tokens[this.pos - 1];
        this.recordRange(path, startToken, endToken);
        return { tag: 'PCtor', name, args };
      }

      // All identifiers are parsed uniformly - elaboration will resolve
      // whether it's a constructor or variable based on context lookup
      this.recordRange(path, startToken, startToken);
      return { tag: 'PCtor', name, args: [] };
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
      token.type === 'LPAREN' ||
      token.type === 'LBRACE';  // Named patterns: {name} or {_}
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
   * IMPORTANT: Wildcards (PWild) also bind variables to ensure De Bruijn indices in
   * the RHS correctly reference pattern positions. We use placeholder names "_" for
   * wildcards here; actual unique names are generated during elaboration.
   *
   * For example, in `head _ default (Nil _) = default`:
   * - Pattern 1: `_` (PWild) → binds "_"
   * - Pattern 2: `default` → binds `default`
   * - Pattern 3: `(Nil _)` → the inner `_` (PWild) binds "_"
   * So the context is ['_', 'default', '_'], and `default` in the RHS is Var(1).
   */
  private collectPatternVars(pattern: TPattern): string[] {
    switch (pattern.tag) {
      case 'PVar':
        return [pattern.name];
      case 'PWild':
        // Wildcards bind a variable too (for De Bruijn indexing)
        // Use "_" as placeholder; real names generated in elaboration
        return ['_'];
      case 'PCtor':
        // With uniform identifier parsing, all identifiers become PCtor nodes.
        // We need to determine which are variables (should be bound) vs constructors.
        //
        // Heuristic for no-arg PCtor:
        // - Lowercase first letter: variable (e.g., 'a', 'b', 'default')
        // - Single uppercase letter: type variable (e.g., 'A', 'T')
        // - Multi-character starting with uppercase: constructor (e.g., 'Zero', 'Succ')
        if (pattern.args.length === 0) {
          const name = pattern.name;
          const firstChar = name[0];
          const isLowercase = firstChar === firstChar.toLowerCase() && firstChar !== firstChar.toUpperCase();
          const isSingleUppercase = name.length === 1 && firstChar === firstChar.toUpperCase();
          if (isLowercase || isSingleUppercase) {
            return [name];
          }
          // Multi-character uppercase: don't bind (it's a constructor)
          return [];
        }
        // For constructors with arguments, collect from all arguments left to right
        return pattern.args.flatMap(arg => this.collectPatternVars(arg));
    }
  }

  /**
   * Parse Type or Type with level expression
   *
   * Syntax:
   * - Prop           → Sort(LNum(0))
   * - Type           → Sort(LNum(1))
   * - Type 0         → Sort(LNum(1))  (Type 0 = Type)
   * - Type 1         → Sort(LNum(2))
   * - Type n         → Sort(LNum(n+1)) for any literal integer n
   * - Type U         → Sort(LName("U")) for identifier U
   * - Type (expr)    → Sort with level expression (USucc, UMax, UIMax)
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
        result = mkTypeTT(level + 1);  // Type_n = Sort(n+1)
      } else {
        result = mkTypeTT(1);
      }
    } else if (this.current().type === 'NUMBER') {
      // Check for "Type n" syntax (space followed by number)
      const level = parseInt(this.current().value, 10);
      this.advance();
      result = mkTypeTT(level + 1);  // Type n = Sort(n+1)
    } else if (this.current().type === 'IDENT') {
      // Type U - level variable
      const name = this.current().value;
      this.advance();
      result = mkSortTT(mkLNameTT(name));
    } else if (this.current().type === 'LPAREN') {
      // Type (level-expr) - parenthesized level expression
      this.advance(); // consume '('
      const level = this.parseLevelExpr();
      this.expect('RPAREN');
      result = mkSortTT(level);
    } else {
      // Just "Type" means Sort(1)
      result = mkTypeTT(1);
    }

    // Record position for Type
    if (path.length > 0) {
      const endToken = this.tokens[this.pos - 1];
      this.recordRange(path, startToken, endToken);
    }

    return result;
  }

  /**
   * Parse a universe level expression.
   *
   * Syntax:
   * - n           → LNum(n) for numeric literal
   * - U           → LName("U") for identifier
   * - USucc e     → LSucc(e)
   * - UMax e1 e2  → LMax(e1, e2)
   * - UIMax e1 e2 → LIMax(e1, e2)
   * - (expr)      → parenthesized level expression
   */
  private parseLevelExpr(): TLevel {
    const current = this.current();

    if (current.type === 'NUMBER') {
      const n = parseInt(current.value, 10);
      this.advance();
      return mkLNumTT(n);
    }

    if (current.type === 'IDENT') {
      const name = current.value;
      this.advance();
      return mkLNameTT(name);
    }

    if (current.type === 'USUCC') {
      this.advance(); // consume 'USucc'
      const pred = this.parseLevelAtom();
      return mkLSuccTT(pred);
    }

    if (current.type === 'UMAX') {
      this.advance(); // consume 'UMax'
      const left = this.parseLevelAtom();
      const right = this.parseLevelAtom();
      return mkLMaxTT(left, right);
    }

    if (current.type === 'UIMAX') {
      this.advance(); // consume 'UIMax'
      const left = this.parseLevelAtom();
      const right = this.parseLevelAtom();
      return mkLIMaxTT(left, right);
    }

    if (current.type === 'LPAREN') {
      this.advance(); // consume '('
      const level = this.parseLevelExpr();
      this.expect('RPAREN');
      return level;
    }

    throw new ParseError(
      `Expected level expression, got ${current.type} '${current.value}'`,
      current.line,
      current.col
    );
  }

  /**
   * Parse an atomic level expression (for use as argument to USucc, UMax, UIMax).
   * This is either a number, identifier, or parenthesized expression.
   */
  private parseLevelAtom(): TLevel {
    const current = this.current();

    if (current.type === 'NUMBER') {
      const n = parseInt(current.value, 10);
      this.advance();
      return mkLNumTT(n);
    }

    if (current.type === 'IDENT') {
      const name = current.value;
      this.advance();
      return mkLNameTT(name);
    }

    if (current.type === 'LPAREN') {
      this.advance(); // consume '('
      const level = this.parseLevelExpr();
      this.expect('RPAREN');
      return level;
    }

    throw new ParseError(
      `Expected level atom (number, identifier, or parenthesized expression), got ${current.type} '${current.value}'`,
      current.line,
      current.col
    );
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
      return mkVarTT(idx);
    }

    // Not in context - treat as constant
    return mkConstTT(name);
  }

  /**
   * Parse a number literal - returns a Nat-like constant
   */
  private parseNumberLiteral(value: string): TTerm {
    // For now, represent numbers as constants
    // In a full implementation, we'd build Nat.succ chains
    return mkConstTT(value);
  }

  /**
   * Check if a token can start an atom (for application detection).
   * Derived from PREFIX_PARSELETS for consistency.
   */
  private canStartAtom(token: Token): boolean {
    return ATOM_STARTER_TOKENS.has(token.type);
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

  /**
   * Get the column of the first non-NEWLINE token on a given line.
   * Used for indentation checking in let expressions.
   */
  private getLineStartCol(line: number): number {
    for (const token of this.tokens) {
      if (token.line === line && token.type !== 'NEWLINE') {
        return token.col;
      }
    }
    return 0;
  }

  // ============================================================================
  // Source Position Tracking Helpers
  // ============================================================================

  /**
   * Record a source position for a single token at the given path.
   * Used by parselets that handle simple tokens like HOLE and UNDERSCORE.
   */
  private recordTokenSourcePosition(token: Token, path: IndexPath): void {
    this.recordTokenSourcePositionWithLength(token, path, token.value.length);
  }

  /**
   * Record a source position for a token with an explicit length.
   * Useful when the token's value doesn't include prefix characters (e.g., '?' for holes).
   */
  private recordTokenSourcePositionWithLength(token: Token, path: IndexPath, length: number): void {
    if (path.length > 0) {
      const startPos = createSourcePos(token.line, token.col, token.pos);
      const endCol = token.col + length;
      const endCharPos = token.pos + length;
      const endPos = createSourcePos(token.line, endCol, endCharPos);
      const range = createSourceRange(startPos, endPos);
      const key = serializeIndexPath(path);
      this.currentSourceMap.set(key, range);
    }
  }

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

