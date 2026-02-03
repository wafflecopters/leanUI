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

import { TTerm, mkVarTT, mkPiTT, mkLambdaTT, mkLetTT, mkMultiLetTT, mkAppTT, mkConstTT, mkHoleTT, mkPropTT, mkTypeTT, mkSortTT, mkULevelTT, TPattern, TClause, TLetBinding, mkULitTT, mkUOmegaTT, mkUSuccAppTT, mkUMaxAppTT, mkUIMaxAppTT, TNamedPatternArg, TWithClause, TacticCommand, CaseBranch, mkTacticBlockTT } from '../compiler/surface';
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
  | 'UZERO'        // UZero - the zero universe level
  | 'USUCC'        // USucc - successor of universe level
  | 'UMAX'         // UMax - maximum of two universe levels
  | 'UIMAX'        // UIMax - impredicative max of two universe levels
  | 'UNDERSCORE'   // _
  | 'OPERATOR'     // infix/prefix operators
  | 'EOF'          // end of input
  | 'NEWLINE'      // newline (for separating declarations)
  | 'SEMICOLON'    // ;
  | 'INDUCTIVE'    // inductive keyword
  | 'RECORD'       // record keyword
  | 'CONSTRUCTOR'  // constructor keyword (for records)
  | 'EXTENDS'      // extends keyword (for records)
  | 'WHERE'        // where keyword
  | 'PIPE'         // |
  | 'CASE'         // case keyword
  | 'MATCH'        // match keyword
  | 'WITH'         // with keyword (for with-abstraction)
  | 'ELLIPSIS'     // ... (for repeating parent patterns in with clauses)
  | 'ABSURD'       // #absurd marker for absurd cases
  | 'BY';          // by keyword (for tactic proofs)

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
  'TYPE': (p, _t, ctx, path) => p['parseType'](ctx, path),
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
  // UZero is the zero universe level
  'UZERO': (p) => {
    p['advance']();
    return mkULitTT(0);
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

      // Skip directive lines (@assumeK, @test, @name, etc.)
      // Check if we're at start of line (col === 1) or only whitespace before @
      if (ch === '@') {
        const lineStart = this.pos - (this.col - 1);
        const beforeAt = this.input.slice(lineStart, this.pos);
        const onlyWhitespaceOrCommentBefore = /^(\s|--\s*)*$/.test(beforeAt);

        if (onlyWhitespaceOrCommentBefore) {
          // Skip to end of line
          while (this.pos < this.input.length && this.input[this.pos] !== '\n') {
            this.pos++;
          }
          continue;
        }
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
        // Check for ... (ellipsis) first
        if (this.input[this.pos + 1] === '.' && this.input[this.pos + 2] === '.') {
          this.pos += 3; this.col += 3;
          return { type: 'ELLIPSIS', value: '...', pos: startPos, line: startLine, col: startCol };
        }
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
      let ident = this.readWhile(c => this.isIdentChar(c));

      // Check for qualified identifiers (e.g., Point.x, Pair.fst)
      // A qualified identifier is: ident.ident.ident...
      while (this.pos < this.input.length && this.input[this.pos] === '.') {
        // Peek ahead to see if there's an identifier after the dot
        const nextPos = this.pos + 1;
        if (nextPos < this.input.length && this.isIdentStart(this.input[nextPos])) {
          // Consume the dot
          this.pos++;
          this.col++;
          // Consume the next identifier part
          const nextPart = this.readWhile(c => this.isIdentChar(c));
          ident = ident + '.' + nextPart;
        } else {
          // Dot not followed by identifier, don't consume it
          break;
        }
      }

      // Check for keywords (only for non-qualified identifiers)
      if (!ident.includes('.')) {
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
          case 'UZero':
            return { type: 'UZERO', value: 'UZero', pos: startPos, line: startLine, col: startCol };
          case 'USucc':
            return { type: 'USUCC', value: 'USucc', pos: startPos, line: startLine, col: startCol };
          case 'UMax':
            return { type: 'UMAX', value: 'UMax', pos: startPos, line: startLine, col: startCol };
          case 'UIMax':
            return { type: 'UIMAX', value: 'UIMax', pos: startPos, line: startLine, col: startCol };
          case 'inductive':
            return { type: 'INDUCTIVE', value: 'inductive', pos: startPos, line: startLine, col: startCol };
          case 'record':
            return { type: 'RECORD', value: 'record', pos: startPos, line: startLine, col: startCol };
          case 'constructor':
            return { type: 'CONSTRUCTOR', value: 'constructor', pos: startPos, line: startLine, col: startCol };
          case 'extends':
            return { type: 'EXTENDS', value: 'extends', pos: startPos, line: startLine, col: startCol };
          case 'where':
            return { type: 'WHERE', value: 'where', pos: startPos, line: startLine, col: startCol };
          case 'case':
            return { type: 'CASE', value: 'case', pos: startPos, line: startLine, col: startCol };
          case 'match':
            return { type: 'MATCH', value: 'match', pos: startPos, line: startLine, col: startCol };
          case 'with':
            return { type: 'WITH', value: 'with', pos: startPos, line: startLine, col: startCol };
          case 'by':
            return { type: 'BY', value: 'by', pos: startPos, line: startLine, col: startCol };
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

      // Qualified identifier (contains dots) - return as IDENT
      return { type: 'IDENT', value: ident, pos: startPos, line: startLine, col: startCol };
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
    const count = errors.length;
    const summary = `${count} parse error${count !== 1 ? 's' : ''}`;
    // Include first error's message for better error display
    const firstErrorMsg = errors[0] ? `: ${errors[0].message}` : '';
    super(summary + firstErrorMsg);
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
 * A parsed record field (name and type).
 */
export interface ParsedRecordField {
  name: string;
  type: TTerm;
  implicit?: boolean;  // true for implicit fields {name : Type}
}

/**
 * A parsed record parameter (name and type).
 */
export interface ParsedRecordParam {
  name: string;
  type: TTerm;
  implicit?: boolean;  // true for implicit parameters {A : Type}
}

/**
 * Result of parsing a top-level declaration.
 */
export interface ParsedDeclaration {
  kind: 'def' | 'expr' | 'inductive' | 'record';
  name?: string;
  type?: TTerm;
  value?: TTerm;
  // For inductive types
  constructors?: Array<{ name: string; type: TTerm }>;
  // For records
  params?: ParsedRecordParam[];
  fields?: ParsedRecordField[];
  constructorName?: string;  // Optional custom constructor name
  extends?: string[];        // Names of records to extend
  extendsExprs?: TTerm[];    // Full expressions for extends (e.g., Semigroup A)
  // For with-clause auxiliary functions: number of scrutinee pattern positions.
  // Used by totality checker to skip frozen function-pattern positions.
  withScrutineeCount?: number;
  // For with-clause auxiliary functions: the original scrutinee expressions.
  // Used by compile.ts to compute the actual scrutinee types (replacing holes
  // in the auxiliary type signature) before checking clauses.
  withScrutineeExprs?: TTerm[];
  // Original surface value before with-clause desugaring.
  // Used for semantic token extraction (the desugared value loses WithClause structure).
  originalSurfaceValue?: TTerm;
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
  /**
   * Remap source map entries from one prefix to another.
   * All entries starting with oldPrefix are moved to start with newPrefix instead.
   */
  private remapSourceMapPaths(oldPrefix: string, newPrefix: string): void {
    const toAdd: Array<[string, SourceRange]> = [];
    const toDelete: string[] = [];
    for (const [pathStr, range] of this.currentSourceMap) {
      if (pathStr === oldPrefix) {
        toDelete.push(pathStr);
        toAdd.push([newPrefix, range]);
      } else if (pathStr.startsWith(oldPrefix + '.') || pathStr.startsWith(oldPrefix + '[')) {
        toDelete.push(pathStr);
        toAdd.push([newPrefix + pathStr.substring(oldPrefix.length), range]);
      }
    }
    for (const key of toDelete) this.currentSourceMap.delete(key);
    for (const [key, value] of toAdd) this.currentSourceMap.set(key, value);
  }

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

    // Record: record Name (params) [extends ...] where fields
    if (current.type === 'RECORD') {
      return this.parseRecordDeclaration();
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

      // Check for :=
      if (this.current().type === 'ASSIGN') {
        this.advance(); // consume ':='

        // Check if this is a tactic proof (by) or a normal value
        if (this.current().type === 'BY') {
          // name : type := by ...tactics...
          this.advance(); // consume 'by'
          const valuePath: IndexPath = [{ kind: 'field', name: 'value' }];
          const value = this.parseTacticBlock([], valuePath);
          return { kind: 'def', name, type, value };
        }

        // name : type := value (normal definition)
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

      // Check if this is a tactic proof or normal value
      if (this.current().type === 'BY') {
        // name := by ...tactics... (tactic proof without type annotation - unusual but allowed)
        this.advance(); // consume 'by'
        const valuePath: IndexPath = [{ kind: 'field', name: 'value' }];
        const value = this.parseTacticBlock([], valuePath);
        return { kind: 'def', name, value };
      }

      // name := value (normal definition)
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
    // Patterns can be positional or named: {name := pattern}
    const patterns: TPattern[] = [];
    const namedPatterns: Array<{ name: string; pattern: TPattern }> = [];

    let argIndex = 0;
    while (this.canStartPattern(this.current())) {
      const patternPath: IndexPath = [
        ...clausePath,
        { kind: 'field', name: 'patterns' },
        { kind: 'array', index: argIndex }
      ];
      const result = this.parsePatternAtomWithSourceInternal(patternPath);
      if (result.kind === 'namedArg') {
        namedPatterns.push({ name: result.name, pattern: result.pattern });
      } else {
        patterns.push(result.pattern);
      }
      argIndex++;
    }

    if (patterns.length === 0 && namedPatterns.length === 0) {
      throw new ParseError(
        `Expected at least one pattern in pattern clause for '${funcName}'`,
        this.current().line,
        this.current().col
      );
    }

    // Check for 'with' or '='
    if (this.current().type === 'WITH') {
      // Parse with-abstraction: funcName patterns with scrutinee | pat => rhs | pat => rhs ...
      return this.parseWithClause(funcName, patterns, namedPatterns, clausePath, clauseStartPos);
    }

    // Expect '='
    if (this.current().type !== 'OPERATOR' || this.current().value !== '=') {
      throw new ParseError(
        `Expected '=' or 'with' in pattern clause, got ${this.current().type} '${this.current().value}'`,
        this.current().line,
        this.current().col
      );
    }
    this.advance(); // consume '='
    this.skipNewlines(); // Allow RHS to start on next line (e.g., let on newline)

    // Parse RHS with pattern variables bound
    // Pattern vars are collected left-to-right, depth-first. But in De Bruijn,
    // index 0 is the most recently bound variable (the last one collected).
    // So we reverse the list to match the type-checker's context ordering.
    // Note: Named patterns come after positional in the surface order
    const positionalVars = patterns.flatMap(p => this.collectPatternVars(p));
    const namedVars = namedPatterns.flatMap(np => this.collectPatternVars(np.pattern));
    const patternVars = [...positionalVars, ...namedVars];
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
          namedPatterns: namedPatterns.length > 0 ? namedPatterns : undefined,
          rhs
        }]
      }
    };
  }

  /**
   * Parse with-abstraction clause:
   * funcName patterns with scrutinee
   *   | withPat1 => rhs1
   *   | withPat2 => rhs2
   *
   * Following Agda's approach, this will be desugared to an auxiliary function.
   */
  private parseWithClause(
    funcName: string,
    patterns: TPattern[],
    namedPatterns: TNamedPatternArg[],
    clausePath: IndexPath,
    clauseStartPos: SourcePos
  ): ParsedDeclaration {
    this.advance(); // consume 'with'

    // Collect pattern variables for context
    const positionalVars = patterns.flatMap(p => this.collectPatternVars(p));
    const namedVars = namedPatterns.flatMap(np => this.collectPatternVars(np.pattern));
    const patternVars = [...positionalVars, ...namedVars];
    const ctx = [...patternVars].reverse();

    // Parse scrutinee expression(s) - can be comma-separated
    const scrutinees: TTerm[] = [];
    const scrutineePath: IndexPath = [...clausePath, { kind: 'field', name: 'scrutinee' }];
    scrutinees.push(this.expr(0, ctx, scrutineePath));

    while (this.current().type === 'COMMA') {
      this.advance(); // consume ','
      scrutinees.push(this.expr(0, ctx, scrutineePath));
    }

    // Skip newlines before with-clauses
    this.skipNewlines();

    // Parse with-clauses: | pattern => rhs
    const withClauses: TClause[] = [];
    let clauseIndex = 0;

    while (this.current().type === 'PIPE' || this.current().type === 'ELLIPSIS') {
      const withClausePath: IndexPath = [
        ...clausePath,
        { kind: 'field', name: 'withClauses' },
        { kind: 'array', index: clauseIndex }
      ];

      // Check for ellipsis (... | pattern => rhs)
      let hasEllipsis = false;
      if (this.current().type === 'ELLIPSIS') {
        hasEllipsis = true;
        this.advance(); // consume '...'
      }

      // Expect and consume '|'
      const pipeCol = this.current().col;
      if (this.current().type === 'PIPE') {
        this.advance();
      } else if (!hasEllipsis) {
        // If no ellipsis and no pipe, we're done with with-clauses
        break;
      }

      // Parse pattern(s) for this with-clause
      // For multiple scrutinees, patterns are comma-separated
      const withPatterns: TPattern[] = [];
      const withPatternPath: IndexPath = [...withClausePath, { kind: 'field', name: 'patterns' }];

      if (this.canStartPattern(this.current())) {
        const firstPat = this.parsePatternWithSource([...withPatternPath, { kind: 'array', index: 0 }]);
        withPatterns.push(firstPat);

        let patIdx = 1;
        while (this.current().type === 'COMMA' && patIdx < scrutinees.length) {
          this.advance(); // consume ','
          const pat = this.parsePatternWithSource([...withPatternPath, { kind: 'array', index: patIdx }]);
          withPatterns.push(pat);
          patIdx++;
        }
      }

      // Parse RHS: either '=> expr' (normal) or 'with scrutinee | ...' (nested with)
      const withPatternVars = withPatterns.flatMap(p => this.collectPatternVars(p));
      const rhsCtx = [...withPatternVars.reverse(), ...ctx];
      const rhsPath: IndexPath = [...withClausePath, { kind: 'field', name: 'rhs' }];

      let rhs: TTerm;
      if (this.current().type === 'WITH') {
        // Nested with: parse as a new WithClause whose functionPatterns
        // include all accumulated patterns (outer function + this with-pattern)
        const nestedFunctionPatterns = [...patterns, ...withPatterns];
        rhs = this.parseNestedWith(nestedFunctionPatterns, namedPatterns, rhsCtx, rhsPath, pipeCol);
      } else {
        this.expect('FATARROW');
        rhs = this.expr(0, rhsCtx, rhsPath);
      }

      withClauses.push({
        patterns: withPatterns,
        rhs
      });

      clauseIndex++;
      this.skipNewlines();
    }

    // Track the clause in source map
    const clauseEndPos = this.getPrevEndPos();
    const clauseKey = serializeIndexPath(clausePath);
    this.currentSourceMap.set(clauseKey, createSourceRange(clauseStartPos, clauseEndPos));

    // Wrap the WithClause inside a Match so that the parser's clause-merging logic
    // can combine it with other clauses of the same function (regular or with).
    // The desugarer will find the WithClause in the clause RHS and transform it.
    const withClauseExpr: TTerm = {
      tag: 'WithClause',
      functionPatterns: patterns,
      functionNamedPatterns: namedPatterns.length > 0 ? namedPatterns : undefined,
      scrutinees,
      clauses: withClauses
    } as TTerm;

    return {
      kind: 'def',
      name: funcName,
      value: {
        tag: 'Match',
        scrutinee: mkHoleTT('_scrutinee', mkHoleTT('_scrutinee_type', mkPropTT())),
        clauses: [{
          patterns,
          namedPatterns: namedPatterns.length > 0 ? namedPatterns : undefined,
          rhs: withClauseExpr,
        }],
      },
    };
  }

  /**
   * Parse a nested with expression inside a with-branch.
   * Instead of '| pattern => rhs', the branch has '| pattern with scrutinee | ... => ...'
   *
   * Returns a WithClause TTerm whose functionPatterns include ALL accumulated patterns
   * from the enclosing with chain.
   */
  private parseNestedWith(
    functionPatterns: TPattern[],
    namedPatterns: TNamedPatternArg[],
    ctx: string[],
    parentPath: IndexPath,
    outerPipeCol: number,
  ): TTerm {
    this.advance(); // consume 'with'

    // Parse scrutinee(s) in the current context
    const scrutinees: TTerm[] = [];
    const scrutineePath: IndexPath = [...parentPath, { kind: 'field', name: 'scrutinee' }];
    scrutinees.push(this.expr(0, ctx, scrutineePath));
    while (this.current().type === 'COMMA') {
      this.advance();
      scrutinees.push(this.expr(0, ctx, scrutineePath));
    }

    this.skipNewlines();

    // Parse nested with-clauses: | pattern => rhs (or further nested with)
    // Stop when we see a '|' at or left of the outer pipe column (belongs to parent)
    const nestedClauses: TClause[] = [];
    let clauseIndex = 0;

    while ((this.current().type === 'PIPE' || this.current().type === 'ELLIPSIS') && this.current().col > outerPipeCol) {
      const withClausePath: IndexPath = [
        ...parentPath,
        { kind: 'field', name: 'withClauses' },
        { kind: 'array', index: clauseIndex },
      ];

      // Handle ellipsis (...) — syntactic sugar for "repeat parent patterns unchanged"
      if (this.current().type === 'ELLIPSIS') {
        this.advance(); // consume '...'
      }

      const pipeCol = this.current().col;
      if (this.current().type === 'PIPE') {
        this.advance(); // consume '|'
      }

      // Parse pattern(s)
      const withPatterns: TPattern[] = [];
      const withPatternPath: IndexPath = [...withClausePath, { kind: 'field', name: 'patterns' }];
      if (this.canStartPattern(this.current())) {
        withPatterns.push(this.parsePatternWithSource([...withPatternPath, { kind: 'array', index: 0 }]));
        let patIdx = 1;
        while (this.current().type === 'COMMA' && patIdx < scrutinees.length) {
          this.advance();
          withPatterns.push(this.parsePatternWithSource([...withPatternPath, { kind: 'array', index: patIdx }]));
          patIdx++;
        }
      }

      // Parse RHS: either '=> expr' or nested 'with ...'
      const withPatternVars = withPatterns.flatMap(p => this.collectPatternVars(p));
      const rhsCtx = [...withPatternVars.reverse(), ...ctx];
      const rhsPath: IndexPath = [...withClausePath, { kind: 'field', name: 'rhs' }];

      let rhs: TTerm;
      if (this.current().type === 'WITH') {
        // Further nesting
        const nestedFunctionPatterns = [...functionPatterns, ...withPatterns];
        rhs = this.parseNestedWith(nestedFunctionPatterns, namedPatterns, rhsCtx, rhsPath, pipeCol);
      } else {
        this.expect('FATARROW');
        rhs = this.expr(0, rhsCtx, rhsPath);
      }

      nestedClauses.push({ patterns: withPatterns, rhs });
      clauseIndex++;
      this.skipNewlines();
    }

    return {
      tag: 'WithClause',
      functionPatterns,
      functionNamedPatterns: namedPatterns.length > 0 ? namedPatterns : undefined,
      scrutinees,
      clauses: nestedClauses,
    } as TTerm;
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
   * Parse a record declaration:
   *
   * record Name (params) [extends Parent1, Parent2] where
   *   [constructor CtorName]
   *   field1 : Type1
   *   field2 : Type2
   *
   * Parameters can be explicit (A : Type) or implicit {A : Type}.
   * Fields are always explicit in the current syntax.
   */
  private parseRecordDeclaration(): ParsedDeclaration {
    this.expect('RECORD');
    const nameToken = this.expect('IDENT');

    // Record source range for the record type name
    const namePath: IndexPath = [{ kind: 'field', name: 'name' }];
    this.recordRange(namePath, nameToken, nameToken);

    // Parse parameters: (A : Type) or {A : Type} or (A B : Type), can be multiple
    const params: ParsedRecordParam[] = [];
    let paramIndex = 0;

    while (this.current().type === 'LPAREN' || this.current().type === 'LBRACE') {
      const implicit = this.current().type === 'LBRACE';
      this.advance(); // consume ( or {

      // Collect all names (space-separated) until we see ':'
      const nameTokens: Token[] = [];
      while (this.current().type === 'IDENT') {
        nameTokens.push(this.current());
        this.advance();
      }

      if (nameTokens.length === 0) {
        throw new ParseError(
          'Expected at least one parameter name',
          this.current().line,
          this.current().col
        );
      }

      this.expect('COLON');

      // Parse parameter type (shared by all names in this group)
      // Type is in scope of all previous parameters
      // Context is built with most recent first (like lambda), so reverse the order
      const paramCtx = [...params].reverse().map(p => p.name);
      const paramTypePath: IndexPath = [
        { kind: 'field', name: 'params' },
        { kind: 'array', index: paramIndex },
        { kind: 'field', name: 'type' }
      ];
      const paramType = this.expr(0, paramCtx, paramTypePath);

      // Expect closing bracket
      if (implicit) {
        this.expect('RBRACE');
      } else {
        this.expect('RPAREN');
      }

      // Create a param for each name, all sharing the same type
      // The type is parsed once and reused - elaboration handles the context/indices
      for (const nameToken of nameTokens) {
        const paramName = nameToken.value;

        // Record source range for parameter name
        const paramNamePath: IndexPath = [
          { kind: 'field', name: 'params' },
          { kind: 'array', index: paramIndex },
          { kind: 'field', name: 'name' }
        ];
        this.recordRange(paramNamePath, nameToken, nameToken);

        params.push({ name: paramName, type: paramType, implicit: implicit || undefined });
        paramIndex++;
      }
    }

    // Parse optional type annotation: : Type or : Type u or : Prop
    // e.g., record Box (A : Type) : Type where ...
    let recordType: TTerm | undefined;
    if (this.current().type === 'COLON') {
      this.advance(); // consume ':'

      // Parse the record type expression in the context of all parameters
      // Context is built with most recent first (like lambda)
      const typeCtx = [...params].reverse().map(p => p.name);
      const typePath: IndexPath = [{ kind: 'field', name: 'type' }];
      recordType = this.expr(0, typeCtx, typePath);
    }

    // Parse optional extends clause: extends Parent1, Parent2
    // Note: extends can reference bound parameters, e.g., extends Pred α
    let extendsNames: string[] | undefined;
    let extendsExprs: TTerm[] | undefined;
    if (this.current().type === 'EXTENDS') {
      this.advance(); // consume 'extends'
      extendsNames = [];
      extendsExprs = [];

      // Parse comma-separated list of parent expressions
      // Each can be a simple name (Pred) or an application (Pred α)
      // Context is built with most recent first (like lambda)
      const extendsCtx = [...params].reverse().map(p => p.name);
      let extendsIndex = 0;
      do {
        const extendsPath: IndexPath = [
          { kind: 'field', name: 'extends' },
          { kind: 'array', index: extendsIndex }
        ];
        // Parse as an expression to allow applications like "Pred α"
        const parentExpr = this.expr(0, extendsCtx, extendsPath);

        // Extract the base name for backwards compatibility
        let baseName: string;
        if (parentExpr.tag === 'Const') {
          baseName = parentExpr.name;
        } else if (parentExpr.tag === 'App') {
          // Walk to the leftmost function to get the base name
          let fn = parentExpr.fn;
          while (fn.tag === 'App') {
            fn = fn.fn;
          }
          if (fn.tag === 'Const') {
            baseName = fn.name;
          } else {
            throw new ParseError(
              'Expected record name in extends clause',
              this.current().line,
              this.current().col
            );
          }
        } else {
          throw new ParseError(
            'Expected record name in extends clause',
            this.current().line,
            this.current().col
          );
        }

        extendsNames.push(baseName);
        extendsExprs.push(parentExpr);
        extendsIndex++;

        // Check for comma to continue
        if (this.current().type !== 'COMMA') {
          break;
        }
        this.advance(); // consume ','
      } while (true);
    }

    // Skip newlines before 'where'
    this.skipNewlines();

    // Expect 'where' keyword
    this.expect('WHERE');

    // Skip newlines after 'where'
    this.skipNewlines();

    // Parse optional constructor declaration: constructor CtorName
    let constructorName: string | undefined;
    if (this.current().type === 'CONSTRUCTOR') {
      this.advance(); // consume 'constructor'
      const ctorNameToken = this.expect('IDENT');
      constructorName = ctorNameToken.value;

      // Record source range for constructor name
      const ctorNamePath: IndexPath = [{ kind: 'field', name: 'constructorName' }];
      this.recordRange(ctorNamePath, ctorNameToken, ctorNameToken);

      this.skipNewlines();
    }

    // Parse fields: name : type
    const fields: ParsedRecordField[] = [];
    let fieldIndex = 0;

    // Build context with all parameters for field type parsing
    // Context is built with most recent first (like lambda)
    const fieldCtx = [...params].reverse().map(p => p.name);

    while (this.current().type !== 'EOF') {
      const current = this.current();

      // Stop if we hit something that's not a field
      // Fields start with IDENT (for explicit) or LBRACE (for implicit)
      if (current.type !== 'IDENT' && current.type !== 'LBRACE') {
        break;
      }

      // Check for implicit field: {name : Type}
      const implicit = current.type === 'LBRACE';
      if (implicit) {
        this.advance(); // consume '{'
      }

      // Parse field name
      if (this.current().type !== 'IDENT') {
        break; // No more fields
      }

      // Lookahead: check if IDENT is followed by COLON (field) or something else (not a field)
      // This allows record parsing to stop when we hit a different declaration like `id = ...`
      if (!implicit) {
        const nextToken = this.tokens[this.pos + 1];
        if (!nextToken || nextToken.type !== 'COLON') {
          break; // Not a field definition, stop parsing fields
        }
      }

      const fieldNameToken = this.expect('IDENT');
      const fieldName = fieldNameToken.value;

      // Record source range for field name
      const fieldNamePath: IndexPath = [
        { kind: 'field', name: 'fields' },
        { kind: 'array', index: fieldIndex },
        { kind: 'field', name: 'name' }
      ];
      this.recordRange(fieldNamePath, fieldNameToken, fieldNameToken);

      this.expect('COLON');

      // Parse field type - in context of parameters AND previous fields
      const fieldTypePath: IndexPath = [
        { kind: 'field', name: 'fields' },
        { kind: 'array', index: fieldIndex },
        { kind: 'field', name: 'type' }
      ];
      // Field types are parsed in context of params AND previous fields (for dependent records)
      // Most recent binding first: [prev_fields_reversed..., params_reversed...]
      const currentFieldCtx = [...[...fields].reverse().map(f => f.name), ...fieldCtx];
      const fieldType = this.expr(0, currentFieldCtx, fieldTypePath);

      if (implicit) {
        this.expect('RBRACE');
      }

      fields.push({ name: fieldName, type: fieldType, implicit: implicit || undefined });
      fieldIndex++;

      // Skip newlines between fields
      this.skipNewlines();
    }

    return {
      kind: 'record',
      name: nameToken.value,
      type: recordType,
      params,
      fields,
      constructorName,
      extends: extendsNames,
      extendsExprs
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
   * Look ahead to determine if { ... } is a named argument ({ name := value } or shorthand {name})
   * or a named binder ({ name : Type } ->).
   * Returns 'named-arg' or 'named-binder'.
   */
  private peekNamedArgOrBinder(): 'named-arg' | 'named-binder' {
    // Save position
    const savedPos = this.pos;

    // Skip past '{'
    this.advance();

    // Count identifiers
    let identCount = 0;
    while (this.current().type === 'IDENT' || this.current().type === 'UNDERSCORE') {
      this.advance();
      identCount++;
    }

    // Check what follows the identifier(s)
    const nextToken = this.current();
    let result: 'named-arg' | 'named-binder';

    if (nextToken.type === 'ASSIGN') {
      // { name := value } - explicit named arg
      result = 'named-arg';
    } else if (nextToken.type === 'RBRACE' && identCount === 1) {
      // { name } - shorthand for { name := name }
      result = 'named-arg';
    } else {
      // { name : Type } -> ... - named binder
      result = 'named-binder';
    }

    // Restore position
    this.pos = savedPos;
    return result;
  }

  /**
   * Parse a named argument: { name := value } or shorthand { name }
   * Shorthand { name } expands to { name := name } (variable reference with same name).
   * Assumes we're positioned at the opening brace.
   */
  private parseNamedArgument(ctx: NameContext, path: IndexPath): { name: string; value: TTerm; usedShorthand?: boolean } {
    // Save open brace token - we'll record its position AFTER parsing the value
    // to avoid it being modified by prefixSourceMapPaths during application parsing
    const openBraceToken = this.current();
    this.expect('LBRACE');
    const argPath = [...path, { kind: 'field' as const, name: 'arg' }];

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

    // Record source range for the named argument name (e.g., "a" in {a := expr})
    const argNamePath = [...argPath, { kind: 'field' as const, name: 'name' }];
    this.recordRange(argNamePath, nameToken, nameToken);

    let value: TTerm;
    let usedShorthand = false;

    if (this.current().type === 'ASSIGN') {
      // Full syntax: { name := value }
      this.advance(); // consume ':='
      value = this.expr(0, ctx, argPath);
    } else {
      // Shorthand syntax: { name } expands to { name := name }
      usedShorthand = true;
      // Look up the variable name in context to create the reference
      const idx = ctx.indexOf(name);
      if (idx >= 0) {
        value = { tag: 'Var', index: idx };
      } else {
        // Not in context - treat as constant (same as parseIdent)
        value = { tag: 'Const', name };
      }
    }

    // Record close brace position for syntax highlighting
    const closeBraceToken = this.current();
    this.expect('RBRACE');

    // Record brace positions AFTER parsing the value expression.
    // This is important because expr() may call prefixSourceMapPaths() which would
    // modify any paths we recorded earlier (e.g., for applications like "(\x=>x) m").
    const openBracePath = [...argPath, { kind: 'field' as const, name: 'openBrace' }];
    this.recordRange(openBracePath, openBraceToken, openBraceToken);
    const closeBracePath = [...argPath, { kind: 'field' as const, name: 'closeBrace' }];
    this.recordRange(closeBracePath, closeBraceToken, closeBraceToken);

    return { name, value, usedShorthand };
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
            // Record source ranges for each name
            for (let ni = 0; ni < nameTokens.length; ni++) {
              const niPath: IndexPath = [...path, { kind: 'field' as const, name: 'names' }, { kind: 'array' as const, index: ni }];
              this.recordRange(niPath, nameTokens[ni], nameTokens[ni]);
            }
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
      // Record source ranges for each name
      for (let ni = 0; ni < nameTokens.length; ni++) {
        const niPath: IndexPath = [...path, { kind: 'field' as const, name: 'names' }, { kind: 'array' as const, index: ni }];
        this.recordRange(niPath, nameTokens[ni], nameTokens[ni]);
      }
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
        // Parse type at a temporary path so we can remap it to the correct
        // binder path during the right-to-left building phase
        const tempDomainPath: IndexPath = [{ kind: 'field' as const, name: '_ld' }, { kind: 'array' as const, index: groups.length }];
        const type = this.expr(0, ctx, tempDomainPath);
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
        // Remap domain type source map entries from temp path to final path
        const tempPrefix = serializeIndexPath([{ kind: 'field', name: '_ld' }, { kind: 'array', index: i }]);
        const finalDomainPath = serializeIndexPath([...binderPath, { kind: 'field', name: 'domain' }]);
        this.remapSourceMapPaths(tempPrefix, finalDomainPath);
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

        // Record source ranges for each name in the MultiBinder
        const multiBinderPath = currentPath.length > 0 ? currentPath : path;
        for (let ni = 0; ni < group.nameTokens.length; ni++) {
          const niPath: IndexPath = [...multiBinderPath, { kind: 'field' as const, name: 'names' }, { kind: 'array' as const, index: ni }];
          this.recordRange(niPath, group.nameTokens[ni], group.nameTokens[ni]);
        }
        // Remap domain type source map entries from temp path to final path
        const tempPrefix = serializeIndexPath([{ kind: 'field', name: '_ld' }, { kind: 'array', index: i }]);
        const finalDomainPath = serializeIndexPath([...multiBinderPath, { kind: 'field', name: 'domain' }]);
        this.remapSourceMapPaths(tempPrefix, finalDomainPath);
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
   * Parse a single let binding (name, optional type, value).
   * Returns the binding info and updates ctx with the new name.
   */
  private parseLetBinding(ctx: NameContext, path: IndexPath, bindingIndex: number): { binding: TLetBinding; nameToken: Token } {
    let name: string;
    let nameToken: Token;
    let type: TTerm | undefined = undefined;

    // For multi-let, path segments go into bindings array
    const bindingPath = [...path, { kind: 'field' as const, name: 'bindings' }, { kind: 'array' as const, index: bindingIndex }];

    if (this.current().type === 'LPAREN') {
      // Parenthesized form: (x : T)
      this.advance();
      nameToken = this.current();
      name = nameToken.type === 'UNDERSCORE' ? '_' : this.expect('IDENT').value;
      if (nameToken.type === 'UNDERSCORE') this.advance();

      this.expect('COLON');
      const domainPath = [...bindingPath, { kind: 'field' as const, name: 'type' }];
      // Inside parens, can parse full expression including = operator
      type = this.expr(0, ctx, domainPath);
      this.expect('RPAREN');
    } else {
      // Non-parenthesized: x or x : T
      nameToken = this.current();
      name = nameToken.type === 'UNDERSCORE' ? '_' : this.expect('IDENT').value;
      if (nameToken.type === 'UNDERSCORE') this.advance();

      // Optional type annotation
      if (this.current().type === 'COLON') {
        this.advance();
        const domainPath = [...bindingPath, { kind: 'field' as const, name: 'type' }];
        // Parse type with precedence > 50 to stop before '=' operator (precedence 50)
        type = this.expr(51, ctx, domainPath);
      }
    }

    // Record the binder name's source range
    const namePath = [...bindingPath, { kind: 'field' as const, name: 'name' }];
    this.recordRange(namePath, nameToken, nameToken);

    // Expect '='
    if (this.current().type !== 'OPERATOR' || this.current().value !== '=') {
      throw new ParseError(
        `Expected '=' in let binding, got '${this.current().type === 'OPERATOR' ? this.current().value : this.current().type}'`,
        this.current().line,
        this.current().col
      );
    }
    this.advance();

    // Parse the value - each binding can reference previous bindings
    const valuePath = [...bindingPath, { kind: 'field' as const, name: 'value' }];
    const value = this.expr(0, ctx, valuePath);

    return { binding: { name, type, value }, nameToken };
  }

  /**
   * Parse let expression.
   *
   * Syntax variants:
   *   let x = val in body                     -- single binding, no type
   *   let x : T = val in body                 -- single binding with type
   *   let (x : T) = val in body               -- parenthesized type
   *   let a = X, b = Y, c = Z in body         -- multi-let (comma-separated)
   *   let a = X,
   *       b = Y in body                       -- multi-let with newlines
   *
   * Multi-let expands to nested single lets during elaboration.
   * Each binding can reference previous bindings: let a = 1, b = a + 1 in b
   */
  private parseLet(ctx: NameContext, path: IndexPath = []): TTerm {
    const startToken = this.current();
    const letLineStartCol = this.getLineStartCol(startToken.line);
    this.expect('LET');

    // Collect all bindings
    const bindings: TLetBinding[] = [];
    const nameTokens: Token[] = [];
    let currentCtx = ctx;
    let bindingIndex = 0;

    // Parse first binding
    const first = this.parseLetBinding(currentCtx, path, bindingIndex);
    bindings.push(first.binding);
    nameTokens.push(first.nameToken);
    currentCtx = [first.binding.name, ...currentCtx];
    bindingIndex++;

    // Parse additional comma-separated bindings
    while (this.current().type === 'COMMA') {
      this.advance(); // consume comma

      // Skip newlines after comma (allow multi-line let)
      while (this.current().type === 'NEWLINE') {
        this.advance();
      }

      // Check indentation for continuation bindings
      if (this.current().col <= letLineStartCol) {
        throw new ParseError(
          `Let binding continuation must be indented beyond 'let' (column ${letLineStartCol}), found at column ${this.current().col}`,
          this.current().line,
          this.current().col
        );
      }

      const next = this.parseLetBinding(currentCtx, path, bindingIndex);
      bindings.push(next.binding);
      nameTokens.push(next.nameToken);
      currentCtx = [next.binding.name, ...currentCtx];
      bindingIndex++;
    }

    // Expect 'in'
    this.expect('IN');

    // Handle indentation: if there's a newline after 'in', body must be indented
    if (this.current().type === 'NEWLINE') {
      this.advance();
      while (this.current().type === 'NEWLINE') {
        this.advance();
      }
      if (this.current().col <= letLineStartCol) {
        throw new ParseError(
          `Body of let expression must be indented beyond line start (column ${letLineStartCol}), found at column ${this.current().col}`,
          this.current().line,
          this.current().col
        );
      }
    }

    // Parse body with all names in context
    const bodyPath = [...path, { kind: 'field' as const, name: 'body' }];
    const body = this.expr(0, currentCtx, bodyPath);

    // Record full let expression
    if (path.length > 0) {
      const endToken = this.tokens[this.pos - 1];
      this.recordRange(path, startToken, endToken);
    }

    // If single binding, return regular let for backwards compatibility
    if (bindings.length === 1) {
      // For single let, also record name at the original path location
      const singleNamePath = [...path, { kind: 'field' as const, name: 'name' }];
      this.recordRange(singleNamePath, nameTokens[0], nameTokens[0]);
      return mkLetTT(bindings[0].name, bindings[0].type, bindings[0].value, body);
    }

    return mkMultiLetTT(bindings, body);
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
    const result = this.parsePatternAtomWithSourceInternal(path);
    if (result.kind === 'namedArg') {
      throw new ParseError(
        `Named pattern argument {${result.name} := ...} can only appear as argument to a constructor pattern`,
        this.current().line,
        this.current().col
      );
    }
    return result.pattern;
  }

  private parsePatternAtomWithSourceInternal(path: IndexPath):
    | { kind: 'pattern'; pattern: TPattern }
    | { kind: 'namedArg'; name: string; pattern: TPattern } {
    const startToken = this.current();

    // Named pattern: {name}, {_}, or {name := pattern}
    if (startToken.type === 'LBRACE') {
      // Record open brace position
      const openBracePath = [...path, { kind: 'field' as const, name: 'openBrace' }];
      this.recordRange(openBracePath, startToken, startToken);
      this.advance();
      const innerToken = this.current();

      if (innerToken.type === 'IDENT') {
        const name = innerToken.value;
        this.advance();

        // Record source range for the named argument name (e.g., "a" in {a:=Succ p})
        const argNamePath = [...path, { kind: 'field' as const, name: 'name' }];
        this.recordRange(argNamePath, innerToken, innerToken);

        // Check for {name := pattern} syntax
        if (this.current().type === 'ASSIGN') {
          this.advance(); // skip :=
          // Parse the pattern after :=
          const patternPath = [...path, { kind: 'field' as const, name: 'pattern' }];
          const innerPattern = this.parsePatternWithSource(patternPath);
          const endToken = this.current();
          // Record close brace position
          const closeBracePath = [...path, { kind: 'field' as const, name: 'closeBrace' }];
          this.recordRange(closeBracePath, endToken, endToken);
          this.expect('RBRACE');
          this.recordRange(path, startToken, endToken);
          return { kind: 'namedArg', name, pattern: innerPattern };
        }

        // Shorthand {name} - expands to {name := name} (namedArg with PVar pattern)
        const endToken = this.current();
        // Record close brace position
        const closeBracePath = [...path, { kind: 'field' as const, name: 'closeBrace' }];
        this.recordRange(closeBracePath, endToken, endToken);
        this.expect('RBRACE');
        this.recordRange(path, startToken, endToken);
        // This is shorthand for {name := name}, so return as namedArg
        return { kind: 'namedArg', name, pattern: { tag: 'PVar', name } };
      } else if (innerToken.type === 'UNDERSCORE') {
        this.advance();
        const endToken = this.current();
        // Record close brace position
        const closeBracePath = [...path, { kind: 'field' as const, name: 'closeBrace' }];
        this.recordRange(closeBracePath, endToken, endToken);
        this.expect('RBRACE');
        this.recordRange(path, startToken, endToken);
        return { kind: 'pattern', pattern: { tag: 'PWild', named: true } };
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
      return { kind: 'pattern', pattern: { tag: 'PWild' } };
    }

    if (startToken.type === 'IDENT') {
      const name = startToken.value;
      this.advance();

      // All identifiers are parsed uniformly - elaboration will resolve
      // whether it's a constructor or variable based on context lookup
      this.recordRange(path, startToken, startToken);
      return { kind: 'pattern', pattern: { tag: 'PCtor', name, args: [] } };
    }

    if (startToken.type === 'LPAREN') {
      this.advance();
      const pattern = this.parsePatternWithSource(path);
      this.expect('RPAREN');
      // Don't overwrite the inner pattern's range - parens are just grouping
      // The inner pattern already recorded its own range at `path`
      return { kind: 'pattern', pattern };
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
      // Also handles named args: "Ctor {A := x} y"
      if (this.canStartPattern(this.current())) {
        // Record the constructor name itself at path.name
        const namePath: IndexPath = [...path, { kind: 'field', name: 'name' }];
        this.recordRange(namePath, startToken, startToken);

        // Parse all arguments (mixing parenthesized, bare, and named is allowed)
        const args: TPattern[] = [];
        const namedArgs: Array<{ name: string; pattern: TPattern }> = [];
        let argIndex = 0;
        while (this.canStartPattern(this.current())) {
          const argPath: IndexPath = [...path, { kind: 'field', name: 'args' }, { kind: 'array', index: argIndex }];
          const result = this.parsePatternAtomWithSourceInternal(argPath);
          if (result.kind === 'namedArg') {
            namedArgs.push({ name: result.name, pattern: result.pattern });
          } else {
            args.push(result.pattern);
          }
          argIndex++;
        }
        const endToken = this.tokens[this.pos - 1];
        this.recordRange(path, startToken, endToken);
        return { tag: 'PCtor', name, args, namedArgs: namedArgs.length > 0 ? namedArgs : undefined };
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
   * Parse tactic block after 'by' keyword
   *
   * Syntax:
   *   by
   *     tactic1
   *     tactic2
   *     ...
   *
   * Tactics are indented and one per line.
   */
  private parseTacticBlock(ctx: NameContext, path: IndexPath = []): TTerm {
    const startToken = this.current();

    // 'by' keyword should already be consumed by caller
    // Expect newline after 'by'
    this.expectNewline('Expected newline after \'by\'');

    // Skip any additional newlines
    this.skipNewlines();

    // Store current indentation level (first tactic's indentation)
    const baseIndent = this.current().col;

    const tactics: TacticCommand[] = [];
    let tacticIndex = 0;

    // Parse tactics while at the same or greater indentation
    while (this.current().type !== 'EOF') {
      const currentIndent = this.current().col;

      // If we've dedented, we're done with the tactic block
      if (currentIndent < baseIndent) {
        break;
      }

      // Parse single tactic
      const tacticPath = [...path, { kind: 'field' as const, name: 'tactics' }, { kind: 'array' as const, index: tacticIndex }];
      const tactic = this.parseTactic(ctx, tacticPath);
      tactics.push(tactic);
      tacticIndex++;

      // Expect newline after tactic (or EOF)
      if (this.current().type === 'NEWLINE') {
        this.advance();
        this.skipNewlines();
      } else if (this.current().type !== 'EOF') {
        // If not newline and not EOF, check if we've dedented
        if (this.current().col < baseIndent) {
          break;
        }
        throw new ParseError(
          'Expected newline after tactic',
          this.current().line,
          this.current().col
        );
      }
    }

    // Allow empty tactic blocks - they'll fail during elaboration/type-checking
    // with "unsolved goals" error instead of parse error

    // Record full tactic block
    if (path.length > 0) {
      const endToken = this.tokens[this.pos - 1];
      this.recordRange(path, startToken, endToken);
    }

    return mkTacticBlockTT(tactics);
  }

  /**
   * Parse a single tactic command with its arguments
   *
   * Dispatch based on tactic name:
   * - intro, intros: parse identifier(s)
   * - exact, apply, refine: parse term
   * - assumption, constructor, reflexivity: no arguments
   * - have: parse identifier ':' term ':=' term
   */
  private parseTactic(ctx: NameContext, path: IndexPath): TacticCommand {
    // Tactic name is always an identifier
    if (this.current().type !== 'IDENT') {
      throw new ParseError(
        'Expected tactic name',
        this.current().line,
        this.current().col
      );
    }

    const tacticName = this.current().value;
    const tacticToken = this.current();
    this.advance();

    // Record tactic name
    const namePath = [...path, { kind: 'field' as const, name: 'name' }];
    this.recordRange(namePath, tacticToken, tacticToken);

    // Dispatch based on tactic name
    switch (tacticName) {
      case 'intro': {
        // intro <identifier>
        if (this.current().type !== 'IDENT') {
          throw new ParseError(
            'intro expects an identifier argument',
            this.current().line,
            this.current().col
          );
        }
        const argName = this.current().value;
        const argToken = this.current();
        this.advance();

        const argPath = [...path, { kind: 'field' as const, name: 'args' }, { kind: 'array' as const, index: 0 }];
        this.recordRange(argPath, argToken, argToken);

        return {
          name: tacticName,
          args: [mkConstTT(argName)]
        };
      }

      case 'intros': {
        // intros [<identifier>]*
        const args: TTerm[] = [];
        let argIndex = 0;

        while (this.current().type === 'IDENT' && this.current().col > tacticToken.col) {
          const argName = this.current().value;
          const argToken = this.current();
          this.advance();

          const argPath = [...path, { kind: 'field' as const, name: 'args' }, { kind: 'array' as const, index: argIndex }];
          this.recordRange(argPath, argToken, argToken);

          args.push(mkConstTT(argName));
          argIndex++;
        }

        return {
          name: tacticName,
          args
        };
      }

      case 'exact':
      case 'apply':
      case 'refine':
      case 'rewrite': {
        // Parse a full term
        const argPath = [...path, { kind: 'field' as const, name: 'args' }, { kind: 'array' as const, index: 0 }];
        const termArg = this.expr(0, ctx, argPath);

        return {
          name: tacticName,
          args: [termArg]
        };
      }

      case 'assumption':
      case 'constructor':
      case 'reflexivity': {
        // No arguments
        return {
          name: tacticName,
          args: []
        };
      }

      case 'cases':
      case 'induction': {
        // cases/induction <identifier> [with | ctor params => tactics | ...]
        if (this.current().type !== 'IDENT') {
          throw new ParseError(
            `${tacticName} expects an identifier argument`,
            this.current().line,
            this.current().col
          );
        }
        const argName = this.current().value;
        const argToken = this.current();
        this.advance();

        const argPath = [...path, { kind: 'field' as const, name: 'args' }, { kind: 'array' as const, index: 0 }];
        this.recordRange(argPath, argToken, argToken);

        // Check for optional 'with' clause for structured syntax
        if (this.current().type === 'WITH') {
          this.advance(); // consume 'with'

          // Expect newline after 'with'
          this.expectNewline('Expected newline after \'with\'');
          this.skipNewlines();

          // Parse case branches: | ctor params => tactics
          const caseBranches: CaseBranch[] = [];

          while (this.current().type === 'PIPE') {
            this.advance(); // consume '|'

            // Parse constructor name
            if (this.current().type !== 'IDENT') {
              throw new ParseError(
                'Expected constructor name after |',
                this.current().line,
                this.current().col
              );
            }
            const ctorName = this.current().value;
            this.advance();

            // Parse optional parameters
            const params: string[] = [];
            while (this.current().type === 'IDENT' && this.current().col > tacticToken.col) {
              params.push(this.current().value);
              this.advance();
            }

            // Expect '=>'
            if (this.current().type !== 'FATARROW') {
              throw new ParseError(
                'Expected => after constructor pattern',
                this.current().line,
                this.current().col
              );
            }
            this.advance(); // consume '=>'

            // Parse tactics for this branch (may be on same line or next line)
            const branchTactics: TacticCommand[] = [];
            const branchTacticPath = [...path, { kind: 'field' as const, name: 'caseBranches' }, { kind: 'array' as const, index: caseBranches.length }];

            if (this.current().type === 'NEWLINE') {
              // Multi-line branch: parse indented tactic sequence
              this.advance();
              this.skipNewlines();
              const branchBaseIndent = this.current().col;

              while (this.current().type !== 'EOF' &&
                     this.current().type !== 'PIPE' &&
                     this.current().col >= branchBaseIndent) {
                const bt = this.parseTactic(ctx, branchTacticPath);
                branchTactics.push(bt);

                if (this.current().type === 'NEWLINE') {
                  this.advance();
                  this.skipNewlines();
                } else {
                  break;
                }
              }
            } else {
              // Single-line branch: parse one tactic
              const bt = this.parseTactic(ctx, branchTacticPath);
              branchTactics.push(bt);
            }

            caseBranches.push({
              constructor: ctorName,
              params,
              tactics: branchTactics
            });

            // Expect newline after branch (or EOF)
            if (this.current().type === 'NEWLINE') {
              this.advance();
              this.skipNewlines();
            } else if (this.current().type !== 'EOF' && this.current().type !== 'PIPE') {
              // If not newline, EOF, or next pipe, check if we've dedented
              if (this.current().col < tacticToken.col) {
                break;
              }
            }
          }

          return {
            name: tacticName,
            args: [mkConstTT(argName)],
            caseBranches
          };
        }

        // No 'with' clause - simple cases
        return {
          name: tacticName,
          args: [mkConstTT(argName)]
        };
      }

      case 'have': {
        // have <identifier> ':' <term> ':=' <term>
        if (this.current().type !== 'IDENT') {
          throw new ParseError(
            'have expects identifier after \'have\'',
            this.current().line,
            this.current().col
          );
        }

        const hypName = this.current().value;
        const hypNameToken = this.current();
        this.advance();

        this.expect('COLON');

        const hypTypePath = [...path, { kind: 'field' as const, name: 'args' }, { kind: 'array' as const, index: 1 }];
        const hypType = this.expr(0, ctx, hypTypePath);

        this.expect('ASSIGN');

        const hypProofPath = [...path, { kind: 'field' as const, name: 'args' }, { kind: 'array' as const, index: 2 }];
        const hypProof = this.expr(0, ctx, hypProofPath);

        const hypNamePath = [...path, { kind: 'field' as const, name: 'args' }, { kind: 'array' as const, index: 0 }];
        this.recordRange(hypNamePath, hypNameToken, hypNameToken);

        return {
          name: tacticName,
          args: [mkConstTT(hypName), hypType, hypProof]
        };
      }

      default:
        throw new ParseError(
          `Unknown tactic: ${tacticName}`,
          tacticToken.line,
          tacticToken.col
        );
    }
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
      case 'PCtor': {
        // With uniform identifier parsing, all identifiers become PCtor nodes.
        // We need to determine which are variables (should be bound) vs constructors.
        //
        // Heuristic for no-arg PCtor (and no namedArgs):
        // - Lowercase first letter: variable (e.g., 'a', 'b', 'default')
        // - Single uppercase letter: type variable (e.g., 'A', 'T')
        // - Multi-character starting with uppercase: constructor (e.g., 'Zero', 'Succ')
        //
        // NOTE: This heuristic can be wrong for lowercase constructors (like 'refl').
        // In such cases, elaboration must resolve the ambiguity by checking if a
        // pattern name is actually a constructor, and adjusting the RHS accordingly.
        const hasArgs = pattern.args.length > 0 || (pattern.namedArgs && pattern.namedArgs.length > 0);
        if (!hasArgs) {
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
        // First collect from positional args, then from named args
        const positionalVars = pattern.args.flatMap(arg => this.collectPatternVars(arg));
        const namedVars = pattern.namedArgs
          ? pattern.namedArgs.flatMap(na => this.collectPatternVars(na.pattern))
          : [];
        return [...positionalVars, ...namedVars];
      }
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
  private parseType(ctx: NameContext, path: IndexPath = []): TTerm {
    const startToken = this.current();
    const typeToken = this.expect('TYPE');

    let result: TTerm;

    // Check if the TYPE token has a level suffix (from Type_n in lexer)
    // The lexer stores this in the token value as "Type_n"
    if (typeToken.value.startsWith('Type_')) {
      const levelStr = typeToken.value.substring(5);
      const level = parseInt(levelStr, 10);
      if (!isNaN(level)) {
        result = mkTypeTT(level);  // Type_n = Sort(n+1), mkTypeTT adds the +1
      } else {
        result = mkTypeTT(0);  // Just "Type" = Type 0 = Sort(1)
      }
    } else if (this.current().type === 'NUMBER') {
      // Check for "Type n" syntax (space followed by number)
      const level = parseInt(this.current().value, 10);
      this.advance();
      result = mkTypeTT(level);  // Type n = Sort(n+1), mkTypeTT adds the +1
    } else if (this.current().type === 'IDENT') {
      // Type U - level variable or omega
      const identToken = this.current();
      const name = identToken.value;
      this.advance();
      if (name === 'ω') {
        result = mkSortTT(mkUSuccAppTT(mkUOmegaTT())); // Type ω = Sort(ω+1)
      } else {
        // Check if this is a bound variable (e.g., from {u : ULevel} ->)
        const idx = ctx.indexOf(name);
        if (idx >= 0) {
          result = mkSortTT(mkUSuccAppTT(mkVarTT(idx))); // Type u where u is bound = Sort(u+1)
        } else {
          result = mkSortTT(mkUSuccAppTT(mkConstTT(name))); // Type U where U is a constant = Sort(U+1)
        }
        // Record source range for the level identifier (e.g., "u" in "Type u")
        // The term structure is Sort(App(USucc, Var/Const)), so the level var is at path.level.arg
        const levelArgPath = [...path, { kind: 'field' as const, name: 'level' }, { kind: 'field' as const, name: 'arg' }];
        this.recordRange(levelArgPath, identToken, identToken);
      }
    } else if (this.current().type === 'LPAREN') {
      // Type (level-expr) - parenthesized level expression
      this.advance(); // consume '('
      const level = this.parseLevelExpr(ctx);
      this.expect('RPAREN');
      result = mkSortTT(mkUSuccAppTT(level)); // Type l = Sort(l+1)
    } else {
      // Just "Type" means Type 0 = Sort(1)
      result = mkTypeTT(0);
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
   * - U           → Var(idx) if U is bound, Const("U") otherwise
   * - USucc e     → LSucc(e)
   * - UMax e1 e2  → LMax(e1, e2)
   * - UIMax e1 e2 → LIMax(e1, e2)
   * - (expr)      → parenthesized level expression
   *
   * @param ctx - Name context for resolving bound level variables
   */
  private parseLevelExpr(ctx: NameContext): TTerm {
    const current = this.current();

    if (current.type === 'NUMBER') {
      const n = parseInt(current.value, 10);
      this.advance();
      return mkULitTT(n);
    }

    // UZero is the zero universe level
    if (current.type === 'UZERO') {
      this.advance();
      return mkULitTT(0);
    }

    if (current.type === 'IDENT') {
      const name = current.value;
      // Check for omega (ω or 'omega')
      if (name === 'ω') {
        this.advance();
        return mkUOmegaTT();
      }
      this.advance();
      // Check if this is a bound variable (e.g., from {u : ULevel} ->)
      const idx = ctx.indexOf(name);
      if (idx >= 0) {
        return mkVarTT(idx); // Bound level variable
      }
      return mkConstTT(name); // Unbound - resolved during elaboration
    }

    if (current.type === 'USUCC') {
      this.advance(); // consume 'USucc'
      const pred = this.parseLevelAtom(ctx);
      return mkUSuccAppTT(pred);
    }

    if (current.type === 'UMAX') {
      this.advance(); // consume 'UMax'
      const left = this.parseLevelAtom(ctx);
      const right = this.parseLevelAtom(ctx);
      return mkUMaxAppTT(left, right);
    }

    if (current.type === 'UIMAX') {
      this.advance(); // consume 'UIMax'
      const left = this.parseLevelAtom(ctx);
      const right = this.parseLevelAtom(ctx);
      return mkUIMaxAppTT(left, right);
    }

    if (current.type === 'LPAREN') {
      this.advance(); // consume '('
      const level = this.parseLevelExpr(ctx);
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
   *
   * @param ctx - Name context for resolving bound level variables
   */
  private parseLevelAtom(ctx: NameContext): TTerm {
    const current = this.current();

    if (current.type === 'NUMBER') {
      const n = parseInt(current.value, 10);
      this.advance();
      return mkULitTT(n);
    }

    // UZero is the zero universe level
    if (current.type === 'UZERO') {
      this.advance();
      return mkULitTT(0);
    }

    if (current.type === 'IDENT') {
      const name = current.value;
      // Check for omega (ω or 'omega')
      if (name === 'ω') {
        this.advance();
        return mkUOmegaTT();
      }
      this.advance();
      // Check if this is a bound variable (e.g., from {u : ULevel} ->)
      const idx = ctx.indexOf(name);
      if (idx >= 0) {
        return mkVarTT(idx); // Bound level variable
      }
      return mkConstTT(name); // Unbound - resolved during elaboration
    }

    if (current.type === 'LPAREN') {
      this.advance(); // consume '('
      const level = this.parseLevelExpr(ctx);
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
   * Expect a newline token with custom error message
   */
  private expectNewline(message?: string): Token {
    const token = this.current();
    if (token.type !== 'NEWLINE' && token.type !== 'EOF') {
      throw new ParseError(
        message || `Expected newline but got ${token.type} '${token.value}'`,
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

