/**
 * Fresh TT Compiler - A clean implementation of the compilation pipeline
 *
 * This module provides a simple interface for compiling TT source code
 * to elaborated kernel terms (TTK).
 */

import { groupByIndentation } from '../parser/indentation-grouper';
import { Parser, ParsedDeclaration, ParseError } from '../parser/parser';
import { elabToKernelWithMap, elabPatternToKernel, elabPatternToKernelWithMap, buildConstructorParamNames, setConstructorParamNames, resetWildcardCounter, extractConstructorParamNames, setCurrentTermParamNames, extractNamedArgMap, countParameters, reorderPatterns, hasNamedPatterns, applyVarPermutation, fixRhsForConstructorPatterns, ConstructorParamNames, NamedArgMap, NamedArgElabError } from './elab';
import { TTKTerm, TTKContext, prettyPrint as prettyPrintTTK, prettyPrintFormatted, TTKClause, TTKPattern, prettyPrintPattern, prettyPrintPatternList } from './kernel';
import { TTerm, TPattern, TClause } from './surface';
import { validateDeclarations, emptySymbolContext, SymbolContext } from '../types/name-resolution';
import { resolvePatternsInDeclarations } from '../parser/pattern-resolution';
import { arraySeg, fieldSeg, appendPath, ElabMap, IndexPath, SourceMap, serializeIndexPath, deserializeIndexPath } from '../types/source-position'
import { checkType, inferType } from './checker';
import { addDefinitionInTCEnv, countPiBinders, createDefinitionsMap, createNamedArgInfoLookup, createTCEnv, DefinitionsMap, extractPiSpine, MatchPartIndex, setDefinitionValueInTCEnv, TCEnv, TCEnvError, TermDefinition, TermDefinitionPartIndex, validateTermNameNotDefined } from './term';
import { checkInductiveDeclaration } from './inductive';
import { checkMatchClause, arePatternsAbsurd } from './patterns';
import { checkTotality, TotalityResult, CaseTree } from './totality';
import { checkStructuralRecursion } from './recursion';
export type { TotalityResult, CaseTree };

// ============================================================================
// Global Configuration
// ============================================================================

/**
 * Whether to show wildcard inlay hints (e.g., `_[n0]`) in the editor.
 */
export const SHOW_WILDCARD_INLAY_HINTS = false;

// ============================================================================
// Parse Result Types
// ============================================================================

/**
 * A single parsed block - either declarations, a comment, or an error
 */
export type ParsedBlock =
  | { kind: 'declarations'; declarations: ParsedDeclaration[]; sourceMaps: SourceMap[]; sourceLines: string[]; startLine: number }
  | { kind: 'comment'; sourceLines: string[]; startLine: number }
  | { kind: 'error'; errors: ParseError[]; sourceLines: string[]; startLine: number };

/**
 * Result of parsing source text
 */
export interface ParseResult {
  blocks: ParsedBlock[];
  totalErrors: number;
}

// ============================================================================
// Elaboration Result Types
// ============================================================================

/**
 * A single elaborated declaration (TT -> TTK)
 */
export interface ElabDeclaration {
  name: string | undefined;
  kind: 'inductive' | 'term';
  // Surface (parsed) terms - used for syntax highlighting
  surfaceType?: TTerm;
  surfaceValue?: TTerm;
  surfaceConstructors?: Array<{ name: string; type: TTerm }>;
  // Elaborated kernel terms
  kernelType?: TTKTerm;
  kernelValue?: TTKTerm;
  kernelConstructors?: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }>;
  /** Maps kernel paths to surface paths (for error mapping) */
  elabMap?: ElabMap;
  /** Maps surface paths to source ranges (for error mapping) */
  sourceMap?: SourceMap;
  /** Error that occurred during elaboration (e.g., named argument errors) */
  elabError?: string;
  /** Serialized surface path where elaboration error occurred */
  elabErrorPath?: string;
}

/**
 * A single elaborated block
 */
export type ElabBlock =
  | { kind: 'declarations'; declarations: ElabDeclaration[]; sourceLines: string[]; startLine: number }
  | { kind: 'comment'; sourceLines: string[]; startLine: number }
  | { kind: 'error'; errors: ParseError[]; sourceLines: string[]; startLine: number };

/**
 * Result of elaborating parsed source
 */
export interface ElabResult {
  blocks: ElabBlock[];
}

// ============================================================================
// Compile Result Types
// ============================================================================

/**
 * Result of compiling a single declaration
 */
export interface CompiledDeclaration {
  name: string | undefined;
  kind: 'inductive' | 'term';

  // Surface (parsed) terms - used for syntax highlighting
  surfaceType?: TTerm;
  surfaceValue?: TTerm;
  surfaceConstructors?: Array<{ name: string; type: TTerm }>;

  // Elaborated kernel terms
  kernelType?: TTKTerm;
  kernelValue?: TTKTerm;
  kernelConstructors?: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }>;

  // For inductive types: positions that are indices (not parameters)
  indexPositions?: number[];

  // Pretty-printed versions for display
  prettyType?: string;
  prettyValue?: string;
  prettyConstructors?: Array<{ name: string; prettyType: string }>;

  // Type checking results
  checkSuccess: boolean;
  checkErrors: TCEnvError[];

  // Totality checking results (for pattern matching terms)
  totalityResult?: TotalityResult;

  // Source mapping for error locations
  elabMap?: ElabMap;
  sourceMap?: SourceMap;

  // Elaboration error source path (for locating errors in source)
  elabErrorPath?: string;
}

/**
 * Name resolution error with source range for squiggly display
 */
export interface NameResolutionErrorWithRange {
  message: string;
  symbolName: string;
  /** Serialized IndexPath for looking up source range */
  path?: string;
  /** Index of the declaration this error belongs to (for sourceMap lookup) */
  declarationIndex?: number;
}

/**
 * Result of compiling a block of source code
 */
export interface CompiledBlock {
  blockIndex: number;
  sourceLines: string[];
  startLine: number;

  // Parsing
  parseSuccess: boolean;
  parseErrors: ParseError[];

  // Name resolution
  nameResolutionSuccess: boolean;
  nameResolutionErrors: NameResolutionErrorWithRange[];

  // Elaborated declarations
  declarations: CompiledDeclaration[];

  // Block metadata
  isComment: boolean;
}

/**
 * Full result of compiling source text
 */
export interface CompileResult {
  success: boolean;
  blocks: CompiledBlock[];
  totalParseErrors: number;
  totalNameErrors: number;
  totalCheckErrors: number;
}

// ============================================================================
// SourceMap Adjustment Helper
// ============================================================================

/**
 * Adjust a sourceMap's line numbers by adding a block offset.
 * This converts block-relative positions to file-absolute positions.
 *
 * @param sourceMap - Original sourceMap with block-relative positions
 * @param blockStartLine - 1-based line number where the block starts in the file
 * @returns New sourceMap with file-absolute positions
 */
function adjustSourceMapToAbsolute(sourceMap: SourceMap, blockStartLine: number): SourceMap {
  if (blockStartLine === 1) {
    // No adjustment needed for first block
    return sourceMap;
  }

  const offset = blockStartLine - 1;
  const adjusted = new Map<string, { start: { line: number; col: number; pos: number }; end: { line: number; col: number; pos: number } }>();

  for (const [key, range] of sourceMap) {
    adjusted.set(key, {
      start: {
        line: range.start.line + offset,
        col: range.start.col,
        pos: range.start.pos  // Note: pos is relative to block, not adjusted
      },
      end: {
        line: range.end.line + offset,
        col: range.end.col,
        pos: range.end.pos
      }
    });
  }

  return adjusted;
}

/**
 * Information for a wildcard inlay hint
 */
export interface WildcardInlayHint {
  /** Line number (1-based) */
  line: number;
  /** Column number (1-based, position after the underscore) */
  column: number;
  /** The generated wildcard name (e.g., "0", "1") */
  name: string;
}

/**
 * Semantic token types for syntax highlighting
 */
export type SemanticTokenType = 'termName' | 'constName' | 'boundVar' | 'patternVar' | 'absurd' | 'namedBrace';

/**
 * A semantic token for highlighting
 */
export interface SemanticToken {
  /** Line number (1-based) */
  line: number;
  /** Column number (1-based) */
  column: number;
  /** Length of the token in characters */
  length: number;
  /** The semantic type of this token */
  type: SemanticTokenType;
}

/**
 * Information about a hole location for warning markers
 */
export interface HoleLocation {
  /** Line number (1-based) */
  line: number;
  /** Column number (1-based) */
  column: number;
  /** End column (1-based, exclusive) */
  endColumn: number;
  /** The hole identifier (e.g., "?sorry") */
  id: string;
}

/**
 * Extract semantic tokens from a compile result for syntax highlighting.
 *
 * This walks through the SURFACE terms (TTerm, TPattern) directly,
 * using the sourceMap to find source positions. No elabMap needed.
 *
 * Token types:
 * - Var (de Bruijn) → boundVar (light blue)
 * - Const lowercase → termName (yellow)
 * - Const uppercase → constName (white)
 * - Binder name → patternVar (light blue)
 * - PVar/PWild → patternVar (light blue)
 * - PCtor → constName (white)
 */
export function extractSemanticTokens(result: CompileResult): SemanticToken[] {
  const tokens: SemanticToken[] = [];

  for (const block of result.blocks) {
    for (const decl of block.declarations) {
      if (!decl.sourceMap) continue;

      // Process declaration name (e.g., "Nat" in "inductive Nat", "plus" in "plus : ...")
      if (decl.name) {
        const tokenType = decl.kind === 'inductive' ? 'constName' : 'termName';
        addSemanticTokenDirect(['name'], decl.sourceMap, block.startLine, tokenType, tokens);
      }

      // Process declaration type (surface)
      if (decl.surfaceType) {
        collectSemanticTokensFromSurfaceTerm(
          decl.surfaceType,
          decl.sourceMap,
          block.startLine,
          ['type'],
          tokens
        );
      }

      // Process declaration value (surface)
      if (decl.surfaceValue) {
        collectSemanticTokensFromSurfaceTerm(
          decl.surfaceValue,
          decl.sourceMap,
          block.startLine,
          ['value'],
          tokens
        );

        // For pattern matching definitions, also emit tokens for term names on each clause line
        // These are recorded at value.clauses[N].defName by the parser
        if (decl.surfaceValue.tag === 'Match') {
          for (let i = 0; i < decl.surfaceValue.clauses.length; i++) {
            addSemanticTokenDirect(
              ['value', 'clauses', i, 'defName'],
              decl.sourceMap,
              block.startLine,
              'termName',
              tokens
            );
          }
        }
      }

      // Process constructors (surface)
      if (decl.surfaceConstructors) {
        for (let i = 0; i < decl.surfaceConstructors.length; i++) {
          // Constructor name at definition site (e.g., "Zero" in "Zero : Nat")
          addSemanticTokenDirect(['constructors', i, 'name'], decl.sourceMap, block.startLine, 'constName', tokens);
          // Constructor type
          collectSemanticTokensFromSurfaceTerm(
            decl.surfaceConstructors[i].type,
            decl.sourceMap,
            block.startLine,
            ['constructors', i, 'type'],
            tokens
          );
        }
      }
    }
  }

  return tokens;
}

/**
 * Walk a surface term (TTerm) and collect semantic tokens.
 * Surface term paths map directly to sourceMap paths.
 */
function collectSemanticTokensFromSurfaceTerm(
  term: TTerm,
  sourceMap: SourceMap,
  blockStartLine: number,
  path: (string | number)[],
  tokens: SemanticToken[]
): void {
  switch (term.tag) {
    case 'Var':
      // Bound variable reference
      addSemanticTokenDirect(path, sourceMap, blockStartLine, 'boundVar', tokens);
      break;

    case 'Const':
      // Check if lowercase (term) or uppercase (constructor/type)
      if (term.name.length > 0) {
        const firstChar = term.name[0];
        const isUppercase = firstChar >= 'A' && firstChar <= 'Z';
        const tokenType = isUppercase ? 'constName' : 'termName';
        addSemanticTokenDirect(path, sourceMap, blockStartLine, tokenType, tokens);
      }
      break;

    case 'Sort':
      // Type/Prop keywords - skip for now
      break;

    case 'Hole':
      collectSemanticTokensFromSurfaceTerm(term.type, sourceMap, blockStartLine, [...path, 'type'], tokens);
      break;

    case 'Binder':
      // Binder name is a pattern variable (light blue)
      addSemanticTokenDirect([...path, 'name'], sourceMap, blockStartLine, 'patternVar', tokens);
      // If named (e.g., { A : Type } ->), emit tokens for braces
      if (term.named) {
        addSemanticTokenDirect([...path, 'openBrace'], sourceMap, blockStartLine, 'namedBrace', tokens);
        addSemanticTokenDirect([...path, 'closeBrace'], sourceMap, blockStartLine, 'namedBrace', tokens);
      }
      // Recurse into domain (if present) and body
      if (term.domain !== undefined) {
        collectSemanticTokensFromSurfaceTerm(term.domain, sourceMap, blockStartLine, [...path, 'domain'], tokens);
      }
      collectSemanticTokensFromSurfaceTerm(term.body, sourceMap, blockStartLine, [...path, 'body'], tokens);
      // Handle let binding value
      if (term.binderKind.tag === 'BLetTT') {
        collectSemanticTokensFromSurfaceTerm(term.binderKind.defVal, sourceMap, blockStartLine, [...path, 'binderKind', 'defVal'], tokens);
      }
      break;

    case 'App':
      collectSemanticTokensFromSurfaceTerm(term.fn, sourceMap, blockStartLine, [...path, 'fn'], tokens);
      collectSemanticTokensFromSurfaceTerm(term.arg, sourceMap, blockStartLine, [...path, 'arg'], tokens);
      // If named argument (e.g., f { A := x }), emit tokens for braces
      if (term.argName) {
        addSemanticTokenDirect([...path, 'arg', 'openBrace'], sourceMap, blockStartLine, 'namedBrace', tokens);
        addSemanticTokenDirect([...path, 'arg', 'closeBrace'], sourceMap, blockStartLine, 'namedBrace', tokens);
      }
      break;

    case 'Annot':
      collectSemanticTokensFromSurfaceTerm(term.term, sourceMap, blockStartLine, [...path, 'term'], tokens);
      collectSemanticTokensFromSurfaceTerm(term.type, sourceMap, blockStartLine, [...path, 'type'], tokens);
      break;

    case 'Match':
      collectSemanticTokensFromSurfaceTerm(term.scrutinee, sourceMap, blockStartLine, [...path, 'scrutinee'], tokens);
      for (let i = 0; i < term.clauses.length; i++) {
        const clause = term.clauses[i];
        // The parser records ALL patterns (both positional and named) under
        // patterns[0], patterns[1], etc. in parsing order. But the data structure
        // separates them into clause.patterns (positional) and clause.namedPatterns.
        // To extract brace tokens for named patterns, we need to iterate through
        // ALL parsing indices and look for braces.
        const totalPatternCount = clause.patterns.length + (clause.namedPatterns?.length || 0);
        for (let j = 0; j < totalPatternCount; j++) {
          // Try to add brace tokens (only exist for named patterns)
          addSemanticTokenDirect([...path, 'clauses', i, 'patterns', j, 'openBrace'], sourceMap, blockStartLine, 'namedBrace', tokens);
          addSemanticTokenDirect([...path, 'clauses', i, 'patterns', j, 'closeBrace'], sourceMap, blockStartLine, 'namedBrace', tokens);
        }
        // Collect from positional patterns. Named patterns come first in the source,
        // so positional patterns have source map indices offset by namedPatterns.length.
        const namedPatternCount = clause.namedPatterns?.length || 0;
        for (let j = 0; j < clause.patterns.length; j++) {
          const sourceMapIndex = j + namedPatternCount;
          collectSemanticTokensFromSurfacePattern(
            clause.patterns[j],
            sourceMap,
            blockStartLine,
            [...path, 'clauses', i, 'patterns', sourceMapIndex],
            tokens
          );
        }
        // Collect from named patterns (they are at indices 0..namedPatternCount-1 in source map)
        if (clause.namedPatterns) {
          for (let j = 0; j < clause.namedPatterns.length; j++) {
            collectSemanticTokensFromSurfacePattern(
              clause.namedPatterns[j].pattern,
              sourceMap,
              blockStartLine,
              [...path, 'clauses', i, 'patterns', j, 'pattern'],
              tokens
            );
          }
        }
        // Collect from RHS
        collectSemanticTokensFromSurfaceTerm(
          clause.rhs,
          sourceMap,
          blockStartLine,
          [...path, 'clauses', i, 'rhs'],
          tokens
        );
      }
      break;

    case 'AbsurdMarker':
      // #absurd marker - highlight in red
      addSemanticTokenDirect(path, sourceMap, blockStartLine, 'absurd', tokens);
      break;

    case 'ULevel':
      // Level type keyword - skip for now
      break;

    case 'MultiBinder':
      // Multi-binder: (a b c : T) -> B or { a b : T } -> B
      for (let i = 0; i < term.names.length; i++) {
        addSemanticTokenDirect([...path, 'names', i], sourceMap, blockStartLine, 'patternVar', tokens);
      }
      // If named (e.g., { A B : Type } ->), emit tokens for braces
      if (term.named) {
        addSemanticTokenDirect([...path, 'openBrace'], sourceMap, blockStartLine, 'namedBrace', tokens);
        addSemanticTokenDirect([...path, 'closeBrace'], sourceMap, blockStartLine, 'namedBrace', tokens);
      }
      collectSemanticTokensFromSurfaceTerm(term.domain, sourceMap, blockStartLine, [...path, 'domain'], tokens);
      collectSemanticTokensFromSurfaceTerm(term.body, sourceMap, blockStartLine, [...path, 'body'], tokens);
      break;
  }
}

/**
 * Collect semantic tokens from a surface pattern (TPattern)
 */
function collectSemanticTokensFromSurfacePattern(
  pattern: TPattern,
  sourceMap: SourceMap,
  blockStartLine: number,
  path: (string | number)[],
  tokens: SemanticToken[]
): void {
  switch (pattern.tag) {
    case 'PVar':
    case 'PWild':
      // Pattern variable - light blue
      addSemanticTokenDirect(path, sourceMap, blockStartLine, 'patternVar', tokens);
      // If named (e.g., {A} or {_}), emit tokens for braces
      if (pattern.named) {
        addSemanticTokenDirect([...path, 'openBrace'], sourceMap, blockStartLine, 'namedBrace', tokens);
        addSemanticTokenDirect([...path, 'closeBrace'], sourceMap, blockStartLine, 'namedBrace', tokens);
      }
      break;

    case 'PCtor':
      // Constructor pattern - white for the constructor name
      // For patterns with args, the name is recorded at path.name
      // For zero-arg patterns, the name is recorded at path itself
      if (pattern.args.length > 0) {
        addSemanticTokenDirect([...path, 'name'], sourceMap, blockStartLine, 'constName', tokens);
        // Recurse into args
        for (let i = 0; i < pattern.args.length; i++) {
          collectSemanticTokensFromSurfacePattern(
            pattern.args[i],
            sourceMap,
            blockStartLine,
            [...path, 'args', i],
            tokens
          );
        }
      } else {
        // Zero-arg constructor: the whole pattern range IS the constructor name
        addSemanticTokenDirect(path, sourceMap, blockStartLine, 'constName', tokens);
      }
      break;
  }
}

/**
 * Add a semantic token directly from sourceMap (no elabMap needed for surface terms)
 */
function addSemanticTokenDirect(
  path: (string | number)[],
  sourceMap: SourceMap,
  _blockStartLine: number,  // Unused - sourceMap already has absolute positions
  type: SemanticTokenType,
  tokens: SemanticToken[]
): void {
  const pathStr = serializePathForLookup(path);
  const range = sourceMap.get(pathStr);
  if (range) {
    // Note: sourceMap positions are already file-absolute (adjusted in elaboration phase)
    // Length calculation assumes single-line tokens; for multi-line tokens this may need revision
    const length = range.start.line === range.end.line
      ? range.end.col - range.start.col
      : 1;  // Fallback for multi-line tokens
    tokens.push({
      line: range.start.line,
      column: range.start.col,
      length,
      type
    });
  }
}

/**
 * Extract hole locations from a compile result for warning markers.
 *
 * This walks through the SURFACE terms (TTerm) to find holes (e.g., ?sorry)
 * and returns their source positions for displaying warning squiggles.
 */
export function extractHoleLocations(result: CompileResult): HoleLocation[] {
  const holes: HoleLocation[] = [];

  for (const block of result.blocks) {
    for (const decl of block.declarations) {
      if (!decl.sourceMap) continue;

      // Process declaration type (surface)
      if (decl.surfaceType) {
        collectHolesFromSurfaceTerm(
          decl.surfaceType,
          decl.sourceMap,
          block.startLine,
          ['type'],
          holes
        );
      }

      // Process declaration value (surface)
      if (decl.surfaceValue) {
        collectHolesFromSurfaceTerm(
          decl.surfaceValue,
          decl.sourceMap,
          block.startLine,
          ['value'],
          holes
        );
      }

      // Process constructors (surface)
      if (decl.surfaceConstructors) {
        for (let i = 0; i < decl.surfaceConstructors.length; i++) {
          collectHolesFromSurfaceTerm(
            decl.surfaceConstructors[i].type,
            decl.sourceMap,
            block.startLine,
            ['constructors', i, 'type'],
            holes
          );
        }
      }
    }
  }

  return holes;
}

/**
 * Walk a surface term (TTerm) and collect hole locations.
 */
function collectHolesFromSurfaceTerm(
  term: TTerm,
  sourceMap: SourceMap,
  blockStartLine: number,
  path: (string | number)[],
  holes: HoleLocation[]
): void {
  switch (term.tag) {
    case 'Hole':
      // Only add explicit user holes (like ?sorry), not wildcards (_)
      // Wildcards are represented as holes with id '_'
      if (term.id !== '_') {
        addHoleLocation(path, sourceMap, blockStartLine, term.id, holes);
      }
      // Also recurse into the hole's type (which might contain more holes)
      collectHolesFromSurfaceTerm(term.type, sourceMap, blockStartLine, [...path, 'type'], holes);
      break;

    case 'Var':
    case 'Const':
    case 'Sort':
      // Leaf nodes - no holes
      break;

    case 'Binder':
      if (term.domain !== undefined) {
        collectHolesFromSurfaceTerm(term.domain, sourceMap, blockStartLine, [...path, 'domain'], holes);
      }
      collectHolesFromSurfaceTerm(term.body, sourceMap, blockStartLine, [...path, 'body'], holes);
      if (term.binderKind.tag === 'BLetTT') {
        collectHolesFromSurfaceTerm(term.binderKind.defVal, sourceMap, blockStartLine, [...path, 'binderKind', 'defVal'], holes);
      }
      break;

    case 'App':
      collectHolesFromSurfaceTerm(term.fn, sourceMap, blockStartLine, [...path, 'fn'], holes);
      collectHolesFromSurfaceTerm(term.arg, sourceMap, blockStartLine, [...path, 'arg'], holes);
      break;

    case 'Annot':
      collectHolesFromSurfaceTerm(term.term, sourceMap, blockStartLine, [...path, 'term'], holes);
      collectHolesFromSurfaceTerm(term.type, sourceMap, blockStartLine, [...path, 'type'], holes);
      break;

    case 'Match':
      collectHolesFromSurfaceTerm(term.scrutinee, sourceMap, blockStartLine, [...path, 'scrutinee'], holes);
      for (let i = 0; i < term.clauses.length; i++) {
        const clause = term.clauses[i];
        collectHolesFromSurfaceTerm(
          clause.rhs,
          sourceMap,
          blockStartLine,
          [...path, 'clauses', i, 'rhs'],
          holes
        );
      }
      break;
  }
}

/**
 * Add a hole location from sourceMap
 */
function addHoleLocation(
  path: (string | number)[],
  sourceMap: SourceMap,
  _blockStartLine: number,  // Unused - sourceMap already has absolute positions
  id: string,
  holes: HoleLocation[]
): void {
  const pathStr = serializePathForLookup(path);
  const range = sourceMap.get(pathStr);
  if (range) {
    // Note: sourceMap positions are already file-absolute (adjusted in elaboration phase)
    holes.push({
      line: range.start.line,
      column: range.start.col,
      endColumn: range.end.col,
      id
    });
  }
}

/**
 * Extract wildcard inlay hints from a compile result.
 *
 * This walks through the compiled declarations, finds PWild patterns in
 * Match expressions, and returns their positions and generated names.
 */
export function extractWildcardInlayHints(result: CompileResult): WildcardInlayHint[] {
  if (!SHOW_WILDCARD_INLAY_HINTS) {
    return [];
  }

  const hints: WildcardInlayHint[] = [];

  for (const block of result.blocks) {
    for (const decl of block.declarations) {
      if (decl.kernelValue) {
        // Start with 'value' to match the path format in elabMap
        collectWildcardsFromTerm(
          decl.kernelValue,
          decl.elabMap,
          decl.sourceMap,
          block.startLine,
          ['value'],
          hints
        );
      }
    }
  }

  return hints;
}

/**
 * Walk a term and collect wildcard hints from Match expressions
 */
function collectWildcardsFromTerm(
  term: TTKTerm,
  elabMap: ElabMap | undefined,
  sourceMap: SourceMap | undefined,
  blockStartLine: number,
  path: (string | number)[],
  hints: WildcardInlayHint[]
): void {
  if (!elabMap || !sourceMap) return;

  switch (term.tag) {
    case 'Match':
      // Collect wildcards from each clause's patterns
      for (let clauseIdx = 0; clauseIdx < term.clauses.length; clauseIdx++) {
        const clause = term.clauses[clauseIdx];
        for (let patIdx = 0; patIdx < clause.patterns.length; patIdx++) {
          collectWildcardsFromPattern(
            clause.patterns[patIdx],
            elabMap,
            sourceMap,
            blockStartLine,
            [...path, 'clauses', clauseIdx, 'patterns', patIdx],
            hints
          );
        }
        // Also recurse into the RHS
        collectWildcardsFromTerm(
          clause.rhs,
          elabMap,
          sourceMap,
          blockStartLine,
          [...path, 'clauses', clauseIdx, 'rhs'],
          hints
        );
      }
      // Recurse into scrutinee
      collectWildcardsFromTerm(
        term.scrutinee,
        elabMap,
        sourceMap,
        blockStartLine,
        [...path, 'scrutinee'],
        hints
      );
      break;

    case 'Binder':
      collectWildcardsFromTerm(term.domain, elabMap, sourceMap, blockStartLine, [...path, 'domain'], hints);
      collectWildcardsFromTerm(term.body, elabMap, sourceMap, blockStartLine, [...path, 'body'], hints);
      if (term.binderKind.tag === 'BLet') {
        collectWildcardsFromTerm(term.binderKind.defVal, elabMap, sourceMap, blockStartLine, [...path, 'binderKind', 'defVal'], hints);
      }
      break;

    case 'App':
      collectWildcardsFromTerm(term.fn, elabMap, sourceMap, blockStartLine, [...path, 'fn'], hints);
      collectWildcardsFromTerm(term.arg, elabMap, sourceMap, blockStartLine, [...path, 'arg'], hints);
      break;

    case 'Annot':
      collectWildcardsFromTerm(term.term, elabMap, sourceMap, blockStartLine, [...path, 'term'], hints);
      collectWildcardsFromTerm(term.type, elabMap, sourceMap, blockStartLine, [...path, 'type'], hints);
      break;

    // Leaf nodes - no recursion
    case 'Hole':
    case 'Meta':
    case 'Var':
    case 'Sort':
    case 'Const':
      break;
  }
}

/**
 * Collect wildcards from a pattern tree
 */
function collectWildcardsFromPattern(
  pattern: TTKPattern,
  elabMap: ElabMap,
  sourceMap: SourceMap,
  _blockStartLine: number,  // Unused - sourceMap already has absolute positions
  path: (string | number)[],
  hints: WildcardInlayHint[]
): void {
  const pathStr = serializePathForLookup(path);

  if (pattern.tag === 'PWild') {
    // Look up the source position via elabMap and sourceMap
    const surfacePathStr = elabMap.get(pathStr);
    if (surfacePathStr) {
      const range = sourceMap.get(surfacePathStr);
      if (range) {
        // Note: sourceMap positions are already file-absolute (adjusted in elaboration phase)
        hints.push({
          line: range.start.line,
          // Position after the underscore (end column of the range)
          column: range.end.col,
          name: pattern.name
        });
      }
    }
  } else if (pattern.tag === 'PCtor') {
    // Recurse into constructor arguments
    for (let i = 0; i < pattern.args.length; i++) {
      collectWildcardsFromPattern(
        pattern.args[i],
        elabMap,
        sourceMap,
        _blockStartLine,
        [...path, 'args', i],
        hints
      );
    }
  }
  // PVar has no sub-patterns
}

/**
 * Serialize a path array to the format used by elabMap
 */
function serializePathForLookup(path: (string | number)[]): string {
  return path.map(seg => {
    if (typeof seg === 'number') {
      return `[${seg}]`;
    }
    return `.${seg}`;
  }).join('').replace(/^\./, '');
}

// ============================================================================
// Parse Function
// ============================================================================

/**
 * Parse TT source code into blocks of declarations.
 *
 * Pipeline:
 * 1. Group source into blocks by indentation
 * 2. Parse each block
 *
 * @param source - The full source code
 * @returns ParseResult with parsed blocks
 */
export function parseTTSource(source: string): ParseResult {
  const sourceBlocks = groupByIndentation(source);
  const parsedBlocks: ParsedBlock[] = [];
  let totalErrors = 0;

  // Accumulate declarations for pattern matching detection
  let allPreviousDeclarations: ParsedDeclaration[] = [];

  for (const block of sourceBlocks) {
    // Handle comment blocks
    if (block.isComment) {
      parsedBlocks.push({
        kind: 'comment',
        sourceLines: block.lines,
        startLine: block.startLine
      });
      continue;
    }

    const blockSource = block.lines.join('\n');
    const parser = new Parser();

    // Parse
    let declarations: ParsedDeclaration[] = [];
    let sourceMaps: SourceMap[] = [];

    try {
      const declsWithSource = parser.parseDeclarationsWithSource(blockSource, allPreviousDeclarations);

      declarations = declsWithSource.map(d => d.decl);
      sourceMaps = declsWithSource.map(d => d.sourceMap);
      allPreviousDeclarations = [...allPreviousDeclarations, ...declarations];
    } catch (e) {
      let parseErrors: ParseError[];
      if (e instanceof Error && 'errors' in e) {
        parseErrors = (e as any).errors as ParseError[];
        parseErrors = parseErrors.map(err => ({
          ...err,
          line: err.line + block.startLine - 1
        }));
      } else {
        parseErrors = [{
          name: 'ParseError',
          message: e instanceof Error ? e.message : String(e),
          line: block.startLine,
          col: 1
        }];
      }
      totalErrors += parseErrors.length;
      parsedBlocks.push({
        kind: 'error',
        errors: parseErrors,
        sourceLines: block.lines,
        startLine: block.startLine
      });
      continue;
    }

    parsedBlocks.push({
      kind: 'declarations',
      declarations,
      sourceMaps,
      sourceLines: block.lines,
      startLine: block.startLine
    });
  }

  return { blocks: parsedBlocks, totalErrors };
}

// ============================================================================
// Elaboration Function
// ============================================================================

/**
 * Options for elaboration phases
 */
export interface ElabOptions {
  /** Whether to elaborate term values (default: true). Set to false for phase 1. */
  elabValues?: boolean;
}

/**
 * Elaborate parsed TT to kernel terms (TTK).
 *
 * Pipeline:
 * 1. Name resolution (validate all identifiers are defined)
 * 2. Pattern resolution (resolve PCtor vs PVar in patterns)
 * 3. Elaborate TT -> TTK
 *
 * @param parseResult - Result from parseTTSource
 * @param _initialContext - Optional initial typing context (for imports/prelude)
 * @param options - Elaboration options (e.g., whether to elaborate values)
 * @returns ElabResult with elaborated blocks
 */
export function elabTT(parseResult: ParseResult, _initialContext: TTKContext = [], options: ElabOptions = {}): ElabResult {
  const { elabValues = true } = options;
  const elabBlocks: ElabBlock[] = [];

  // Collect all declarations from all blocks for resolution
  let allDeclarations: ParsedDeclaration[] = [];
  for (const block of parseResult.blocks) {
    if (block.kind === 'declarations') {
      allDeclarations = [...allDeclarations, ...block.declarations];
    }
  }

  // Phase 1: Name resolution
  let symbolContext: SymbolContext = emptySymbolContext();
  for (const decl of allDeclarations) {
    const result = validateDeclarations([decl], symbolContext);
    if (result.success) {
      symbolContext = result.value;
    }
    // Note: We could collect resolution errors here and convert blocks to error blocks
    // For now, we continue and let type checking catch unresolved names
  }

  // Phase 2: Pattern resolution
  allDeclarations = resolvePatternsInDeclarations(allDeclarations, symbolContext);

  // Build a map from declaration name to resolved declaration
  const resolvedDeclMap = new Map<string, ParsedDeclaration>();
  for (const decl of allDeclarations) {
    if (decl.name) {
      resolvedDeclMap.set(decl.name, decl);
    }
  }

  for (const block of parseResult.blocks) {
    // Pass through comment blocks
    if (block.kind === 'comment') {
      elabBlocks.push({
        kind: 'comment',
        sourceLines: block.sourceLines,
        startLine: block.startLine
      });
      continue;
    }

    // Pass through error blocks
    if (block.kind === 'error') {
      elabBlocks.push({
        kind: 'error',
        errors: block.errors,
        sourceLines: block.sourceLines,
        startLine: block.startLine
      });
      continue;
    }

    // Elaborate declaration blocks
    const elabDeclarations: ElabDeclaration[] = [];

    for (let declIndex = 0; declIndex < block.declarations.length; declIndex++) {
      const origDecl = block.declarations[declIndex];
      // Adjust sourceMap to file-absolute positions
      const sourceMap = adjustSourceMapToAbsolute(block.sourceMaps[declIndex], block.startLine);
      // Use resolved declaration if available, otherwise fall back to original
      const decl = (origDecl.name && resolvedDeclMap.get(origDecl.name)) || origDecl;
      const elabMap: ElabMap = new Map();

      let kernelType: TTKTerm | undefined;
      let kernelValue: TTKTerm | undefined;
      let kernelConstructors: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }> | undefined;

      try {
        // Elaborate type
        if (decl.type) {
          const typePath: IndexPath = [{ kind: 'field', name: 'type' }];
          kernelType = elabToKernelWithMap(decl.type, elabMap, typePath, typePath);
        }

        // Elaborate value (only if elabValues is true)
        if (elabValues && decl.value) {
          const valuePath: IndexPath = [{ kind: 'field', name: 'value' }];
          // Extract namedArgMap and totalArity from type for pattern validation and reordering
          const namedArgMap = decl.type ? extractNamedArgMap(decl.type) : undefined;
          const totalArity = decl.type ? countParameters(decl.type) : undefined;
          kernelValue = elabToKernelWithMap(decl.value, elabMap, valuePath, valuePath, namedArgMap, undefined, totalArity);
        }

        // Elaborate constructors
        if (decl.constructors) {
          // Extract the inductive type's named arg map and arity so constructor types
          // can reference the inductive type with named arguments
          const inductiveNamedArgMap = decl.type ? extractNamedArgMap(decl.type) : undefined;
          const inductiveTotalArity = decl.type ? countParameters(decl.type) : undefined;

          // Create a lookup that includes this inductive type's named arg info
          // This is needed because the inductive type isn't registered in definitions yet
          const ctorAppLookup = decl.name && inductiveNamedArgMap && inductiveNamedArgMap.size > 0
            ? (name: string) => name === decl.name ? { namedArgMap: inductiveNamedArgMap, totalArity: inductiveTotalArity } : undefined
            : undefined;

          kernelConstructors = decl.constructors.map((ctor, ctorIndex) => {
            const ctorTypePath: IndexPath = [
              { kind: 'field', name: 'constructors' },
              { kind: 'array', index: ctorIndex },
              { kind: 'field', name: 'type' }
            ];
            // Extract namedArgMap from the constructor's surface type
            const ctorNamedArgMap = extractNamedArgMap(ctor.type);
            return {
              name: ctor.name,
              type: elabToKernelWithMap(ctor.type, elabMap, ctorTypePath, ctorTypePath, undefined, ctorAppLookup),
              namedArgMap: ctorNamedArgMap.size > 0 ? ctorNamedArgMap : undefined,
            };
          });
        }

        elabDeclarations.push({
          name: decl.name,
          kind: decl.kind === 'inductive' ? 'inductive' : 'term',
          // Surface terms for syntax highlighting
          surfaceType: decl.type,
          surfaceValue: decl.value,
          surfaceConstructors: decl.constructors,
          // Kernel terms for type checking
          kernelType,
          kernelValue,
          kernelConstructors,
          elabMap,
          sourceMap
        });
      } catch (e) {
        // Elaboration error - record the error for later reporting
        const errorMessage = e instanceof Error ? e.message : String(e);
        // Extract surfacePath if this is a NamedArgElabError
        const elabErrorPath = e instanceof NamedArgElabError && e.surfacePath
          ? serializeIndexPath(e.surfacePath)
          : undefined;
        elabDeclarations.push({
          name: decl.name,
          kind: decl.kind === 'inductive' ? 'inductive' : 'term',
          surfaceType: decl.type,
          surfaceValue: decl.value,
          surfaceConstructors: decl.constructors,
          elabMap,
          sourceMap,
          elabError: errorMessage,
          elabErrorPath,
        });
      }
    }

    elabBlocks.push({
      kind: 'declarations',
      declarations: elabDeclarations,
      sourceLines: block.sourceLines,
      startLine: block.startLine
    });
  }

  return { blocks: elabBlocks };
}

/**
 * Collect constructor param names from checked inductive declarations.
 * This should be called after phase 1 type checking.
 */
function collectConstructorParamNames(compiledBlocks: CompiledBlock[]): ConstructorParamNames {
  const result: ConstructorParamNames = new Map();

  for (const block of compiledBlocks) {
    for (const decl of block.declarations) {
      if (decl.kind === 'inductive' && decl.checkSuccess && decl.kernelConstructors) {
        const ctorParamNames = buildConstructorParamNames(decl.kernelConstructors);
        for (const [ctorName, paramInfo] of ctorParamNames) {
          result.set(ctorName, paramInfo);
        }
      }
    }
  }

  return result;
}

// ============================================================================
// Type Checking Functions
// ============================================================================

/**
 * Result of checking a single declaration
 */
interface CheckDeclarationResult {
  compiled: CompiledDeclaration;
  newDefinitions: DefinitionsMap;
  errorCount: number;
}

/**
 * Check a single declaration and return the compiled result with updated context.
 */
function checkDeclaration(
  decl: ElabDeclaration,
  definitions: DefinitionsMap,
): CheckDeclarationResult {
  let checkSuccess = true;
  const checkErrors: TCEnvError[] = [];
  let newDefinitions = definitions;
  let errorCount = 0;
  let indexPositions: number[] | undefined;
  let totalityResult: TotalityResult | undefined;
  let checkedValue: TTKTerm | undefined;
  let zonkedConstructors: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }> | undefined;

  // Check for elaboration errors first (e.g., named argument errors)
  if (decl.elabError) {
    checkSuccess = false;
    // Create TCEnv with the error path so the error points to the correct source location
    const errorPath = decl.elabErrorPath ? deserializeIndexPath(decl.elabErrorPath) : [];
    const env = createTCEnv({ definitions, indexPath: errorPath, options: { mode: 'check' } });
    const error = TCEnvError.create(decl.elabError, env);
    checkErrors.push(error);
    errorCount = 1;
  } else if (decl.kind === 'inductive') {
    const result = checkInductiveTypeDeclaration(decl, definitions);
    if (result.success) {
      newDefinitions = result.definitions;
      indexPositions = result.indexPositions;
      zonkedConstructors = result.zonkedConstructors;
    } else {
      checkSuccess = false;
      checkErrors.push(...result.errors);
      errorCount = result.errors.length;
    }
  } else if (decl.kind === 'term') {
    const result = checkTermDeclaration(decl, definitions);
    if (result.success) {
      newDefinitions = result.definitions;
      totalityResult = result.totalityResult;
      checkedValue = result.checkedValue;
    } else {
      checkSuccess = false;
      checkErrors.push(...result.errors);
      errorCount = result.errors.length;
      // Still capture totalityResult even on failure (for UI visualization)
      totalityResult = result.totalityResult;
    }
  } else {
    checkSuccess = false;
    const error = TCEnvError.create('Declaration is not an inductive or term', createTCEnv({ definitions, options: { mode: 'check' } }));
    checkErrors.push(error);
    errorCount = 1;
  }

  // Build compiled declaration with pretty-printed versions
  // Use zonkedConstructors (with solved metas) if available, otherwise fall back to elaborated kernelConstructors
  const effectiveConstructors = zonkedConstructors ?? decl.kernelConstructors;
  const compiled: CompiledDeclaration = {
    name: decl.name,
    kind: decl.kind,
    // Surface terms (for syntax highlighting)
    surfaceType: decl.surfaceType,
    surfaceValue: decl.surfaceValue,
    surfaceConstructors: decl.surfaceConstructors,
    // Kernel terms
    kernelType: decl.kernelType,
    kernelValue: decl.kernelValue,
    kernelConstructors: effectiveConstructors,
    indexPositions,
    prettyType: decl.kernelType ? prettyPrintTTK(decl.kernelType) : undefined,
    // Use checkedValue (with solutions) if available, otherwise fall back to elaborated kernelValue
    // Use formatted pretty print for better readability of match/let expressions
    prettyValue: (checkedValue ?? decl.kernelValue) ? prettyPrintFormatted(checkedValue ?? decl.kernelValue!) : undefined,
    prettyConstructors: effectiveConstructors?.map(c => ({
      name: c.name,
      prettyType: prettyPrintTTK(c.type)
    })),
    checkSuccess,
    checkErrors,
    totalityResult,
    elabMap: decl.elabMap,
    sourceMap: decl.sourceMap,
    elabErrorPath: decl.elabErrorPath
  };

  return { compiled, newDefinitions, errorCount };
}

function checkInductiveTypeDeclaration(
  decl: ElabDeclaration,
  definitions: DefinitionsMap,
): { success: false, errors: TCEnvError[] } | { success: true, definitions: DefinitionsMap, indexPositions: number[], zonkedConstructors: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }> } {
  if (decl.kind !== 'inductive') {
    return failCheck('Declaration is not an inductive type', createTCEnv({ definitions, options: { mode: 'check' } }))
  }

  if (!decl.kernelType) {
    return failCheck('Inductive type declaration is ill-formed', createTCEnv({ definitions, options: { mode: 'check' } }))
  }
  if (!decl.kernelConstructors) {
    return failCheck('Inductive type declaration is ill-formed', createTCEnv({ definitions, options: { mode: 'check' } }))
  }

  // Extract namedArgMap from the surface type for the inductive type itself
  const inductiveNamedArgMap = decl.surfaceType ? extractNamedArgMap(decl.surfaceType) : undefined;

  const result = checkInductiveDeclaration(
    decl.name || 'anonymous',
    decl.kernelType,
    decl.kernelConstructors,
    definitions,
    inductiveNamedArgMap && inductiveNamedArgMap.size > 0 ? inductiveNamedArgMap : undefined
  );
  if (!result.success) {
    return result
  } else {
    return {
      success: true,
      definitions: result.newDefinitions,
      indexPositions: result.indexPositions,
      zonkedConstructors: result.zonkedConstructors,
    }
  }
}

function failCheck(message: string, env: TCEnv<unknown>): { success: false, errors: TCEnvError[] } {
  return {
    success: false,
    errors: [TCEnvError.create(message, env)],
  }
}

function checkTermDeclaration(
  decl: ElabDeclaration,
  definitions: DefinitionsMap,
): { success: false, errors: TCEnvError[], totalityResult?: TotalityResult } | { success: true, definitions: DefinitionsMap, checkedValue: TTKTerm, totalityResult?: TotalityResult } {
  if (!decl.name) {
    return failCheck('Term declaration is ill-formed (no name)', createTCEnv({ definitions, options: { mode: 'check' } }))
  }

  let env = createTCEnv({ definitions, options: { mode: 'check' } })

  if (decl.kind !== 'term') {
    return failCheck('Declaration is not a term', env)
  }

  if (!decl.kernelType) {
    return failCheck('Term declaration is ill-formed', env)
  }

  try {
    // Create a placeholder kernel value - actual clause elaboration happens in checkTermValue
    // following the flow: for each clause, elaborate LHS, unify, then elaborate RHS
    const placeholderValue: TTKTerm = {
      tag: 'Match',
      scrutinee: { tag: 'Hole', id: '_scrutinee' },
      clauses: []
    };

    let termEnv = env.withValue<TermDefinition>({
      name: decl.name,
      type: decl.kernelType,
      value: placeholderValue,
    });

    // Check for duplicate names
    validateTermNameNotDefined(termEnv);

    const sigResult = inferType(termEnv.inTermType());
    // Solve meta constraints before checking for unsolved metas
    const solvedSigResult = sigResult.solveMetasAndConstraints({ liftMetasToFullContext: false });
    const unsolvedSigMetas = Array.from(solvedSigResult.metaVars.values()).filter(m => !m.solution);
    if (unsolvedSigMetas.length > 0) {
      return {
        success: false, errors: [
          TCEnvError.create('Checking the signature produced unsolved metas.', env)
        ]
      }
    }

    // Extract named arg info from type for use in definition and pattern elaboration
    const namedArgMap = decl.surfaceType ? extractNamedArgMap(decl.surfaceType) : undefined;
    const totalArity = decl.surfaceType ? countParameters(decl.surfaceType) : undefined;

    // Add to context for subsequent declarations, including namedArgMap for lookup
    if (decl.name) {
      termEnv = addDefinitionInTCEnv(termEnv, decl.name, decl.kernelType, namedArgMap);
    }

    // Handle #absurd clauses from surface value
    // These are filtered out during elaboration, so we validate them here
    const absurdClauseErrors: TCEnvError[] = [];
    const annotatedAbsurdClauses: number[] = [];

    if (decl.surfaceValue?.tag === 'Match') {
      for (let i = 0; i < decl.surfaceValue.clauses.length; i++) {
        const clause = decl.surfaceValue.clauses[i];
        if (clause.rhs.tag === 'AbsurdMarker') {
          // First validate pattern structure - check for positional patterns in implicit positions
          // This is the same validation done in checkTermClause via reorderPatterns
          if (namedArgMap && namedArgMap.size > 0) {
            const reorderResult = reorderPatterns(clause.patterns, namedArgMap, clause.namedPatterns, totalArity);
            if ('error' in reorderResult && reorderResult.error !== undefined) {
              absurdClauseErrors.push(TCEnvError.create(reorderResult.error, termEnv));
              continue; // Skip absurdity check if pattern structure is invalid
            }
          }

          // Elaborate the patterns to TTKPattern for validation
          const kernelPatterns = clause.patterns.map(p => elabPatternToKernel(p));
          const patternsEnv = termEnv.withValue(kernelPatterns);

          // First try basic absurdity check
          let isAbsurd = arePatternsAbsurd(decl.name, patternsEnv, decl.kernelType);

          // If basic check passes (not absurd), try Agda-style recursive splitting
          // This handles cases like Fin Zero where the type is uninhabited
          if (!isAbsurd) {
            isAbsurd = tryCaseSplitsInSearchOfAbsurdity(
              decl.name,
              kernelPatterns,
              decl.kernelType,
              termEnv.definitions,
              termEnv
            );
          }

          if (isAbsurd) {
            // Valid #absurd annotation - track for totality display
            annotatedAbsurdClauses.push(i);
          } else {
            // Patterns are NOT absurd but #absurd was used - error
            absurdClauseErrors.push(TCEnvError.create(
              `#absurd used but case is not absurd: patterns can be inhabited`,
              termEnv
            ));
          }
        }
      }
    }

    if (absurdClauseErrors.length > 0) {
      return { success: false, errors: absurdClauseErrors };
    }

    // Handle non-Match values (simple definitions like `test = True`)
    // These don't involve pattern matching, so we elaborate and check directly
    if (decl.surfaceValue && decl.surfaceValue.tag !== 'Match') {
      const valuePath: IndexPath = [{ kind: 'field', name: 'value' }];
      const appNamedArgLookup = createNamedArgInfoLookup(termEnv.definitions);
      const kernelValue = elabToKernelWithMap(
        decl.surfaceValue,
        decl.elabMap ?? new Map(),
        valuePath,
        valuePath,
        namedArgMap,
        appNamedArgLookup
      );

      try {
        const valueEnv = termEnv.withValue(kernelValue);
        const result = checkType(valueEnv, decl.kernelType);
        // Solve meta constraints before checking for unsolved metas
        const solvedResult = result.solveMetasAndConstraints({ liftMetasToFullContext: false });
        // Check for UNSOLVED metas in the value (solved metas have a 'solution' property)
        const unsolvedMetas = Array.from(solvedResult.metaVars.values()).filter(m => !m.solution);
        if (unsolvedMetas.length > 0) {
          return {
            success: false, errors: [
              TCEnvError.create('Checking the value produced unsolved metas.', termEnv)
            ]
          };
        }
        // Zonk the value to substitute solved metas with their solutions
        const zonkedValue = solvedResult.zonkTerm(solvedResult.value);
        const resultEnv = setDefinitionValueInTCEnv(termEnv, decl.name, zonkedValue);
        return { success: true, definitions: resultEnv.definitions, checkedValue: zonkedValue };
      } catch (e) {
        if (e instanceof TCEnvError) {
          return { success: false, errors: [e] };
        }
        return { success: false, errors: [TCEnvError.create(String(e), termEnv)] };
      }
    }

    // Get surface clauses for incremental elaboration (pattern matching case)
    const surfaceClauses = decl.surfaceValue?.tag === 'Match'
      ? decl.surfaceValue.clauses.filter(c => c.rhs.tag !== 'AbsurdMarker')
      : [];

    const result = checkTermValue(
      decl.name,
      termEnv,
      decl.kernelType,
      surfaceClauses,
      decl.elabMap ?? new Map(),
      namedArgMap,
      totalArity,
      annotatedAbsurdClauses
    );
    if (!result.success) {
      return { success: false, errors: result.errors, totalityResult: result.totalityResult }
    }

    const resultEnv = setDefinitionValueInTCEnv(termEnv, decl.name, result.checkedValue);
    return { success: true, definitions: resultEnv.definitions, checkedValue: result.checkedValue, totalityResult: result.totalityResult }
  } catch (e) {
    if (e instanceof TCEnvError) {
      return {
        success: false,
        errors: [e],
      }
    } else {
      return {
        success: false,
        errors: [TCEnvError.create(e instanceof Error ? e.message : String(e), env)],
      }
    }
  }
}

/**
 * Result of checking a single block
 */
interface CheckBlockResult {
  compiled: CompiledBlock;
  newDefinitions: DefinitionsMap;
  errorCount: number;
}

/**
 * Check a single block and return the compiled result with updated context.
 */
function checkBlock(
  block: ElabBlock,
  blockIndex: number,
  definitions: DefinitionsMap,
): CheckBlockResult {
  // Handle comment blocks
  if (block.kind === 'comment') {
    return {
      compiled: {
        blockIndex,
        sourceLines: block.sourceLines,
        startLine: block.startLine,
        parseSuccess: true,
        parseErrors: [],
        nameResolutionSuccess: true,
        nameResolutionErrors: [],
        declarations: [],
        isComment: true
      },
      newDefinitions: definitions,
      errorCount: 0
    };
  }

  // Handle error blocks
  if (block.kind === 'error') {
    return {
      compiled: {
        blockIndex,
        sourceLines: block.sourceLines,
        startLine: block.startLine,
        parseSuccess: false,
        parseErrors: block.errors,
        nameResolutionSuccess: true,
        nameResolutionErrors: [],
        declarations: [],
        isComment: false
      },
      newDefinitions: definitions,
      errorCount: 0
    };
  }

  // Handle declaration blocks - type check each declaration
  const compiledDeclarations: CompiledDeclaration[] = [];
  let currentDefinitions = definitions;
  let totalErrors = 0;

  for (const decl of block.declarations) {
    const result = checkDeclaration(decl, currentDefinitions);
    compiledDeclarations.push(result.compiled);
    currentDefinitions = result.newDefinitions;
    totalErrors += result.errorCount;
  }

  return {
    compiled: {
      blockIndex,
      sourceLines: block.sourceLines,
      startLine: block.startLine,
      parseSuccess: true,
      parseErrors: [],
      nameResolutionSuccess: true,
      nameResolutionErrors: [],
      declarations: compiledDeclarations,
      isComment: false
    },
    newDefinitions: currentDefinitions,
    errorCount: totalErrors
  };
}

/**
 * Result of checking all blocks
 */
interface CheckBlocksResult {
  blocks: CompiledBlock[];
  totalCheckErrors: number;
  finalDefinitions: DefinitionsMap;
}

/**
 * Options for type checking phases
 */
interface CheckOptions {
  /** Only check declarations of this kind (default: check all) */
  onlyKind?: 'inductive' | 'term';
  /** Existing compiled blocks to merge with (for phase 2) */
  existingBlocks?: CompiledBlock[];
}

/**
 * Check all elaborated blocks and return compiled blocks with type check results.
 */
function checkBlocks(
  _parseResult: ParseResult,
  elabResult: ElabResult,
  initialDefinitions: DefinitionsMap = createDefinitionsMap(),
  options: CheckOptions = {},
): CheckBlocksResult {
  const { onlyKind, existingBlocks } = options;
  const compiledBlocks: CompiledBlock[] = [];
  let currentDefinitions = initialDefinitions;
  let totalCheckErrors = 0;

  for (let blockIndex = 0; blockIndex < elabResult.blocks.length; blockIndex++) {
    const block = elabResult.blocks[blockIndex];

    // If we're filtering by kind, we need to handle it specially
    if (onlyKind && block.kind === 'declarations') {
      // Filter declarations to only include the specified kind
      const filteredDecls = block.declarations.filter(d => d.kind === onlyKind);

      if (filteredDecls.length === 0) {
        // No declarations of this kind - use existing block or create placeholder
        if (existingBlocks && existingBlocks[blockIndex]) {
          compiledBlocks.push(existingBlocks[blockIndex]);
        } else {
          compiledBlocks.push({
            blockIndex,
            sourceLines: block.sourceLines,
            startLine: block.startLine,
            parseSuccess: true,
            parseErrors: [],
            nameResolutionSuccess: true,
            nameResolutionErrors: [],
            declarations: [],
            isComment: false
          });
        }
        continue;
      }

      // Create a filtered elab block
      const filteredBlock: ElabBlock = {
        kind: 'declarations',
        declarations: filteredDecls,
        sourceLines: block.sourceLines,
        startLine: block.startLine,
      };

      const result = checkBlock(filteredBlock, blockIndex, currentDefinitions);

      // Merge with existing blocks if provided (for phase 2, merge with phase 1 results)
      if (existingBlocks && existingBlocks[blockIndex]) {
        const existingDecls = existingBlocks[blockIndex].declarations;
        // Merge: keep existing checked declarations, add newly checked ones
        const mergedDecls: CompiledDeclaration[] = [];

        // Add existing declarations that weren't in this phase
        for (const existingDecl of existingDecls) {
          if (existingDecl.kind !== onlyKind) {
            mergedDecls.push(existingDecl);
          }
        }
        // Add newly checked declarations
        mergedDecls.push(...result.compiled.declarations);

        result.compiled.declarations = mergedDecls;
      }

      compiledBlocks.push(result.compiled);
      currentDefinitions = result.newDefinitions;
      totalCheckErrors += result.errorCount;
    } else {
      // No filtering - check all declarations
      const result = checkBlock(block, blockIndex, currentDefinitions);
      compiledBlocks.push(result.compiled);
      currentDefinitions = result.newDefinitions;
      totalCheckErrors += result.errorCount;
    }
  }

  return {
    blocks: compiledBlocks,
    totalCheckErrors,
    finalDefinitions: currentDefinitions
  };
}

// ============================================================================
// Main Compile Function
// ============================================================================

/**
 * Result of processing a single declaration
 */
interface ProcessDeclarationResult {
  success: boolean;
  compiled: CompiledDeclaration;
  newDefinitions: DefinitionsMap;
  errorCount: number;
}

/**
 * Create a CompiledDeclaration from the given components
 */
function createCompiledDeclaration(
  decl: ParsedDeclaration,
  kernelType: TTKTerm | undefined,
  kernelValue: TTKTerm | undefined,
  kernelConstructors: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }> | undefined,
  elabMap: ElabMap,
  sourceMap: SourceMap,
  checkSuccess: boolean,
  checkErrors: TCEnvError[],
  totalityResult?: TotalityResult,
  indexPositions?: number[],
  elabErrorPath?: string,
): CompiledDeclaration {
  return {
    name: decl.name,
    kind: decl.kind === 'inductive' ? 'inductive' : 'term',
    surfaceType: decl.type,
    surfaceValue: decl.value,
    surfaceConstructors: decl.constructors,
    kernelType,
    kernelValue,
    kernelConstructors,
    indexPositions,
    prettyType: kernelType ? prettyPrintTTK(kernelType) : undefined,
    prettyValue: kernelValue ? prettyPrintFormatted(kernelValue) : undefined,
    prettyConstructors: kernelConstructors?.map(c => ({
      name: c.name,
      prettyType: prettyPrintTTK(c.type)
    })),
    checkSuccess,
    checkErrors,
    totalityResult,
    elabMap,
    sourceMap,
    elabErrorPath,
  };
}

/**
 * Create an error result from an elaboration error
 */
function createElabErrorResult(
  e: unknown,
  decl: ParsedDeclaration,
  sourceMap: SourceMap,
  elabMap: ElabMap,
  definitions: DefinitionsMap,
): ProcessDeclarationResult {
  const errorMessage = e instanceof Error ? e.message : String(e);
  const elabErrorPath = e instanceof NamedArgElabError && e.surfacePath
    ? serializeIndexPath(e.surfacePath)
    : undefined;
  const errorPath = elabErrorPath ? deserializeIndexPath(elabErrorPath) : [];
  const env = createTCEnv({ definitions, indexPath: errorPath, options: { mode: 'check' } });
  const error = TCEnvError.create(errorMessage, env);

  return {
    success: false,
    compiled: createCompiledDeclaration(
      decl, undefined, undefined, undefined, elabMap, sourceMap,
      false, [error], undefined, undefined, elabErrorPath
    ),
    newDefinitions: definitions,
    errorCount: 1
  };
}

/**
 * Process a single inductive declaration: elaborate and check.
 *
 * Following the flow:
 * 1. Elaborate & check signature. Add name+sig to context.
 * 2. Elab+Check each constructor in that extended context.
 * 3. Add all constructors to the context.
 * 4. Check sizing rules on indices and check for positive definiteness in ctors.
 *    (Return original context if any failure, along with errors)
 */
function processInductiveDeclaration(
  decl: ParsedDeclaration,
  sourceMap: SourceMap,
  definitions: DefinitionsMap,
): ProcessDeclarationResult {
  const elabMap: ElabMap = new Map();

  // Elaborate signature
  let kernelType: TTKTerm | undefined;
  if (decl.type) {
    try {
      const typePath: IndexPath = [{ kind: 'field', name: 'type' }];
      kernelType = elabToKernelWithMap(decl.type, elabMap, typePath, typePath);
    } catch (e) {
      return createElabErrorResult(e, decl, sourceMap, elabMap, definitions);
    }
  }

  // Extract inductive's named arg map and arity for constructor elaboration
  const inductiveNamedArgMap = decl.type ? extractNamedArgMap(decl.type) : undefined;
  const inductiveTotalArity = decl.type ? countParameters(decl.type) : undefined;
  const ctorAppLookup = decl.name && inductiveNamedArgMap && inductiveNamedArgMap.size > 0
    ? (name: string) => name === decl.name ? { namedArgMap: inductiveNamedArgMap, totalArity: inductiveTotalArity } : undefined
    : undefined;

  // Elaborate constructors
  let kernelConstructors: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }> | undefined;
  if (decl.constructors) {
    kernelConstructors = [];
    for (let ctorIndex = 0; ctorIndex < decl.constructors.length; ctorIndex++) {
      const ctor = decl.constructors[ctorIndex];
      try {
        const ctorTypePath: IndexPath = [
          { kind: 'field', name: 'constructors' },
          { kind: 'array', index: ctorIndex },
          { kind: 'field', name: 'type' }
        ];
        const ctorKernelType = elabToKernelWithMap(ctor.type, elabMap, ctorTypePath, ctorTypePath, undefined, ctorAppLookup);
        // Extract namedArgMap from the constructor's surface type
        const ctorNamedArgMap = extractNamedArgMap(ctor.type);
        kernelConstructors.push({
          name: ctor.name,
          type: ctorKernelType,
          namedArgMap: ctorNamedArgMap.size > 0 ? ctorNamedArgMap : undefined
        });
      } catch (e) {
        return createElabErrorResult(e, decl, sourceMap, elabMap, definitions);
      }
    }
  }

  // Validate we have required components
  if (!kernelType || !kernelConstructors) {
    const env = createTCEnv({ definitions, options: { mode: 'check' } });
    const error = TCEnvError.create('Inductive type declaration is ill-formed', env);
    return {
      success: false,
      compiled: createCompiledDeclaration(
        decl, kernelType, undefined, kernelConstructors, elabMap, sourceMap,
        false, [error]
      ),
      newDefinitions: definitions,
      errorCount: 1
    };
  }

  // Check the inductive declaration
  // (This handles: signature check, add to context, constructor checks, sizing, positivity)
  const result = checkInductiveDeclaration(
    decl.name || 'anonymous',
    kernelType,
    kernelConstructors,
    definitions,
    inductiveNamedArgMap
  );

  if (!result.success) {
    // Return original context on failure
    return {
      success: false,
      compiled: createCompiledDeclaration(
        decl, kernelType, undefined, kernelConstructors, elabMap, sourceMap,
        false, result.errors
      ),
      newDefinitions: definitions,
      errorCount: result.errors.length
    };
  }

  return {
    success: true,
    compiled: createCompiledDeclaration(
      // Use zonkedConstructors (with solved metas) instead of the original kernelConstructors
      decl, kernelType, undefined, result.zonkedConstructors, elabMap, sourceMap,
      true, [], undefined, result.indexPositions
    ),
    newDefinitions: result.newDefinitions,
    errorCount: 0
  };
}

/**
 * Process a single term declaration: elaborate and check.
 *
 * Following the flow:
 * a. Elaborate, check, and solve metas in signature.
 * b. For each clause: elaborate the LHS args, unify the LHS args & constraints solve,
 *    then elaborate the RHS under the context created from LHS elab, and check RHS
 *    under refined return type (from LHS unification).
 * c. Run totality checker on checked clauses.
 * d. Run safe recursion checker on checked clauses.
 * e. Add to context if no errors.
 */
function processTermDeclaration(
  decl: ParsedDeclaration,
  sourceMap: SourceMap,
  definitions: DefinitionsMap,
): ProcessDeclarationResult {
  const elabMap: ElabMap = new Map();

  // a. Elaborate signature
  let kernelType: TTKTerm | undefined;
  if (decl.type) {
    try {
      const typePath: IndexPath = [{ kind: 'field', name: 'type' }];
      // Pass appNamedArgLookup so named arguments in the type signature can be resolved
      const appNamedArgLookup = createNamedArgInfoLookup(definitions);
      kernelType = elabToKernelWithMap(decl.type, elabMap, typePath, typePath, undefined, appNamedArgLookup);
    } catch (e) {
      return createElabErrorResult(e, decl, sourceMap, elabMap, definitions);
    }
  }

  // NOTE: We do NOT elaborate the value here. Per step (b) above, clause elaboration
  // happens incrementally in checkTermDeclaration: for each clause, we elaborate
  // LHS patterns, unify & solve, THEN elaborate RHS under the resulting context.

  // Create ElabDeclaration for checkTermDeclaration
  const elabDecl: ElabDeclaration = {
    name: decl.name,
    kind: 'term',
    surfaceType: decl.type,
    surfaceValue: decl.value,
    kernelType,
    // kernelValue is NOT set here - elaboration happens clause-by-clause in checkTermDeclaration
    elabMap,
    sourceMap
  };

  // Check the term declaration
  // (This handles: signature check & meta solving, clause checking with LHS/RHS,
  //  totality, recursion, and adds to context if no errors)
  const result = checkTermDeclaration(elabDecl, definitions);

  if (!result.success) {
    return {
      success: false,
      compiled: createCompiledDeclaration(
        decl, kernelType, undefined, undefined, elabMap, sourceMap,
        false, result.errors, result.totalityResult
      ),
      newDefinitions: definitions,
      errorCount: result.errors.length
    };
  }

  return {
    success: true,
    compiled: createCompiledDeclaration(
      decl, kernelType, result.checkedValue, undefined, elabMap, sourceMap,
      true, [], result.totalityResult
    ),
    newDefinitions: result.definitions,
    errorCount: 0
  };
}

/**
 * Compile TT source code to elaborated kernel terms.
 *
 * Pipeline:
 * 1. Parse the source file
 * 2. For each block, for each definition...
 * 3. If it is an inductive type def: elaborate & check signature, add name+sig to context,
 *    elab+check each constructor, add all constructors to context, check sizing/positivity
 * 4. If it is a term: elaborate & check signature with meta solving, for each clause
 *    elaborate LHS, unify, elaborate RHS under LHS context, check RHS, then run
 *    totality and recursion checkers, add to context if no errors
 *
 * @param source - The full source code
 * @returns CompileResult with elaborated declarations
 */
export function compileTTFromText(source: string): CompileResult {
  // Reset wildcard counter for fresh compilation
  resetWildcardCounter();

  // 1. Parse the source file
  const parseResult = parseTTSource(source);

  // 2. For each block, for each definition...
  // We build context incrementally as we process declarations
  let definitions = createDefinitionsMap();
  let constructorParamNames: ConstructorParamNames = new Map();
  let symbolContext: SymbolContext = emptySymbolContext();
  const compiledBlocks: CompiledBlock[] = [];
  let totalCheckErrors = 0;
  let totalNameErrors = 0;

  for (let blockIndex = 0; blockIndex < parseResult.blocks.length; blockIndex++) {
    const block = parseResult.blocks[blockIndex];

    // Handle comment blocks
    if (block.kind === 'comment') {
      compiledBlocks.push({
        blockIndex,
        sourceLines: block.sourceLines,
        startLine: block.startLine,
        parseSuccess: true,
        parseErrors: [],
        nameResolutionSuccess: true,
        nameResolutionErrors: [],
        declarations: [],
        isComment: true
      });
      continue;
    }

    // Handle parse error blocks
    if (block.kind === 'error') {
      compiledBlocks.push({
        blockIndex,
        sourceLines: block.sourceLines,
        startLine: block.startLine,
        parseSuccess: false,
        parseErrors: block.errors,
        nameResolutionSuccess: true,
        nameResolutionErrors: [],
        declarations: [],
        isComment: false
      });
      continue;
    }

    // Process declarations in this block
    const compiledDecls: CompiledDeclaration[] = [];
    const blockNameErrors: NameResolutionErrorWithRange[] = [];

    for (let declIndex = 0; declIndex < block.declarations.length; declIndex++) {
      const origDecl = block.declarations[declIndex];
      const sourceMap = adjustSourceMapToAbsolute(block.sourceMaps[declIndex], block.startLine);

      // Name resolution for this declaration (using current symbol context)
      const nameResult = validateDeclarations([origDecl], symbolContext);
      if (nameResult.success) {
        symbolContext = nameResult.value;
      } else {
        // Collect name resolution errors with paths for source range lookup
        for (const err of nameResult.errors) {
          blockNameErrors.push({
            message: err.message,
            symbolName: err.symbolName,
            path: serializeIndexPath(err.path),
            declarationIndex: declIndex
          });
          totalNameErrors++;
        }
      }

      // Pattern resolution for this declaration (using current symbol context)
      const [resolvedDecl] = resolvePatternsInDeclarations([origDecl], symbolContext);
      const decl = resolvedDecl;

      if (decl.kind === 'inductive') {
        // 3. If it is an inductive type def...
        const result = processInductiveDeclaration(decl, sourceMap, definitions);
        compiledDecls.push(result.compiled);

        if (result.success) {
          definitions = result.newDefinitions;
          // Update constructor param names for subsequent term elaboration
          if (result.compiled.kernelConstructors) {
            const newCtorParamNames = buildConstructorParamNames(result.compiled.kernelConstructors);
            for (const [ctorName, paramInfo] of newCtorParamNames) {
              constructorParamNames.set(ctorName, paramInfo);
            }
            setConstructorParamNames(constructorParamNames);
          }
        }
        totalCheckErrors += result.errorCount;
      } else {
        // 4. If we are looking at a term...
        const result = processTermDeclaration(decl, sourceMap, definitions);
        compiledDecls.push(result.compiled);

        if (result.success) {
          definitions = result.newDefinitions;
        }
        totalCheckErrors += result.errorCount;
      }
    }

    compiledBlocks.push({
      blockIndex,
      sourceLines: block.sourceLines,
      startLine: block.startLine,
      parseSuccess: true,
      parseErrors: [],
      nameResolutionSuccess: blockNameErrors.length === 0,
      nameResolutionErrors: blockNameErrors,
      declarations: compiledDecls,
      isComment: false
    });
  }

  return {
    success: parseResult.totalErrors === 0 && totalNameErrors === 0 && totalCheckErrors === 0,
    blocks: compiledBlocks,
    totalParseErrors: parseResult.totalErrors,
    totalNameErrors,
    totalCheckErrors
  };
}

// ============================================================================
// Helper Functions for Absurdity Checking
// ============================================================================

/**
 * Get the type of the Nth argument in a Pi type.
 * Note: This returns the type as-is (may contain bound variables).
 */
function getNthPiArgType(type: TTKTerm, n: number): TTKTerm | null {
  let current = type;
  for (let i = 0; i < n; i++) {
    if (current.tag !== 'Binder' || current.binderKind.tag !== 'BPi') {
      return null;
    }
    current = current.body;
  }
  if (current.tag !== 'Binder' || current.binderKind.tag !== 'BPi') {
    return null;
  }
  return current.domain;
}

/**
 * Extract the inductive type name from a type term.
 * Handles applications like "Vec A n" by extracting the head "Vec".
 */
function extractInductiveTypeName(type: TTKTerm, definitions: DefinitionsMap): string | null {
  // Unwrap applications to get the head
  let head = type;
  while (head.tag === 'App') {
    head = head.fn;
  }

  // Check if it's a Const reference to an inductive type
  if (head.tag === 'Const' && definitions.inductiveTypes.has(head.name)) {
    return head.name;
  }

  return null;
}

/**
 * Try Agda-style recursive splitting on remaining arguments to find absurdity.
 *
 * This is used when basic LHS unification succeeds but we suspect the case
 * might still be absurd due to uninhabited argument types (like Fin Zero).
 *
 * The algorithm tries splitting on each wildcard position after the explicit patterns.
 * If ALL constructors at any position fail unification, the case is absurd.
 *
 * @param termName - The term being checked (for error messages)
 * @param patterns - The explicit patterns to check
 * @param type - The function type
 * @param definitions - The definitions map (for looking up constructors)
 * @param env - A TCEnv for creating pattern environments
 * @returns true if the patterns are absurd, false otherwise
 */
function tryCaseSplitsInSearchOfAbsurdity(
  termName: string,
  patterns: TTKPattern[],
  type: TTKTerm,
  definitions: DefinitionsMap,
  env: TCEnv<unknown>
): boolean {
  const expectedArgCount = countPiBinders(type);

  // Helper to try splitting at a given position
  const trySplitAtPosition = (pos: number): boolean => {
    const argType = getNthPiArgType(type, pos);
    if (!argType) return false;

    const typeName = extractInductiveTypeName(argType, definitions);
    if (!typeName) return false;

    const inductiveDef = definitions.inductiveTypes.get(typeName);
    if (!inductiveDef) return false;

    // A type with zero constructors (like Void) is uninhabited - the case is absurd
    if (inductiveDef.constructors.length === 0) {
      return true;
    }

    let allConstructorsFail = true;
    for (const ctor of inductiveDef.constructors) {
      const ctorArity = countPiBinders(ctor.type);
      const ctorPattern: TTKPattern = {
        tag: 'PCtor',
        name: ctor.name,
        args: Array(ctorArity).fill(null).map(() => ({ tag: 'PWild' as const, name: '_' }))
      };

      // Build patterns with constructor at this position
      const newPatterns: TTKPattern[] = [];
      for (let j = 0; j < expectedArgCount; j++) {
        if (j === pos) {
          newPatterns.push(ctorPattern);
        } else if (j < patterns.length) {
          newPatterns.push(patterns[j]);
        } else {
          newPatterns.push({ tag: 'PWild', name: '_' });
        }
      }

      const newEnv = env.withValue(newPatterns);
      if (!arePatternsAbsurd(termName, newEnv, type)) {
        allConstructorsFail = false;
        break;
      }
    }

    return allConstructorsFail;
  };

  // Helper to replace pattern at a path within the pattern list
  const replacePatternAtPath = (
    pats: TTKPattern[],
    path: number[],
    newPattern: TTKPattern
  ): TTKPattern[] => {
    if (path.length === 0) return pats;

    const [first, ...rest] = path;
    return pats.map((p, i) => {
      if (i !== first) return p;
      if (rest.length === 0) return newPattern;

      // Recurse into PCtor args
      if (p.tag === 'PCtor') {
        return { ...p, args: replacePatternAtPath(p.args, rest, newPattern) };
      }
      return p;
    });
  };

  // Helper to try splitting at a path within a constructor pattern
  // path = [topPos, arg1, arg2, ...] represents patterns[topPos].args[arg1].args[arg2]...
  const trySplitAtPath = (path: number[], argType: TTKTerm): boolean => {
    const typeName = extractInductiveTypeName(argType, definitions);
    if (!typeName) return false;

    const inductiveDef = definitions.inductiveTypes.get(typeName);
    if (!inductiveDef) return false;

    // A type with zero constructors is uninhabited - absurd
    if (inductiveDef.constructors.length === 0) {
      return true;
    }

    let allConstructorsFail = true;
    for (const ctor of inductiveDef.constructors) {
      const ctorArity = countPiBinders(ctor.type);
      const ctorPattern: TTKPattern = {
        tag: 'PCtor',
        name: ctor.name,
        args: Array(ctorArity).fill(null).map(() => ({ tag: 'PWild' as const, name: '_' }))
      };

      // Build padded patterns first
      const paddedPatterns: TTKPattern[] = [];
      for (let j = 0; j < expectedArgCount; j++) {
        if (j < patterns.length) {
          paddedPatterns.push(patterns[j]);
        } else {
          paddedPatterns.push({ tag: 'PWild', name: '_' });
        }
      }

      // Replace the pattern at the given path
      const newPatterns = replacePatternAtPath(paddedPatterns, path, ctorPattern);

      const newEnv = env.withValue(newPatterns);
      if (!arePatternsAbsurd(termName, newEnv, type)) {
        allConstructorsFail = false;
        break;
      }
    }

    return allConstructorsFail;
  };

  // Collect all wildcard paths and their types from constructor patterns
  // Returns array of { path, ctorName, argIndex }
  const collectWildcardPaths = (
    pattern: TTKPattern,
    basePath: number[]
  ): { path: number[], ctorName: string, argIndex: number }[] => {
    const results: { path: number[], ctorName: string, argIndex: number }[] = [];

    if (pattern.tag === 'PCtor') {
      for (let i = 0; i < pattern.args.length; i++) {
        const arg = pattern.args[i];
        const argPath = [...basePath, i];

        if (arg.tag === 'PWild' || arg.tag === 'PVar') {
          results.push({ path: argPath, ctorName: pattern.name, argIndex: i });
        } else if (arg.tag === 'PCtor') {
          results.push(...collectWildcardPaths(arg, argPath));
        }
      }
    }

    return results;
  };

  // Helper to get constructor type from definitions
  const getConstructorType = (ctorName: string): TTKTerm | undefined => {
    const inductiveName = definitions.inductiveNameOfConstructor.get(ctorName);
    if (!inductiveName) return undefined;
    const inductiveDef = definitions.inductiveTypes.get(inductiveName);
    if (!inductiveDef) return undefined;
    const ctor = inductiveDef.constructors.find(c => c.name === ctorName);
    return ctor?.type;
  };

  // Try splitting on existing wildcard positions (PVar or PWild)
  for (let pos = 0; pos < patterns.length; pos++) {
    const pattern = patterns[pos];
    if (pattern.tag === 'PVar' || pattern.tag === 'PWild') {
      if (trySplitAtPosition(pos)) {
        return true;
      }
    }
  }

  // Try splitting on padded wildcard positions (positions after the pattern list)
  for (let pos = patterns.length; pos < expectedArgCount; pos++) {
    if (trySplitAtPosition(pos)) {
      return true;
    }
  }

  // Try splitting on wildcards nested inside constructor patterns
  for (let pos = 0; pos < patterns.length; pos++) {
    const pattern = patterns[pos];
    if (pattern.tag === 'PCtor') {
      const wildcardPaths = collectWildcardPaths(pattern, [pos]);

      for (const { path, ctorName, argIndex } of wildcardPaths) {
        // Get the constructor's type to find the arg type at argIndex
        const ctorType = getConstructorType(ctorName);
        if (!ctorType) continue;

        const argType = getNthPiArgType(ctorType, argIndex);
        if (!argType) continue;

        if (trySplitAtPath(path, argType)) {
          return true;
        }
      }
    }
  }

  return false;
}

// ============================================================================
// Term Value Checking
// ============================================================================

/**
 * Check a match clause from surface syntax, following the proper order:
 * 1. Elaborate LHS patterns (surface -> kernel)
 * 2. Run LHS unification & constraint solving
 * 3. Elaborate RHS (surface -> kernel) - can use context from LHS in future
 * 4. Check RHS against refined return type
 *
 * This ensures RHS elaboration happens AFTER LHS unification, allowing
 * future type-directed RHS elaboration if needed.
 */
function checkMatchClauseFromSurface(
  termName: string,
  surfaceClause: TClause,
  type: TTKTerm,
  termEnv: TCEnv<TermDefinition>,
  elabMap: ElabMap,
  clauseIndex: number,
  namedArgMap: NamedArgMap | undefined,
  totalArity: number | undefined,
): TTKClause {
  const clauseSurfacePath: IndexPath = [
    { kind: 'field', name: 'value' },
    { kind: 'field', name: 'clauses' },
    { kind: 'array', index: clauseIndex }
  ];
  const clauseKernelPath: IndexPath = [
    { kind: 'field', name: 'value' },
    { kind: 'field', name: 'clauses' },
    { kind: 'array', index: clauseIndex }
  ];

  // Step 1: Elaborate LHS patterns (surface -> kernel)
  // This includes reordering for named arguments
  let patternsToElab = surfaceClause.patterns;
  let rhsToElab = surfaceClause.rhs;
  const hasClauseNamedPatterns = surfaceClause.namedPatterns && surfaceClause.namedPatterns.length > 0;
  // sourceIndexMap[kernelIndex] = sourceIndex (or null for synthetic wildcards)
  let sourceIndexMap: (number | null)[] | undefined;

  if (namedArgMap && namedArgMap.size > 0) {
    const reorderResult = reorderPatterns(surfaceClause.patterns, namedArgMap, surfaceClause.namedPatterns, totalArity);
    if ('error' in reorderResult && reorderResult.error !== undefined) {
      throw TCEnvError.create(reorderResult.error, termEnv);
    }
    patternsToElab = reorderResult.ordered!;
    sourceIndexMap = reorderResult.sourceIndexMap;

    // Apply RHS adjustment for pattern reordering
    // When user explicitly uses named patterns, apply the computed permutation
    // When wildcards are inserted for missing named params (at front positions),
    // no RHS adjustment is needed - they get highest de Bruijn indices and don't affect user vars
    if (hasNamedPatterns(surfaceClause.patterns) || hasClauseNamedPatterns) {
      rhsToElab = applyVarPermutation(surfaceClause.rhs, reorderResult.varIndexPermutation!);
    }
  }

  // Fix RHS for constructor patterns that the parser mistakenly treated as variables
  // (e.g., lowercase constructors like 'refl' that the parser thought were variable bindings)
  rhsToElab = fixRhsForConstructorPatterns(patternsToElab, rhsToElab, termEnv.definitions);

  // Elaborate patterns to kernel form
  const kernelPatterns: TTKPattern[] = patternsToElab.map((pattern, patternIndex) => {
    // Use sourceIndexMap to find the original source pattern index
    // sourceIndexMap[kernelIndex] = sourceIndex (or null for synthetic patterns)
    const sourcePatternIndex = sourceIndexMap?.[patternIndex] ?? patternIndex;
    // For synthetic patterns (null), use the kernel index as a fallback (no real source)
    const effectiveSourceIndex = sourcePatternIndex ?? patternIndex;
    const patternSurfacePath = appendPath(clauseSurfacePath, fieldSeg('patterns'), arraySeg(effectiveSourceIndex));
    const patternKernelPath = appendPath(clauseKernelPath, fieldSeg('patterns'), arraySeg(patternIndex));
    return elabPatternToKernelWithMap(pattern, elabMap, patternSurfacePath, patternKernelPath);
  });

  // Record the clause mapping
  elabMap.set(serializeIndexPath(clauseKernelPath), serializeIndexPath(clauseSurfacePath));

  // Step 2: Elaborate RHS (surface -> kernel) AFTER LHS patterns are elaborated
  // This is the key change - RHS elaboration happens after LHS elaboration
  const rhsSurfacePath = appendPath(clauseSurfacePath, fieldSeg('rhs'));
  const rhsKernelPath = appendPath(clauseKernelPath, fieldSeg('rhs'));

  // Create lookup for named args of other definitions being applied in RHS
  // Include the current function for recursive calls
  const baseNamedArgLookup = createNamedArgInfoLookup(termEnv.definitions);
  const appNamedArgLookup = (name: string) => {
    // For recursive calls, use the current function's named arg info
    if (name === termName && namedArgMap && namedArgMap.size > 0) {
      return { namedArgMap, totalArity };
    }
    return baseNamedArgLookup(name);
  };

  const kernelRhs: TTKTerm = elabToKernelWithMap(
    rhsToElab,
    elabMap,
    rhsSurfacePath,
    rhsKernelPath,
    namedArgMap,
    appNamedArgLookup
  );

  // Now create the full kernel clause and check it
  const fullKernelClause: TTKClause = {
    patterns: kernelPatterns,
    rhs: kernelRhs
  };

  // Step 4: Check the clause (unify LHS, check RHS)
  // NOTE: Don't pass namedArgMap/totalArity here - reorderPatterns already handled wildcard insertion
  // for missing named arguments. Passing them would cause double-padding.
  const clauseEnv = termEnv.atIndexPathAndValue([...termEnv.indexPath, TermDefinitionPartIndex.Value, MatchPartIndex.Clauses, arraySeg(clauseIndex)], fullKernelClause);
  const checkedClauseEnv = checkMatchClause(termName, clauseEnv, type);

  return checkedClauseEnv.value;
}

function checkTermValue(
  name: string | undefined,
  termEnv: TCEnv<TermDefinition>,
  type: TTKTerm,
  surfaceClauses: TClause[],
  elabMap: ElabMap,
  namedArgMap: NamedArgMap | undefined,
  totalArity: number | undefined,
  annotatedAbsurdClauses: number[] = [],
): { success: false, errors: TCEnvError[], totalityResult?: TotalityResult } | { success: true, checkedValue: TTKTerm, totalityResult?: TotalityResult } {
  const errors: TCEnvError[] = [];
  const checkedClauses: TTKClause[] = [];

  // Handle zero-clause case (e.g., absurd : Void -> A)
  const hasNoClauses = surfaceClauses.length === 0;

  const firstClauseRootPatternsCount = hasNoClauses ? 0 : surfaceClauses[0].patterns.length;
  const maxAllowedPatternsCount = countPiBinders(type);

  // Note: #absurd clauses are validated in checkTermDeclaration and filtered before reaching here
  // The annotatedAbsurdClauses parameter contains their surface indices

  for (let clauseIndex = 0; clauseIndex < surfaceClauses.length; clauseIndex++) {
    const surfaceClause = surfaceClauses[clauseIndex];
    const rootPatternsCount = surfaceClause.patterns.length;

    if (rootPatternsCount !== firstClauseRootPatternsCount) {
      errors.push(TCEnvError.create(`Mismatch in pattern count: clause ${clauseIndex + 1} has ${rootPatternsCount} patterns, expected ${firstClauseRootPatternsCount}.`, termEnv));
    } else if (rootPatternsCount > maxAllowedPatternsCount) {
      errors.push(TCEnvError.create(`Pattern count exceeds type binders count: clause ${clauseIndex + 1} has ${rootPatternsCount} patterns, expected <= ${maxAllowedPatternsCount}.`, termEnv));
    } else {
      try {
        // Following the flow: elaborate LHS, unify & solve, then elaborate and check RHS
        const checkedClause = checkMatchClauseFromSurface(
          name ?? '???',
          surfaceClause,
          type,
          termEnv,
          elabMap,
          clauseIndex,
          namedArgMap,
          totalArity
        );
        checkedClauses.push(checkedClause);
      } catch (e) {
        if (e instanceof TCEnvError) {
          errors.push(e);
        } else {
          errors.push(TCEnvError.create(String(e), termEnv));
        }
      }
    }
  }

  if (errors.length > 0) {
    return { success: false, errors };
  }

  // Build the checked Match term with solved/reified RHS terms
  const checkedValue: TTKTerm = {
    tag: 'Match',
    scrutinee: { tag: 'Hole', id: '_scrutinee' },
    clauses: checkedClauses
  };

  // Structural recursion check
  if (name) {
    const recursionResult = checkStructuralRecursion(name, checkedClauses);
    if (!recursionResult.isValid) {
      const recursionErrors = recursionResult.errors.map(({ clauseIndex, error }) => {
        // Construct the full path to the recursive call:
        // value.clauses[clauseIndex].rhs + rhsPath
        const errorPath: IndexPath = [
          fieldSeg('value'),
          fieldSeg('clauses'),
          arraySeg(clauseIndex),
          fieldSeg('rhs'),
          ...error.rhsPath
        ];
        const errorEnv = termEnv.atIndexPath(errorPath);
        return TCEnvError.create(error.message, errorEnv);
      });
      return { success: false, errors: recursionErrors };
    }
  }

  // Create absurdity checker that uses pattern LHS unification
  // Enhanced with Agda-style recursive splitting on remaining arguments
  const absurdityChecker = (patterns: TTKPattern[]): boolean => {
    const termName = name ?? '???';
    const expectedArgCount = countPiBinders(type);

    // Pad patterns with wildcards if needed
    const paddedPatterns = [...patterns];
    while (paddedPatterns.length < expectedArgCount) {
      paddedPatterns.push({ tag: 'PWild', name: '_' });
    }

    // Basic absurdity check with padded patterns
    const patternEnv = termEnv.withValue(paddedPatterns);
    if (arePatternsAbsurd(termName, patternEnv, type)) {
      return true;
    }

    // Try Agda-style recursive splitting on remaining arguments
    return tryCaseSplitsInSearchOfAbsurdity(termName, patterns, type, termEnv.definitions, termEnv);
  };

  // Run totality checking (builds case tree and checks coverage)
  // Pass zonked elabArgs and contextNames for case tree display
  const totalityClauses = checkedClauses.map(c => ({
    patterns: c.patterns,
    elabArgs: c.elabArgs,
    contextNames: c.contextNames
  }));
  const totalityResult = checkTotality(name ?? '???', totalityClauses, termEnv.definitions, absurdityChecker);

  // Helper to format missing patterns with padding and named args
  const formatMissingPatterns = (patterns: TTKPattern[]): string => {
    const expectedArgCount = countPiBinders(type);

    // Pad patterns with wildcards if needed
    const paddedPatterns = [...patterns];
    while (paddedPatterns.length < expectedArgCount) {
      paddedPatterns.push({ tag: 'PWild', name: '_' });
    }

    // Build position -> name map from namedArgMap (which is name -> position)
    const positionToName = new Map<number, string>();
    if (namedArgMap) {
      for (const [argName, position] of namedArgMap) {
        positionToName.set(position, argName);
      }
    }

    // Format each pattern, using named arg syntax for named positions
    return paddedPatterns.map((p, i) => {
      const argName = positionToName.get(i);
      const patternStr = prettyPrintPattern(p);
      if (argName) {
        return `{${argName}:=${patternStr}}`;
      }
      return patternStr;
    }).join(' ');
  };

  // Convert totality issues to errors
  const totalityErrors: TCEnvError[] = [];
  for (const { clauseIndex, patterns } of totalityResult.unreachableClauses) {
    totalityErrors.push(TCEnvError.create(`Redundant clause: ${name ? `${name} ` : ''}${prettyPrintPatternList(patterns)}`, termEnv.atIndexPath(
      appendPath(termEnv.indexPath, fieldSeg('value'), fieldSeg('clauses'), arraySeg(clauseIndex))
    )));
  }
  if (!totalityResult.isExhaustive) {
    const formattedClauses = totalityResult.missingValidClauses.map(c => formatMissingPatterns(c.patterns)).join('\n');
    totalityErrors.push(TCEnvError.create(`Function ${name ? `${name} ` : ''}is non-total. Missing clause${totalityResult.missingValidClauses.length === 1 ? '' : 's'
      }:\n${formattedClauses}`, termEnv));
  }

  // Add annotatedAbsurdClauses to the totality result
  const enrichedTotalityResult: TotalityResult = {
    ...totalityResult,
    annotatedAbsurdClauses: annotatedAbsurdClauses.length > 0 ? annotatedAbsurdClauses : undefined
  };

  if (totalityErrors.length > 0) {
    return { success: false, errors: totalityErrors, totalityResult: enrichedTotalityResult };
  }

  return { success: true, checkedValue, totalityResult: enrichedTotalityResult };
}
