/**
 * Fresh TT Compiler - A clean implementation of the compilation pipeline
 *
 * This module provides a simple interface for compiling TT source code
 * to elaborated kernel terms (TTK).
 */

import { groupByIndentation } from '../parser/indentation-grouper';
import { Parser, ParsedDeclaration, ParseError } from '../parser/parser';
import { elabToKernelWithMap, buildConstructorParamNames, setConstructorParamNames, resetWildcardCounter, extractConstructorParamNames, setCurrentTermParamNames, ConstructorParamNames, ParamInfo } from './elab';
import { TTKTerm, TTKContext, prettyPrint as prettyPrintTTK, TTKClause, TTKPattern, prettyPrintPattern } from './kernel';
import { TTerm, TPattern, TClause } from './surface';
import { validateDeclarations, emptySymbolContext, SymbolContext } from '../types/name-resolution';
import { resolvePatternsInDeclarations } from '../parser/pattern-resolution';
import { arraySeg, ElabMap, fieldSeg, IndexPath, SourceMap } from '../types/source-position'
import { checkType, inferType } from './checker';
import { addDefinitionInTCEnv, countPiBinders, createDefinitionsMap, createTCEnv, DefinitionsMap, setDefinitionValueInTCEnv, TCEnv, TCEnvError, TermDefinition, validateTermNameNotDefined } from './term';
import { checkInductiveDeclaration } from './inductive';
import { checkMatchClause } from './patterns';
import { checkFunctionTotality, formatMissingCase } from './ttk-totality-check';
import { analyzeRecursionTTK } from './ttk-recursion-check';

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
  kernelConstructors?: Array<{ name: string; type: TTKTerm }>;
  /** Maps kernel paths to surface paths (for error mapping) */
  elabMap?: ElabMap;
  /** Maps surface paths to source ranges (for error mapping) */
  sourceMap?: SourceMap;
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
  kernelConstructors?: Array<{ name: string; type: TTKTerm }>;

  // For inductive types: positions that are indices (not parameters)
  indexPositions?: number[];

  // Pretty-printed versions for display
  prettyType?: string;
  prettyValue?: string;
  prettyConstructors?: Array<{ name: string; prettyType: string }>;

  // Type checking results
  checkSuccess: boolean;
  checkErrors: TCEnvError[];

  // Source mapping for error locations
  elabMap?: ElabMap;
  sourceMap?: SourceMap;
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
  nameResolutionErrors: string[];

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
export type SemanticTokenType = 'termName' | 'constName' | 'boundVar' | 'patternVar';

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
      break;

    case 'Annot':
      collectSemanticTokensFromSurfaceTerm(term.term, sourceMap, blockStartLine, [...path, 'term'], tokens);
      collectSemanticTokensFromSurfaceTerm(term.type, sourceMap, blockStartLine, [...path, 'type'], tokens);
      break;

    case 'Match':
      collectSemanticTokensFromSurfaceTerm(term.scrutinee, sourceMap, blockStartLine, [...path, 'scrutinee'], tokens);
      for (let i = 0; i < term.clauses.length; i++) {
        const clause = term.clauses[i];
        // Collect from patterns
        for (let j = 0; j < clause.patterns.length; j++) {
          collectSemanticTokensFromSurfacePattern(
            clause.patterns[j],
            sourceMap,
            blockStartLine,
            [...path, 'clauses', i, 'patterns', j],
            tokens
          );
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
  blockStartLine: number,
  type: SemanticTokenType,
  tokens: SemanticToken[]
): void {
  const pathStr = serializePathForLookup(path);
  const range = sourceMap.get(pathStr);
  if (range) {
    tokens.push({
      line: range.start.line + blockStartLine - 1,
      column: range.start.col,
      length: range.end.col - range.start.col,
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
      // Found a hole - add its location
      addHoleLocation(path, sourceMap, blockStartLine, term.id, holes);
      // Also recurse into the hole's type (which might contain more holes)
      collectHolesFromSurfaceTerm(term.type, sourceMap, blockStartLine, [...path, 'type'], holes);
      break;

    case 'Var':
    case 'Const':
    case 'Sort':
      // Leaf nodes - no holes
      break;

    case 'Binder':
      collectHolesFromSurfaceTerm(term.domain, sourceMap, blockStartLine, [...path, 'domain'], holes);
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
  blockStartLine: number,
  id: string,
  holes: HoleLocation[]
): void {
  const pathStr = serializePathForLookup(path);
  const range = sourceMap.get(pathStr);
  if (range) {
    holes.push({
      line: range.start.line + blockStartLine - 1,
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
  blockStartLine: number,
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
        hints.push({
          line: range.start.line + blockStartLine - 1,
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
        blockStartLine,
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
      const sourceMap = block.sourceMaps[declIndex];
      // Use resolved declaration if available, otherwise fall back to original
      const decl = (origDecl.name && resolvedDeclMap.get(origDecl.name)) || origDecl;
      const elabMap: ElabMap = new Map();

      let kernelType: TTKTerm | undefined;
      let kernelValue: TTKTerm | undefined;
      let kernelConstructors: Array<{ name: string; type: TTKTerm }> | undefined;

      try {
        // Elaborate type
        if (decl.type) {
          const typePath: IndexPath = [{ kind: 'field', name: 'type' }];
          kernelType = elabToKernelWithMap(decl.type, elabMap, typePath, typePath);
        }

        // Elaborate value (only if elabValues is true)
        if (elabValues && decl.value) {
          const valuePath: IndexPath = [{ kind: 'field', name: 'value' }];
          kernelValue = elabToKernelWithMap(decl.value, elabMap, valuePath, valuePath);
        }

        // Elaborate constructors
        if (decl.constructors) {
          kernelConstructors = decl.constructors.map((ctor, ctorIndex) => {
            const ctorTypePath: IndexPath = [
              { kind: 'field', name: 'constructors' },
              { kind: 'array', index: ctorIndex },
              { kind: 'field', name: 'type' }
            ];
            return {
              name: ctor.name,
              type: elabToKernelWithMap(ctor.type, elabMap, ctorTypePath, ctorTypePath)
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
        // Elaboration error - skip this declaration
        console.error('Elaboration error:', e);
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
 * Elaborate term values for declarations that were elaborated without values in phase 1.
 * This is phase 2 of elaboration, after constructor param names are available.
 *
 * @param parseResult - Original parse result (needed for source values)
 * @param elabResult - Result from phase 1 elaboration (has types but no values)
 * @returns ElabResult with values filled in
 */
export function elabTTValuesOnly(parseResult: ParseResult, elabResult: ElabResult): ElabResult {
  // Build a map from declaration name to parsed declaration for value lookup
  const parsedDeclMap = new Map<string, { decl: ParsedDeclaration; sourceMap: SourceMap }>();
  for (const block of parseResult.blocks) {
    if (block.kind === 'declarations') {
      for (let i = 0; i < block.declarations.length; i++) {
        const decl = block.declarations[i];
        if (decl.name) {
          parsedDeclMap.set(decl.name, { decl, sourceMap: block.sourceMaps[i] });
        }
      }
    }
  }

  // Collect all parsed declarations for pattern resolution (need resolved patterns)
  let allDeclarations: ParsedDeclaration[] = [];
  for (const block of parseResult.blocks) {
    if (block.kind === 'declarations') {
      allDeclarations = [...allDeclarations, ...block.declarations];
    }
  }

  // Name resolution
  let symbolContext: SymbolContext = emptySymbolContext();
  for (const decl of allDeclarations) {
    const result = validateDeclarations([decl], symbolContext);
    if (result.success) {
      symbolContext = result.value;
    }
  }

  // Pattern resolution
  allDeclarations = resolvePatternsInDeclarations(allDeclarations, symbolContext);

  // Build resolved map
  const resolvedDeclMap = new Map<string, ParsedDeclaration>();
  for (const decl of allDeclarations) {
    if (decl.name) {
      resolvedDeclMap.set(decl.name, decl);
    }
  }

  const newBlocks: ElabBlock[] = [];

  for (const block of elabResult.blocks) {
    if (block.kind !== 'declarations') {
      newBlocks.push(block);
      continue;
    }

    const newDeclarations: ElabDeclaration[] = [];

    for (const elabDecl of block.declarations) {
      // Skip inductive types - they don't have values
      if (elabDecl.kind === 'inductive' || !elabDecl.name) {
        newDeclarations.push(elabDecl);
        continue;
      }

      // Get the resolved parsed declaration
      const resolvedDecl = resolvedDeclMap.get(elabDecl.name);
      if (!resolvedDecl || !resolvedDecl.value) {
        newDeclarations.push(elabDecl);
        continue;
      }

      // Elaborate the value with constructor param context available
      const elabMap: ElabMap = elabDecl.elabMap ?? new Map();
      try {
        // Extract param names from the term's type signature for top-level pattern naming
        if (elabDecl.kernelType) {
          const termParamNames = extractConstructorParamNames(elabDecl.kernelType);
          setCurrentTermParamNames(termParamNames);
        }

        const valuePath: IndexPath = [{ kind: 'field', name: 'value' }];
        const kernelValue = elabToKernelWithMap(resolvedDecl.value, elabMap, valuePath, valuePath);

        // Clear term param names after elaboration
        setCurrentTermParamNames(null);

        newDeclarations.push({
          ...elabDecl,
          surfaceValue: resolvedDecl.value,
          kernelValue,
          elabMap,
        });
      } catch (e) {
        console.error('Value elaboration error:', e);
        setCurrentTermParamNames(null);
        newDeclarations.push(elabDecl);
      }
    }

    newBlocks.push({
      kind: 'declarations',
      declarations: newDeclarations,
      sourceLines: block.sourceLines,
      startLine: block.startLine,
    });
  }

  return { blocks: newBlocks };
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

  if (decl.kind === 'inductive') {
    const result = checkInductiveTypeDeclaration(decl, definitions);
    if (result.success) {
      newDefinitions = result.definitions;
      indexPositions = result.indexPositions;
    } else {
      checkSuccess = false;
      checkErrors.push(...result.errors);
      errorCount = result.errors.length;
    }
  } else if (decl.kind === 'term') {
    const result = checkTermDeclaration(decl, definitions);
    if (result.success) {
      newDefinitions = result.definitions;
    } else {
      checkSuccess = false;
      checkErrors.push(...result.errors);
      errorCount = result.errors.length;
    }
  } else {
    checkSuccess = false;
    const error = TCEnvError.create('Declaration is not an inductive or term', createTCEnv(definitions));
    checkErrors.push(error);
    errorCount = 1;
  }

  // Build compiled declaration with pretty-printed versions
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
    kernelConstructors: decl.kernelConstructors,
    indexPositions,
    prettyType: decl.kernelType ? prettyPrintTTK(decl.kernelType) : undefined,
    prettyValue: decl.kernelValue ? prettyPrintTTK(decl.kernelValue) : undefined,
    prettyConstructors: decl.kernelConstructors?.map(c => ({
      name: c.name,
      prettyType: prettyPrintTTK(c.type)
    })),
    checkSuccess,
    checkErrors,
    elabMap: decl.elabMap,
    sourceMap: decl.sourceMap
  };

  return { compiled, newDefinitions, errorCount };
}

function checkInductiveTypeDeclaration(
  decl: ElabDeclaration,
  definitions: DefinitionsMap,
): { success: false, errors: TCEnvError[] } | { success: true, definitions: DefinitionsMap, indexPositions: number[] } {
  if (decl.kind !== 'inductive') {
    return failCheck('Declaration is not an inductive type', createTCEnv(definitions))
  }

  if (!decl.kernelType) {
    return failCheck('Inductive type declaration is ill-formed', createTCEnv(definitions))
  }
  if (!decl.kernelConstructors) {
    return failCheck('Inductive type declaration is ill-formed', createTCEnv(definitions))
  }

  const result = checkInductiveDeclaration(
    decl.name || 'anonymous',
    decl.kernelType,
    decl.kernelConstructors,
    definitions
  );
  if (!result.success) {
    return result
  } else {
    return {
      success: true,
      definitions: result.newDefinitions,
      indexPositions: result.indexPositions,
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
): { success: false, errors: TCEnvError[] } | { success: true, definitions: DefinitionsMap } {
  if (!decl.name) {
    return failCheck('Term declaration is ill-formed (no name)', createTCEnv(definitions))
  }

  let env = createTCEnv(definitions)

  if (decl.kind !== 'term') {
    return failCheck('Declaration is not a term', env)
  }

  if (!decl.kernelType) {
    return failCheck('Term declaration is ill-formed', env)
  }

  try {
    if (!decl.kernelValue) {
      return failCheck('Term declaration is ill-formed', env)
    }

    let termEnv = env.withValue<TermDefinition>({
      name: decl.name,
      type: decl.kernelType,
      value: decl.kernelValue,
    });

    // Check for duplicate names
    validateTermNameNotDefined(termEnv);

    inferType(termEnv.inTermType());

    // Add to context for subsequent declarations
    if (decl.name) {
      termEnv = addDefinitionInTCEnv(termEnv, decl.name, decl.kernelType);
    }

    const termValueEnv = termEnv.inTermValue()
    if (!termValueEnv.hasDefinedValue()) {
      return failCheck('Term declaration is ill-formed (missing value)', termValueEnv)
    }

    const result = checkTermValue(decl.name, termValueEnv, decl.kernelType);
    if (!result.success) {
      return { success: false, errors: result.errors }
    }

    const resultEnv = setDefinitionValueInTCEnv(termEnv, decl.name, result.checkedValue);
    return { success: true, definitions: resultEnv.definitions }
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
 * Compile TT source code to elaborated kernel terms.
 *
 * Pipeline (phased for constructor-aware wildcard naming):
 * 1. Parse source (grouping, parsing)
 * 2. Phase 1 elaboration: elaborate types and constructors (no term values)
 * 3. Phase 1 type check: check inductive types only
 * 4. Build constructor param names from checked inductives
 * 5. Phase 2 elaboration: elaborate term values (with constructor context)
 * 6. Phase 2 type check: check term declarations
 *
 * @param source - The full source code
 * @returns CompileResult with elaborated declarations
 */
export function compileTTFromText(source: string): CompileResult {
  // Reset wildcard counter for fresh compilation
  resetWildcardCounter();

  const parseResult = parseTTSource(source);

  // Phase 1: Elaborate types and constructors only (no term values)
  const elabResultPhase1 = elabTT(parseResult, [], { elabValues: false });

  // Phase 1: Type check inductive types only
  const checkResultPhase1 = checkBlocks(elabResultPhase1, createDefinitionsMap(), {
    onlyKind: 'inductive'
  });

  // Build constructor param names from checked inductives
  const constructorParamNames = collectConstructorParamNames(checkResultPhase1.blocks);
  setConstructorParamNames(constructorParamNames);

  // Phase 2: Elaborate term values (now with constructor context)
  const elabResultPhase2 = elabTTValuesOnly(parseResult, elabResultPhase1);

  // Phase 2: Type check term declarations
  const checkResultPhase2 = checkBlocks(elabResultPhase2, checkResultPhase1.finalDefinitions, {
    onlyKind: 'term',
    existingBlocks: checkResultPhase1.blocks
  });

  const totalCheckErrors = checkResultPhase1.totalCheckErrors + checkResultPhase2.totalCheckErrors;

  return {
    success: parseResult.totalErrors === 0 && totalCheckErrors === 0,
    blocks: checkResultPhase2.blocks,
    totalParseErrors: parseResult.totalErrors,
    totalNameErrors: 0,
    totalCheckErrors
  };
}

function checkTermValue(
  name: string | undefined,
  env: TCEnv<TTKTerm>,
  type: TTKTerm,
): { success: false, errors: TCEnvError[] } | { success: true, checkedValue: TTKTerm } {
  if (!env.isMatchTerm()) {
    try {
      const result = checkType(env, type);
      return { success: true, checkedValue: result.value };
    } catch (e) {
      if (e instanceof TCEnvError) {
        return { success: false, errors: [e] };
      } else {
        return { success: false, errors: [TCEnvError.create(String(e), env)] };
      }
    }
  }

  const clausesEnv = env.inMatchClauses();
  const errors: TCEnvError[] = [];
  const checkedClauses: TTKClause[] = [];

  const firstClauseRootPatternsCount = clausesEnv.value[0].patterns.length;
  const maxAllowedPatternsCount = countPiBinders(type);

  for (let clauseIndex = 0; clauseIndex < clausesEnv.value.length; clauseIndex++) {
    const clauseEnv = clausesEnv.inMatchClause(clauseIndex);
    const rootPatternsCount = clauseEnv.value.patterns.length;

    if (rootPatternsCount !== firstClauseRootPatternsCount) {
      errors.push(TCEnvError.create(`Mismatch in pattern count: clause ${clauseIndex + 1} has ${rootPatternsCount} patterns, expected ${firstClauseRootPatternsCount}.`, clauseEnv));
    } else if (rootPatternsCount > maxAllowedPatternsCount) {
      errors.push(TCEnvError.create(`Pattern count exceeds type binders count: clause ${clauseIndex + 1} has ${rootPatternsCount} patterns, expected <= ${maxAllowedPatternsCount}.`, clauseEnv));
    } else {
      try {
        const checkedClauseEnv = checkMatchClause(name ?? '???', clauseEnv, type);
        checkedClauses.push(checkedClauseEnv.value);
      } catch (e) {
        if (e instanceof TCEnvError) {
          errors.push(e);
        } else {
          errors.push(TCEnvError.create(String(e), clausesEnv.inMatchClause(clauseIndex)));
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
    scrutinee: env.value.scrutinee,
    clauses: checkedClauses
  };

  // Structural recursion check: ensure all recursive calls are on structurally smaller arguments
  // We analyze the CHECKED term (with metas solved) not the raw input term
  if (name !== undefined) {
    const recursionAnalysis = analyzeRecursionTTK(name, checkedValue);
    if (recursionAnalysis.unsafeRecursion.length > 0) {
      for (const unsafe of recursionAnalysis.unsafeRecursion) {
        errors.push(TCEnvError.create(`Unsafe recursion in '${name}': ${unsafe.error}`, env));
      }
      return { success: false, errors };
    }
  }

  // Totality check - verify all patterns are covered
  if (name) {
    const totalityAnalysis = checkFunctionTotality(name, type, clausesEnv.value, env.definitions);
    if (!totalityAnalysis.exhaustive) {
      const missingCasesStr = totalityAnalysis.missingCases
        .map(mc => formatMissingCase(name, mc))
        .join('\n  ');
      errors.push(TCEnvError.create(
        `Non-exhaustive pattern match in '${name}'. Missing cases:\n  ${missingCasesStr}`,
        env
      ));
    }

    // Report inaccessible clauses (shadowed by earlier patterns)
    for (const clauseIdx of totalityAnalysis.inaccessibleClauses) {
      errors.push(TCEnvError.create(
        `Inaccessible clause: clause ${clauseIdx + 1} is never reached (shadowed by earlier patterns)`,
        clausesEnv.inMatchClause(clauseIdx)
      ));
    }
  }

  if (errors.length > 0) {
    return { success: false, errors };
  }

  return { success: true, checkedValue };
}
