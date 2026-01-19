/**
 * Fresh TT Compiler - A clean implementation of the compilation pipeline
 *
 * This module provides a simple interface for compiling TT source code
 * to elaborated kernel terms (TTK).
 */

import { groupByIndentation } from '../parser/indentation-grouper';
import { Parser, ParsedDeclaration, ParseError } from '../parser/parser';
import { elabToKernelWithMap, buildConstructorParamNames, setConstructorParamNames, resetWildcardCounter, extractConstructorParamNames, setCurrentTermParamNames, ConstructorParamNames, ParamInfo } from './elab';
import { TTKTerm, TTKContext, prettyPrint as prettyPrintTTK, TTKClause, TTKPattern, prettyPrintPattern, mkVar, mkConst, mkType, mkAppSpine } from './kernel';
import { TTerm, TPattern, TClause } from './surface';
import { validateDeclarations, emptySymbolContext, SymbolContext } from '../types/name-resolution';
import { resolvePatternsInDeclarations } from '../parser/pattern-resolution';
import { arraySeg, ElabMap, fieldSeg, IndexPath, SourceMap } from '../types/source-position'
import { checkType, inferType } from './checker';
import { addDefinitionInTCEnv, addMetaVarInTCEnv, assertDefined, assertIsNotPi, assertIsPi, countPiBinders, createDefinitionsMap, createTCEnv, DefinitionsMap, extractAppSpine, printCollectionFancy, setDefinitionValueInTCEnv, Signature, TCEnv, TCEnvError, TermDefinition, transformVarsInTerm, validateTermNameNotDefined, validatePatternVarName } from './term';
import { checkInductiveDeclaration } from './inductive';
import { unifyTerms } from './unify';
import { enumerateAppliedSubstitutions, shiftTerm, subst } from './subst';

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
  checkErrors: TCEnvError<unknown>[];

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
      // Recurse into domain and body
      collectSemanticTokensFromSurfaceTerm(term.domain, sourceMap, blockStartLine, [...path, 'domain'], tokens);
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
 * Extract wildcard inlay hints from a compile result.
 *
 * This walks through the compiled declarations, finds PWild patterns in
 * Match expressions, and returns their positions and generated names.
 */
export function extractWildcardInlayHints(result: CompileResult): WildcardInlayHint[] {
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

    case 'Hole':
      collectWildcardsFromTerm(term.type, elabMap, sourceMap, blockStartLine, [...path, 'type'], hints);
      break;

    // Leaf nodes - no recursion
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
  const checkErrors: TCEnvError<unknown>[] = [];
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
    const error = new TCEnvError<unknown>('Declaration is not an inductive or term', createTCEnv(definitions));
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
): { success: false, errors: TCEnvError<unknown>[] } | { success: true, definitions: DefinitionsMap, indexPositions: number[] } {
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

function failCheck(message: string, env: TCEnv<unknown>): { success: false, errors: TCEnvError<unknown>[] } {
  return {
    success: false,
    errors: [new TCEnvError(message, env)],
  }
}

function checkTermDeclaration(
  decl: ElabDeclaration,
  definitions: DefinitionsMap,
): { success: false, errors: TCEnvError<unknown>[] } | { success: true, definitions: DefinitionsMap } {
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
        errors: [new TCEnvError(e instanceof Error ? e.message : String(e), env)],
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

let loggingEnabled = true;

function logInfo(fn: () => string) {
  if (loggingEnabled) {
    console.log(fn());
  }
}

function checkTermValue(
  name: string | undefined,
  env: TCEnv<TTKTerm>,
  type: TTKTerm,
): { success: false, errors: TCEnvError<unknown>[] } | { success: true, checkedValue: TTKTerm } {
  if (!env.isMatchTerm()) {
    try {
      const result = checkType(env, type);
      return { success: true, checkedValue: result.value };
    } catch (e) {
      if (e instanceof TCEnvError) {
        return { success: false, errors: [e] };
      } else {
        return { success: false, errors: [new TCEnvError(String(e), env)] };
      }
    }
  }

  const clausesEnv = env.inMatchClauses();
  const errors: TCEnvError<unknown>[] = [];

  const firstClauseRootPatternsCount = clausesEnv.value[0].patterns.length;
  const maxAllowedPatternsCount = countPiBinders(type);

  for (let clauseIndex = 0; clauseIndex < clausesEnv.value.length; clauseIndex++) {
    const clauseEnv = clausesEnv.inMatchClause(clauseIndex);
    const rootPatternsCount = clauseEnv.value.patterns.length;

    if (rootPatternsCount !== firstClauseRootPatternsCount) {
      errors.push(new TCEnvError(`Mismatch in pattern count: clause ${clauseIndex + 1} has ${rootPatternsCount} patterns, expected ${firstClauseRootPatternsCount}.`, clauseEnv));
    } else if (rootPatternsCount > maxAllowedPatternsCount) {
      errors.push(new TCEnvError(`Pattern count exceeds type binders count: clause ${clauseIndex + 1} has ${rootPatternsCount} patterns, expected <= ${maxAllowedPatternsCount}.`, clauseEnv));
    } else {
      try {
        checkMatchClause(name ?? '???', clauseEnv, type);
      } catch (e) {
        if (e instanceof TCEnvError) {
          errors.push(e);
        } else {
          errors.push(new TCEnvError(String(e), clausesEnv.inMatchClause(clauseIndex)));
        }
      }
    }
  }

  // TODO: structural recursion check
  // TODO: totality check

  if (errors.length > 0) {
    return { success: false, errors };
  }

  return { success: true, checkedValue: env.value };
}

/* PATTERNS */

function checkMatchClause(
  termName: string,
  env: TCEnv<TTKClause>,
  type: TTKTerm,
): TCEnv<void> {
  const result = processMatchClauseLhs(termName, env.inMatchClausePatterns(), type)
  // TODO: rhs type check

  result.assertNoConstraints()

  return result.withoutValue();
}

type PatternStackEntry = { tag: 'pattern', pattern: TTKPattern } | { tag: 'done', pattern: TTKPattern, arity: number }
type CheckStackEntry = { type: TTKTerm, ctxLength: number }

function prettyPrintInSignature(term: TTKTerm, signature: Signature): string {
  return prettyPrintTTK(term, signature.map(s => s.name).reverse())
}

function constructorDone(pattern: TTKPattern, arity: number, checkTypeEntry: CheckStackEntry, checkStack: CheckStackEntry[], elabStack: TTKTerm[], workEnv: TCEnv<unknown>) {
  logInfo(() => `STEP DONE(${prettyPrintPattern(pattern)}, ${arity})`);

  const nextCheckTypeEntry = checkStack.pop() as CheckStackEntry
  assertDefined(nextCheckTypeEntry, 'No next check type')

  const checkType = checkTypeEntry.type
  const nextCheckType = nextCheckTypeEntry.type

  logInfo(() => `  Pop T -> ${prettyPrintInSignature(checkType, workEnv.signature.slice(0, checkTypeEntry.ctxLength))}`)
  logInfo(() => `  Peek T -> ${prettyPrintInSignature(nextCheckType, workEnv.signature.slice(0, nextCheckTypeEntry.ctxLength))}`)

  assertIsPi(nextCheckType, 'Next check type must be a Pi')
  assertIsNotPi(checkType, 'Check type should not be a Pi')

  const unifyLeft = shiftTerm(checkType, workEnv.signature.length - checkTypeEntry.ctxLength, 0)
  const unifyRight = shiftTerm(nextCheckType.domain, workEnv.signature.length - nextCheckTypeEntry.ctxLength, 0)

  logInfo(() => `  Unifying: ${workEnv.prettyPrint(unifyLeft)} = ${workEnv.prettyPrint(unifyRight)}`)

  const unifyResult = unifyTerms(unifyLeft, unifyRight)

  if (!unifyResult.success) {
    debugger
    throw new Error('TODO: unification failed')
  }

  if (unifyResult.metaConstraints.length > 0) {
    debugger
    throw new Error('Meta constraints should not be emitted in clause lhs elaboration')
  }

  const elabHead = mkConst(pattern.name, mkType(-1) /* HACK */)
  let elabTerm = elabHead
  if (arity > 0) {
    const elabArgs = elabStack.slice(elabStack.length - arity)
    elabStack.length -= arity
    elabTerm = mkAppSpine(elabHead, elabArgs)
  }
  elabStack.push(elabTerm)

  // Elab var indices are backwards compared to debruijn indices
  const adjustedElabTerm = transformVarsInTerm(elabTerm, (index) => {
    return mkVar(workEnv.signature.length - 1 - index)
  })

  const shiftAmount = workEnv.signature.length - nextCheckTypeEntry.ctxLength
  const adjustedBody = shiftTerm(nextCheckType.body, shiftAmount, 0)

  checkStack.push({ type: subst(shiftAmount, adjustedElabTerm, adjustedBody), ctxLength: workEnv.signature.length })

  for (const { varIndex, value } of enumerateAppliedSubstitutions(unifyResult.substitutions)) {
    logInfo(() => `    Apply: ${workEnv.prettyPrint(mkVar(varIndex))} -> ${workEnv.prettyPrint(value)}`)

    // Update these 2 before the signature
    applySubstitutionToCheckStackInPlace(checkStack, workEnv.signature.length, varIndex, value)
    applySubstitutionToElabStackInPlace(elabStack, workEnv.signature.length, varIndex, value)

    workEnv = workEnv.applySubstitutionToContextMetasAndConstraints(varIndex, value)
    logResultState(workEnv, undefined, checkStack, elabStack, '    AFTER APPLYING SUBSTITUTION:')
  }

  return workEnv.solveMetasAndConstraints({ liftMetasToFullContext: false })
}

function applySubstitutionToCheckStackInPlace(
  stack: CheckStackEntry[],
  mainSigLength: number,
  varIndex: number,
  value: TTKTerm
): CheckStackEntry[] {
  for (let i = 0; i < stack.length; i++) {
    const entry = stack[i];
    const m = entry.ctxLength;

    if (varIndex >= mainSigLength - m) {
      const localVarIndex = varIndex - (mainSigLength - m);
      const shiftAmount = m - mainSigLength;
      const shiftedValue = shiftAmount !== 0 ? shiftTerm(value, shiftAmount, 0) : value;

      const newTerm = subst(localVarIndex, shiftedValue, entry.type);
      // Mutate entry in place
      stack[i] = { type: newTerm, ctxLength: entry.ctxLength - 1 };
    }
    // else, leave entry as is
  }
  return stack;
}

function applySubstitutionToElabStackInPlace(
  stack: TTKTerm[],
  mainSigLength: number,
  varIndex: number,
  value: TTKTerm
): TTKTerm[] {
  const varLevel = mainSigLength - 1 - varIndex;

  const valueInLevels = transformVarsInTerm(value, (idx) => {
    const level = mainSigLength - 1 - idx;
    if (level > varLevel) {
      return mkVar(level - 1);
    } else {
      return mkVar(level);
    }
  });

  for (let i = 0; i < stack.length; i++) {
    stack[i] = transformVarsInTerm(stack[i], (level) => {
      if (level === varLevel) {
        return valueInLevels;
      } else if (level > varLevel) {
        return mkVar(level - 1);
      } else {
        return mkVar(level);
      }
    });
  }

  return stack;
}

function processPattern(pattern: TTKPattern, checkTypeEntry: CheckStackEntry, patternStack: PatternStackEntry[], checkStack: CheckStackEntry[], elabStack: TTKTerm[], workEnv: TCEnv<unknown>) {
  const checkType = checkTypeEntry.type
  assertIsPi(checkType, 'Check type must be a Pi')

  const binderName = checkType.name
  const binderType = checkType.domain
  const binderBody = checkType.body

  logInfo(() => `\nSTEP ${prettyPrintPattern(pattern)} against (${binderName}: ${workEnv.prettyPrint(binderType)}) -> ...`);

  let env = workEnv

  if (pattern.tag === 'PWild') {
    // Wildcard pattern: create a meta variable for the binding
    const { env: newWorkEnv, name } = addMetaVarInTCEnv(env, binderType)
    logInfo(() => `  Create meta ${name} : ${env.prettyPrint(binderType)}`);

    env = newWorkEnv
      .extendSignature(pattern.name, binderType)

    env = env.withConstraint({ meta: name, rhs: mkVar(env.signature.length - 1) })
    checkStack.push({ type: binderBody, ctxLength: env.signature.length })
    elabStack.push(mkVar(env.signature.length - 1))
  } else if (pattern.tag === 'PVar') {
    // Named variable pattern: validate and bind the variable
    // Validate pattern variable naming: must be lowercase, cannot shadow term definitions
    const patternNameEnv = env.withValue(pattern.name);
    validatePatternVarName(patternNameEnv);

    logInfo(() => `  Binding (${pattern.name} : ${env.prettyPrint(binderType)})`);
    env = env.extendSignature(pattern.name, binderType)

    checkStack.push({ type: binderBody, ctxLength: env.signature.length })
    elabStack.push(mkVar(env.signature.length - 1))
  } else {
    logInfo(() => `  Constructor pattern. Push DONE. Push sub-patterns. Push ${pattern.name} type`);

    checkStack.push({ type: checkType, ctxLength: env.signature.length })

    patternStack.push({ tag: 'done', pattern, arity: pattern.args.length })
    for (let i = pattern.args.length - 1; i >= 0; i--) {
      patternStack.push({ tag: 'pattern', pattern: pattern.args[i] })
    }

    checkStack.push({ type: env.getTypeDefinitionAssert(pattern.name).value, ctxLength: env.signature.length })
  }

  return env
}

/**
 * Validate pattern variables after LHS elaboration.
 *
 * Traverses the original patterns and elaborated terms in parallel to build a mapping
 * from de Bruijn indices to pattern variable names. Throws an error if:
 * - The same de Bruijn index is bound by multiple different names (e.g., A and A2 both map to #0)
 * - The same name is used multiple times (even if they refer to the same index)
 */
function assertPatternVarsValid(
  env: TCEnv<TTKPattern[]>,
  elabStack: TTKTerm[]
): void {
  const patterns = env.value;

  // Map from de Bruijn index to list of (name, indexPath) entries
  const varToNames = new Map<number, { name: string; path: IndexPath }[]>();

  function traverse(pattern: TTKPattern, elabTerm: TTKTerm, path: IndexPath): void {
    switch (pattern.tag) {
      case 'PVar': {
        // For PVar, the elabTerm should be a Var after elaboration
        if (elabTerm.tag === 'Var') {
          const varIndex = elabTerm.index;
          const existing = varToNames.get(varIndex);
          if (existing) {
            existing.push({ name: pattern.name, path });
          } else {
            varToNames.set(varIndex, [{ name: pattern.name, path }]);
          }
        }
        // If elabTerm is not a Var, the pattern variable unified with a complex term.
        // We skip these cases as we can't easily detect conflicts.
        break;
      }

      case 'PWild':
        // Wildcards don't have user-defined names, nothing to validate
        break;

      case 'PCtor': {
        // Extract the App spine from elabTerm
        const spine = extractAppSpine(elabTerm);

        if (spine.args.length !== pattern.args.length) {
          // This shouldn't happen if elaboration is correct
          throw new Error(
            `Internal error: PCtor arg count mismatch in pattern validation: ` +
            `pattern '${pattern.name}' has ${pattern.args.length} args, ` +
            `but elaborated term has ${spine.args.length} args`
          );
        }

        for (let i = 0; i < pattern.args.length; i++) {
          traverse(
            pattern.args[i],
            spine.args[i],
            [...path, fieldSeg('args'), arraySeg(i)]
          );
        }
        break;
      }
    }
  }

  // Traverse all top-level patterns paired with their elaborated terms
  for (let i = 0; i < patterns.length; i++) {
    traverse(patterns[i], elabStack[i], [arraySeg(i)]);
  }

  // Check for conflicts
  for (const [_varIndex, entries] of varToNames) {
    if (entries.length > 1) {
      const names = entries.map(e => e.name);
      const uniqueNames = [...new Set(names)];

      if (uniqueNames.length === 1) {
        // Same name used multiple times - duplicate name error
        const errorPath = entries[1].path; // Point to second occurrence
        throw new TCEnvError(
          `Duplicate pattern variable '${names[0]}': this name is already bound earlier in the pattern`,
          env.atIndexPath([...env.indexPath, ...errorPath])
        );
      } else {
        // Different names refer to same variable - conflict error
        const nameList = names.map(n => `'${n}'`).join(' and ');
        const errorPath = entries[1].path; // Point to second occurrence
        throw new TCEnvError(
          `Pattern variables ${nameList} refer to the same binding; use a single consistent name`,
          env.atIndexPath([...env.indexPath, ...errorPath])
        );
      }
    }
  }
}

function processMatchClauseLhs(termName: string, env: TCEnv<TTKPattern[]>, type: TTKTerm): TCEnv<unknown> {
  logInfo(() => `\n\nLHS: ${prettyPrintPattern({ tag: 'PCtor', name: termName, args: env.value })}`);
  const checkStack: CheckStackEntry[] = [{ type, ctxLength: env.signature.length }]
  const patternStack: PatternStackEntry[] = env.value.map(p => ({ tag: 'pattern' as const, pattern: p })).reverse()
  const elabStack: TTKTerm[] = []

  let workEnv: TCEnv<unknown> = env

  logInfo(() => `\n  ~~ INITIAL STATE ~~`)
  logInfo(() => `    P = [${patternStack.map(p => {
    if (p.tag === 'pattern') {
      return prettyPrintPattern(p.pattern)
    } else {
      return `DONE(${prettyPrintPattern(p.pattern)}, ${p.arity})`
    }
  }).join(', ')}]`)
  logInfo(() => `    T = [${checkStack.map(s => prettyPrintInSignature(s.type, env.signature.slice(0, s.ctxLength))).join(', ')}]`)

  while (patternStack.length > 0) {
    const patternEntry = patternStack.pop() as PatternStackEntry
    const checkTypeEntry = checkStack.pop() as CheckStackEntry

    if (!checkTypeEntry) {
      debugger
      throw new Error('No next check type')
    }

    if (patternEntry.tag === 'done') {
      workEnv = constructorDone(patternEntry.pattern, patternEntry.arity, checkTypeEntry, checkStack, elabStack, workEnv)
    } else {
      workEnv = processPattern(patternEntry.pattern, checkTypeEntry, patternStack, checkStack, elabStack, workEnv)
    }

    logResultState(workEnv, patternStack, checkStack, elabStack)
  }

  if (checkStack.length !== 1) {
    debugger
    throw new Error('Check stack not empty')
  }

  // Validate pattern variables: check for duplicate names or conflicting bindings
  assertPatternVarsValid(env, elabStack);

  workEnv = workEnv.solveMetasAndConstraints({ liftMetasToFullContext: true })

  return workEnv
}

function logResultState(workEnv: TCEnv<unknown>, patternStack: PatternStackEntry[] | undefined, checkStack: CheckStackEntry[], elabStack: TTKTerm[], header?: string) {
  logInfo(() => header ?? `\n  ~~ RESULT STATE ~~`)
  logInfo(() => `    Γ = ${workEnv.printSignature()}`)
  logInfo(() => `    Σ = ${workEnv.printMetas({ indentLevel: 8, innerIndentOffset: 2 })}`)
  logInfo(() => `    C = ${workEnv.printConstraints({ indentLevel: 8, innerIndentOffset: 2 })}`)
  if (patternStack) {
    logInfo(() => `    P = [${patternStack.map(p => {
      if (p.tag === 'pattern') {
        return prettyPrintPattern(p.pattern)
      } else {
        return `DONE(${prettyPrintPattern(p.pattern)}, ${p.arity})`
      }
    }).join(', ')}]`)
  }
  logInfo(() => `    T = ${printCollectionFancy(checkStack.map(s => {
    return `|${s.ctxLength}| >> ${prettyPrintInSignature(s.type, workEnv.signature.slice(0, s.ctxLength))}`
  }), '[', ']', ',', { indentLevel: 8, innerIndentOffset: 2 })}`)
  logInfo(() => `    E = ${printCollectionFancy(elabStack.map(s => prettyPrintTTK(s)), '[', ']', ',', { indentLevel: 8, innerIndentOffset: 2 })}`)
}