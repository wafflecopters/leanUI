/**
 * Fresh TT Compiler - A clean implementation of the compilation pipeline
 *
 * This module provides a simple interface for compiling TT source code
 * to elaborated kernel terms (TTK).
 */

import { groupByIndentation } from '../parser/indentation-grouper';
import { Parser, ParsedDeclaration, ParseError } from '../parser/parser';
import { elabToKernelWithMap, elabPatternToKernel, elabPatternToKernelWithMap, buildConstructorParamNames, setConstructorParamNames, resetWildcardCounter, extractConstructorParamNames, setCurrentTermParamNames, extractNamedArgMap, countParameters, reorderPatterns, hasNamedPatterns, applyVarPermutation, fixRhsForConstructorPatterns, ConstructorParamNames, NamedArgMap, NamedArgElabError } from './elab';
import { TTKTerm, TTKContext, prettyPrint as prettyPrintTTK, prettyPrintFormatted, TTKClause, TTKPattern, prettyPrintPattern, prettyPrintPatternList, mkPi, mkType } from './kernel';
import { TTerm, TPattern, TClause, mkPiTT, mkTypeTT, mkULitTT, mkConstTT, mkAppTT, mkVarTT, mkPropTT, mkHoleTT } from './surface';
import { validateDeclarations, emptySymbolContext, SymbolContext } from '../types/name-resolution';
import { resolvePatternsInDeclarations } from '../parser/pattern-resolution';
import { arraySeg, fieldSeg, appendPath, ElabMap, IndexPath, SourceMap, serializeIndexPath, deserializeIndexPath } from '../types/source-position'
import { checkType, inferType } from './checker';
import { addDefinition, addDefinitionInTCEnv, countPiBinders, createDefinitionsMap, createNamedArgInfoLookup, createNamedArgLookup, createTCEnv, DefinitionsMap, extractPiSpine, MatchPartIndex, setDefinitionValueInTCEnv, TCEnv, TCEnvError, TermDefinition, TermDefinitionPartIndex, validateTermNameNotDefined } from './term';
import { checkInductiveDeclaration } from './inductive';
import { recordToInductiveDefinition, generateProjections } from './record';
import { TTKRecordDef, TTKRecordField, TTKRecordParam } from './kernel';
import { elabToKernel, defaultRecordConstructorName } from './elab';
import { checkMatchClause, arePatternsAbsurd } from './patterns';
import { checkTotality, TotalityResult, CaseTree } from './totality';
import { checkStructuralRecursion } from './recursion';
import { desugarWithClauses, resetWithCounter } from './with-desugar';
import { subst } from './subst';
import type { TypeInfoMap } from './type-info';
import { createInitialEngine, TacticEngine } from '../tactics/tacticsEngine';
import { ExactTactic, AssumptionTactic, IntroTactic, IntrosTactic, ApplyTactic, Tactic } from '../tactics/tactic';
import { CasesTactic } from '../tactics/cases-tactic';
import { ReflexivityTactic } from '../tactics/reflexivity-tactic';
import { InductionTactic } from '../tactics/induction-tactic';
import { RewriteTactic } from '../tactics/rewrite-tactic';
import { SymmetryTactic } from '../tactics/symmetry-tactic';
import { TransitivityTactic } from '../tactics/transitivity-tactic';
import { CongTactic } from '../tactics/cong-tactic';
import { SubstTactic } from '../tactics/subst-tactic';
import { FocusTactic } from '../tactics/focus-tactic';
import { TacticCommand, TTacticBlock } from './surface';
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
  | { kind: 'declarations'; declarations: ParsedDeclaration[]; sourceMaps: SourceMap[]; sourceLines: string[]; startLine: number; posOffset: number }
  | { kind: 'comment'; sourceLines: string[]; startLine: number; posOffset: number }
  | { kind: 'error'; errors: ParseError[]; sourceLines: string[]; startLine: number; posOffset: number };

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
  /** For with-clause auxiliaries: metadata needed for scrutinee type resolution */
  withScrutineeCount?: number;
  withScrutineeExprs?: TTerm[];
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

  // Record-specific surface info for syntax highlighting
  isRecord?: boolean;
  surfaceParams?: Array<{ name: string; type: TTerm }>;
  surfaceFields?: Array<{ name: string; type: TTerm }>;
  surfaceExtendsExprs?: TTerm[];

  // Elaborated kernel terms
  kernelType?: TTKTerm;
  kernelValue?: TTKTerm;
  kernelConstructors?: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }>;

  // For term declarations: map from parameter names to positions
  namedArgMap?: NamedArgMap;

  // For inductive types: positions that are indices (not parameters)
  indexPositions?: number[];

  // Pretty-printed versions for display
  prettyType?: string;
  prettyValue?: string;
  prettyConstructors?: Array<{ name: string; prettyType: string }>;

  // Record-specific: generated projection signatures
  prettyProjections?: Array<{ name: string; prettyType: string }>;

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

  // Whether this declaration is a with-clause auxiliary
  isWithAuxiliary?: boolean;

  // For with-clause auxiliaries: metadata needed for scrutinee type resolution
  withScrutineeCount?: number;
  withScrutineeExprs?: TTerm[];

  // Errors promoted from failed with-clause auxiliaries (displayed on the main declaration)
  withClauseErrors?: TCEnvError[];

  // ElabMap from failed auxiliaries, for mapping withClauseErrors to source ranges
  withClauseElabMap?: ElabMap;

  // Type info map for type-at-cursor feature
  typeInfoMap?: TypeInfoMap;
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
  definitions: DefinitionsMap;  // For debugging/testing
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
function adjustSourceMapToAbsolute(sourceMap: SourceMap, blockStartLine: number, posOffset: number): SourceMap {
  if (blockStartLine === 1 && posOffset === 0) {
    // No adjustment needed for first block
    return sourceMap;
  }

  const lineOffset = blockStartLine - 1;
  const adjusted = new Map<string, { start: { line: number; col: number; pos: number }; end: { line: number; col: number; pos: number } }>();

  for (const [key, range] of sourceMap) {
    adjusted.set(key, {
      start: {
        line: range.start.line + lineOffset,
        col: range.start.col,
        pos: range.start.pos + posOffset
      },
      end: {
        line: range.end.line + lineOffset,
        col: range.end.col,
        pos: range.end.pos + posOffset
      }
    });
  }

  return adjusted;
}

/**
 * Compute the character offset of a 1-based line number in a source string.
 * Returns the index of the first character of the given line.
 */
function lineToCharOffset(source: string, line: number): number {
  let offset = 0;
  for (let i = 1; i < line; i++) {
    const nl = source.indexOf('\n', offset);
    if (nl < 0) return source.length;
    offset = nl + 1;
  }
  return offset;
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
export type SemanticTokenType = 'termName' | 'constName' | 'boundVar' | 'patternVar' | 'absurd' | 'namedBrace' | 'directive' | 'directiveValue';

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
export function extractSemanticTokens(result: CompileResult, source?: string): SemanticToken[] {
  const tokens: SemanticToken[] = [];

  // Extract directive tokens from source if provided
  if (source) {
    tokens.push(...extractDirectiveTokens(source));
  }

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
        } else {
          // Simple definitions (e.g., "fox = expr") also have defName recorded
          // when merged with a type signature line
          addSemanticTokenDirect(
            ['value', 'clauses', 0, 'defName'],
            decl.sourceMap,
            block.startLine,
            'termName',
            tokens
          );
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

      // Process record-specific tokens
      if (decl.isRecord) {
        // Record constructor name (e.g., "MkPoint" in "constructor MkPoint")
        addSemanticTokenDirect(['constructorName'], decl.sourceMap, block.startLine, 'constName', tokens);

        // Record parameter names and types (e.g., "u" and "A" in "{u : ULevel} (A : Type u)")
        if (decl.surfaceParams) {
          for (let i = 0; i < decl.surfaceParams.length; i++) {
            addSemanticTokenDirect(['params', i, 'name'], decl.sourceMap, block.startLine, 'boundVar', tokens);
            collectSemanticTokensFromSurfaceTerm(
              decl.surfaceParams[i].type,
              decl.sourceMap,
              block.startLine,
              ['params', i, 'type'],
              tokens
            );
          }
        }

        // Record field names at definition site (e.g., "x" and "y" in "x : Nat" and "y : Nat")
        if (decl.surfaceFields) {
          for (let i = 0; i < decl.surfaceFields.length; i++) {
            addSemanticTokenDirect(['fields', i, 'name'], decl.sourceMap, block.startLine, 'termName', tokens);
            // Also process the field type
            collectSemanticTokensFromSurfaceTerm(
              decl.surfaceFields[i].type,
              decl.sourceMap,
              block.startLine,
              ['fields', i, 'type'],
              tokens
            );
          }
        }

        // Process record extends expressions (e.g., "Monoid A" in "extends Monoid A")
        if (decl.surfaceExtendsExprs) {
          for (let i = 0; i < decl.surfaceExtendsExprs.length; i++) {
            collectSemanticTokensFromSurfaceTerm(
              decl.surfaceExtendsExprs[i],
              decl.sourceMap,
              block.startLine,
              ['extends', i],
              tokens
            );
          }
        }
      }
    }
  }

  return tokens;
}

/**
 * Extract directive tokens from source text for syntax highlighting.
 * Directives like @test, @name, @import, @error, @assumeK get highlighted.
 */
export function extractDirectiveTokens(source: string): SemanticToken[] {
  const tokens: SemanticToken[] = [];
  const lines = source.split('\n');

  for (let lineIndex = 0; lineIndex < lines.length; lineIndex++) {
    const line = lines[lineIndex];

    // Match directive: @directive=value or @directive value or @directive "value" (with optional -- comment prefix)
    const directiveMatch = line.match(/^(\s*)(?:--\s*)?(@\w+)(?:=(\w+)|\s+(\w+)|\s+"([^"]*)")?/);
    if (!directiveMatch) continue;

    const [, , directive, equalsValue, spaceValue, quotedValue] = directiveMatch;
    const value = equalsValue || spaceValue || quotedValue;

    // Calculate column based on where the @ appears in the original line
    const atIndex = line.indexOf('@');
    const column = atIndex >= 0 ? atIndex + 1 : 0;

    // Add token for the directive name (e.g., @test, @assumeK)
    tokens.push({
      line: lineIndex + 1,
      column,
      length: directive.length,
      type: 'directive'
    });

    // Add token for the directive value (e.g., false, true, "test name")
    if (value) {
      const valueIndex = line.indexOf(value, atIndex + directive.length);
      if (valueIndex >= 0) {
        tokens.push({
          line: lineIndex + 1,
          column: valueIndex + 1,
          length: value.length,
          type: 'directiveValue'
        });
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
      // Recurse into level (e.g., the "u" in "Type u")
      collectSemanticTokensFromSurfaceTerm(term.level, sourceMap, blockStartLine, [...path, 'level'], tokens);
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
      // Note: parser records let value at path bindings[0].value, not binderKind.defVal
      if (term.binderKind.tag === 'BLetTT') {
        collectSemanticTokensFromSurfaceTerm(term.binderKind.defVal, sourceMap, blockStartLine, [...path, 'bindings', 0, 'value'], tokens);
      }
      break;

    case 'App':
      collectSemanticTokensFromSurfaceTerm(term.fn, sourceMap, blockStartLine, [...path, 'fn'], tokens);
      collectSemanticTokensFromSurfaceTerm(term.arg, sourceMap, blockStartLine, [...path, 'arg'], tokens);
      // If named argument (e.g., f { A := x }), emit tokens for braces and name
      if (term.argName) {
        addSemanticTokenDirect([...path, 'arg', 'name'], sourceMap, blockStartLine, 'boundVar', tokens);
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
            // Emit token for the named argument name (e.g., "a" in {a:=Succ p})
            addSemanticTokenDirect([...path, 'clauses', i, 'patterns', j, 'name'], sourceMap, blockStartLine, 'boundVar', tokens);
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
        if (clause.rhs.tag === 'WithClause') {
          // With-clause RHS: the parser records with-clause sub-paths under
          // 'withClauses' relative to the Match clause, not under 'rhs.clauses'.
          const wc = clause.rhs as any;
          const clausePath = [...path, 'clauses', i];
          // Process scrutinees (recorded at clause.scrutinee by parser)
          for (let si = 0; si < wc.scrutinees.length; si++) {
            collectSemanticTokensFromSurfaceTerm(wc.scrutinees[si], sourceMap, blockStartLine, [...clausePath, 'scrutinee'], tokens);
          }
          // Process with-clauses
          for (let wi = 0; wi < wc.clauses.length; wi++) {
            const wcClause = wc.clauses[wi];
            const wcPath = [...clausePath, 'withClauses', wi];
            const wcNamedPatternCount = wcClause.namedPatterns?.length || 0;
            const wcTotalPatternCount = wcClause.patterns.length + wcNamedPatternCount;
            // Emit brace tokens for all pattern indices (named patterns have braces)
            for (let pj = 0; pj < wcTotalPatternCount; pj++) {
              addSemanticTokenDirect([...wcPath, 'patterns', pj, 'openBrace'], sourceMap, blockStartLine, 'namedBrace', tokens);
              addSemanticTokenDirect([...wcPath, 'patterns', pj, 'closeBrace'], sourceMap, blockStartLine, 'namedBrace', tokens);
            }
            // Process positional patterns (offset by namedPatternCount)
            for (let pj = 0; pj < wcClause.patterns.length; pj++) {
              const sourceMapIndex = pj + wcNamedPatternCount;
              collectSemanticTokensFromSurfacePattern(
                wcClause.patterns[pj],
                sourceMap,
                blockStartLine,
                [...wcPath, 'patterns', sourceMapIndex],
                tokens
              );
            }
            // Process named patterns at indices 0..namedPatternCount-1
            if (wcClause.namedPatterns) {
              for (let pj = 0; pj < wcClause.namedPatterns.length; pj++) {
                addSemanticTokenDirect([...wcPath, 'patterns', pj, 'name'], sourceMap, blockStartLine, 'boundVar', tokens);
                collectSemanticTokensFromSurfacePattern(
                  wcClause.namedPatterns[pj].pattern,
                  sourceMap,
                  blockStartLine,
                  [...wcPath, 'patterns', pj, 'pattern'],
                  tokens
                );
              }
            }
            // Process RHS (could be nested WithClause or a normal term)
            if (wcClause.rhs.tag === 'WithClause') {
              // Nested with: the parser records nested with RHS expressions at
              // the same 'rhs' path, so we can still extract tokens from them.
              collectSemanticTokensFromSurfaceTerm(
                wcClause.rhs,
                sourceMap,
                blockStartLine,
                [...wcPath, 'rhs'],
                tokens
              );
            } else {
              collectSemanticTokensFromSurfaceTerm(
                wcClause.rhs,
                sourceMap,
                blockStartLine,
                [...wcPath, 'rhs'],
                tokens
              );
            }
          }
        } else {
          collectSemanticTokensFromSurfaceTerm(
            clause.rhs,
            sourceMap,
            blockStartLine,
            [...path, 'clauses', i, 'rhs'],
            tokens
          );
        }
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

    case 'PCtor': {
      // Constructor pattern - white for the constructor name
      // For patterns with args, the name is recorded at path.name
      // For zero-arg patterns, the name is recorded at path itself
      const namedArgCount = pattern.namedArgs?.length || 0;
      if (pattern.args.length > 0 || namedArgCount > 0) {
        addSemanticTokenDirect([...path, 'name'], sourceMap, blockStartLine, 'constName', tokens);

        // Emit brace tokens for all arg indices (named args have braces in sourceMap)
        const totalArgCount = pattern.args.length + namedArgCount;
        for (let i = 0; i < totalArgCount; i++) {
          addSemanticTokenDirect([...path, 'args', i, 'openBrace'], sourceMap, blockStartLine, 'namedBrace', tokens);
          addSemanticTokenDirect([...path, 'args', i, 'closeBrace'], sourceMap, blockStartLine, 'namedBrace', tokens);
        }

        // Positional args: sourceMap indices are offset by namedArgCount
        // (named args come first in parser argIndex order)
        for (let i = 0; i < pattern.args.length; i++) {
          const sourceMapIndex = i + namedArgCount;
          collectSemanticTokensFromSurfacePattern(
            pattern.args[i],
            sourceMap,
            blockStartLine,
            [...path, 'args', sourceMapIndex],
            tokens
          );
        }

        // Named args at indices 0..namedArgCount-1
        if (pattern.namedArgs) {
          for (let i = 0; i < pattern.namedArgs.length; i++) {
            // Emit token for the named arg label (e.g., "m" in {m:=a})
            addSemanticTokenDirect([...path, 'args', i, 'name'], sourceMap, blockStartLine, 'boundVar', tokens);
            // Recurse into the inner pattern (e.g., "a" in {m:=a}, or "Succ p" in {m:=Succ p})
            collectSemanticTokensFromSurfacePattern(
              pattern.namedArgs[i].pattern,
              sourceMap,
              blockStartLine,
              [...path, 'args', i, 'pattern'],
              tokens
            );
          }
        }
      } else {
        // Zero-arg constructor: the whole pattern range IS the constructor name
        addSemanticTokenDirect(path, sourceMap, blockStartLine, 'constName', tokens);
      }
      break;
    }
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
      // Skip with-clause auxiliaries — their holes are already collected via the main declaration
      if ((decl as any).isWithAuxiliary) continue;

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
        collectHolesFromSurfaceTerm(term.binderKind.defVal, sourceMap, blockStartLine, [...path, 'bindings', 0, 'value'], holes);
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

    case 'WithClause':
    case 'Match': {
      if (term.tag === 'Match') {
        collectHolesFromSurfaceTerm(term.scrutinee, sourceMap, blockStartLine, [...path, 'scrutinee'], holes);
      }
      // For WithClause, term.clauses are the with-branches; for Match, term.clauses are match clauses.
      // WithClause also has scrutinees to walk.
      const isWith = term.tag === 'WithClause';
      const clauses = (term as any).clauses as { rhs: TTerm; patterns: any[] }[];
      if (isWith) {
        const wc = term as any;
        for (let si = 0; si < wc.scrutinees.length; si++) {
          collectHolesFromSurfaceTerm(wc.scrutinees[si], sourceMap, blockStartLine, [...path, 'scrutinee'], holes);
        }
      }
      for (let i = 0; i < clauses.length; i++) {
        const clause = clauses[i];
        if (isWith) {
          // Walking with-clause branches: path uses 'withClauses' convention
          const wcPath = [...path, 'withClauses', i];
          collectHolesFromSurfaceTerm(clause.rhs, sourceMap, blockStartLine, [...wcPath, 'rhs'], holes);
        } else if (clause.rhs.tag === 'WithClause') {
          // Match clause whose RHS is a WithClause: recurse with clausePath context
          const clausePath = [...path, 'clauses', i];
          collectHolesFromSurfaceTerm(clause.rhs, sourceMap, blockStartLine, clausePath, holes);
        } else {
          collectHolesFromSurfaceTerm(clause.rhs, sourceMap, blockStartLine, [...path, 'clauses', i, 'rhs'], holes);
        }
      }
      break;
    }
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
    const posOffset = lineToCharOffset(source, block.startLine);

    // Handle comment blocks
    if (block.isComment) {
      parsedBlocks.push({
        kind: 'comment',
        sourceLines: block.lines,
        startLine: block.startLine,
        posOffset
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
          name: err.name,
          message: err.message,
          line: err.line + block.startLine - 1,
          col: err.col
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
        startLine: block.startLine,
        posOffset
      });
      continue;
    }

    parsedBlocks.push({
      kind: 'declarations',
      declarations,
      sourceMaps,
      sourceLines: block.lines,
      startLine: block.startLine,
      posOffset
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
 * Convert a tactic command to a Tactic object.
 * Args can be TTerm (un-elaborated) or TTKTerm (elaborated).
 */
function tacticCommandToTactic(cmd: { name: string; args: Array<TTerm | TTKTerm>; focusedTactics?: Tactic[] }): Tactic {
  switch (cmd.name) {
    case 'focus':
      if (!cmd.focusedTactics || cmd.focusedTactics.length === 0) {
        throw new Error(`'focus' tactic requires nested tactics`);
      }
      return new FocusTactic(cmd.focusedTactics);

    case 'exact':
      if (cmd.args.length !== 1) {
        throw new Error(`'exact' tactic requires exactly 1 argument, got ${cmd.args.length}`);
      }
      // args[0] is a TTKTerm at this point (elaborated by caller)
      return new ExactTactic(cmd.args[0] as TTKTerm);

    case 'assumption':
      if (cmd.args.length !== 0) {
        throw new Error(`'assumption' tactic requires no arguments, got ${cmd.args.length}`);
      }
      return new AssumptionTactic();

    case 'intro':
      if (cmd.args.length > 1) {
        throw new Error(`'intro' tactic requires 0 or 1 arguments, got ${cmd.args.length}`);
      }
      const introName = cmd.args.length === 1 && cmd.args[0].tag === 'Const'
        ? (cmd.args[0] as any).name
        : undefined;
      return new IntroTactic(introName);

    case 'intros':
      // Arguments should all be Const nodes (identifiers)
      const names = cmd.args.map(arg => {
        if (arg.tag !== 'Const') {
          throw new Error(`'intros' tactic arguments must be identifiers, got ${arg.tag}`);
        }
        return (arg as any).name;
      });
      return new IntrosTactic(names.length > 0 ? names : undefined);

    case 'apply':
      if (cmd.args.length !== 1) {
        throw new Error(`'apply' tactic requires exactly 1 argument, got ${cmd.args.length}`);
      }
      // args[0] is a TTKTerm at this point (elaborated by caller)
      return new ApplyTactic(cmd.args[0] as TTKTerm);

    case 'cases':
      if (cmd.args.length !== 1) {
        throw new Error(`'cases' tactic requires exactly 1 argument, got ${cmd.args.length}`);
      }
      // args[0] is a TTKTerm at this point (elaborated by caller)
      return new CasesTactic(cmd.args[0] as TTKTerm);

    case 'induction':
      if (cmd.args.length !== 1) {
        throw new Error(`'induction' tactic requires exactly 1 argument, got ${cmd.args.length}`);
      }
      // args[0] is a TTKTerm at this point (elaborated by caller)
      return new InductionTactic(cmd.args[0] as TTKTerm);

    case 'reflexivity':
      if (cmd.args.length !== 0) {
        throw new Error(`'reflexivity' tactic requires no arguments, got ${cmd.args.length}`);
      }
      return new ReflexivityTactic();

    case 'rewrite':
      if (cmd.args.length !== 1) {
        throw new Error(`'rewrite' tactic requires exactly 1 argument (an equality proof), got ${cmd.args.length}`);
      }
      // args[0] is a TTKTerm at this point (elaborated by caller)
      return new RewriteTactic(cmd.args[0] as TTKTerm);

    case 'symmetry':
      if (cmd.args.length !== 0) {
        throw new Error(`'symmetry' tactic requires no arguments, got ${cmd.args.length}`);
      }
      return new SymmetryTactic();

    case 'transitivity':
      if (cmd.args.length !== 1) {
        throw new Error(`'transitivity' tactic requires exactly 1 argument (middle term), got ${cmd.args.length}`);
      }
      // args[0] is a TTKTerm at this point (elaborated by caller)
      return new TransitivityTactic(cmd.args[0] as TTKTerm);

    case 'cong':
      if (cmd.args.length !== 1) {
        throw new Error(`'cong' tactic requires exactly 1 argument (equality proof or function), got ${cmd.args.length}`);
      }
      // args[0] is a TTKTerm at this point (elaborated by caller)
      return new CongTactic(cmd.args[0] as TTKTerm);

    case 'subst':
      if (cmd.args.length !== 1) {
        throw new Error(`'subst' tactic requires exactly 1 argument (equality proof), got ${cmd.args.length}`);
      }
      // args[0] is a TTKTerm at this point (elaborated by caller)
      return new SubstTactic(cmd.args[0] as TTKTerm);

    default:
      throw new Error(`Unknown tactic: ${cmd.name}`);
  }
}

/**
 * Elaborate a TacticBlock to a kernel term by executing the tactics.
 *
 * @param tacticBlock - The surface-level tactic block
 * @param expectedType - The expected type for the proof (kernel term)
 * @param definitions - Definitions map for type checking
 * @param elabMap - Elaboration map for elaborating tactic arguments
 * @param context - Optional typing context (for nested proofs)
 * @returns The proof term (kernel term)
 */
function elaborateTacticBlock(
  tacticBlock: TTacticBlock,
  expectedType: TTKTerm,
  definitions: DefinitionsMap,
  elabMap: ElabMap,
  context: TTKContext = []
): TTKTerm {
  // Check if empty
  if (tacticBlock.tactics.length === 0) {
    throw new Error('Tactic proof has no tactics (unsolved goals)');
  }

  // Create initial tactic engine
  let engine = createInitialEngine(expectedType, context, definitions);

  // Helper: look up implicit param names for a definition
  const namedArgLookup = createNamedArgLookup(definitions);

  // Helper: convert a surface App term to kernel, inserting Holes for implicit params.
  // When the head of an application chain is a Const with implicit params (namedArgMap),
  // we need to insert Holes so the type checker can create metas for them.
  // Without this, `Just x` becomes `App(Just, x)` which fails because the type checker
  // tries to apply `x` to the first (implicit) parameter `{A : Type}`.
  function insertImplicitHolesForApp(
    term: TTerm,
    convertTerm: (t: TTerm, depth: number) => TTKTerm,
    depth: number
  ): TTKTerm {
    // Collect the application spine
    const args: TTerm[] = [];
    let head: TTerm = term;
    while (head.tag === 'App') {
      args.unshift(head.arg);
      head = head.fn;
    }

    // Convert the head
    let kernelHead = convertTerm(head, depth);

    // If the head is a Const with implicit params, insert Holes for them
    if (kernelHead.tag === 'Const') {
      const namedArgs = namedArgLookup(kernelHead.name);
      if (namedArgs) {
        for (const [paramName] of namedArgs) {
          kernelHead = { tag: 'App', fn: kernelHead, arg: { tag: 'Hole', id: '_implicit_' + paramName } };
        }
      }
    }

    // Apply the explicit args
    let result = kernelHead;
    for (const arg of args) {
      result = { tag: 'App', fn: result, arg: convertTerm(arg, depth) };
    }
    return result;
  }

  // Execute each tactic, elaborating arguments in the current goal's context
  for (const cmd of tacticBlock.tactics) {
    const goal = engine.getFocusedGoal();
    const goalId = engine.getFocusedGoalId();

    if (!goal || !goalId) {
      throw new Error('Tactic proof: no active goal');
    }

    // Elaborate arguments in the CURRENT goal's context
    const elabArgs: Array<TTerm | TTKTerm> = cmd.args.map(arg => {
      // For intro/intros, keep names as Const (don't elaborate)
      if (cmd.name === 'intro' || cmd.name === 'intros') {
        return arg;
      }

      // For apply/exact/etc, elaborate in the goal's context
      // Build a name map from context for de Bruijn conversion
      const nameContext: string[] = goal.ctx.map(binding => binding.name);

      // Helper to recursively convert Const to Var based on context
      // This walks the surface term and resolves names to de Bruijn indices
      function surfaceToKernel(term: TTerm, depth: number = 0): TTKTerm {
        switch (term.tag) {
          case 'Var':
            // Already a de Bruijn index (shouldn't happen in surface syntax from parser)
            return { tag: 'Var', index: term.index };

          case 'Const': {
            // Look up the name in the context (most recent first)
            for (let i = nameContext.length - 1; i >= 0; i--) {
              if (nameContext[i] === term.name) {
                // Found in local context! Convert to de Bruijn index
                const index = nameContext.length - 1 - i + depth;
                return { tag: 'Var', index };
              }
            }
            // Not found in context, keep as Const (global definition)
            return { tag: 'Const', name: term.name };
          }

          case 'App': {
            // Insert Holes for implicit params when head is a Const with namedArgMap
            return insertImplicitHolesForApp(term, surfaceToKernel, depth);
          }

          case 'Sort': {
            // Elaborate the level
            return {
              tag: 'Sort',
              level: surfaceToKernel(term.level, depth) as any
            };
          }

          case 'Hole':
            return { tag: 'Hole', id: term.id };

          case 'ULevel':
            return { tag: 'ULevel' };

          case 'ULit':
            return { tag: 'ULit', n: term.n };

          case 'UOmega':
            return { tag: 'UOmega' };

          // For complex terms, just use standard elaboration
          // (Binder, Match, etc. are unlikely in tactic arguments)
          default:
            return elabToKernelWithMap(term, elabMap, [], []);
        }
      }

      return surfaceToKernel(arg);
    });

    // Elaborate focused tactics (for bullet syntax)
    let elabFocusedTactics: Tactic[] | undefined;
    if (cmd.focusedTactics && cmd.focusedTactics.length > 0) {
      elabFocusedTactics = cmd.focusedTactics.map(focusedCmd => {
        // Recursively elaborate each focused tactic
        const focusedElabArgs: Array<TTerm | TTKTerm> = focusedCmd.args.map(arg => {
          if (focusedCmd.name === 'intro' || focusedCmd.name === 'intros') {
            return arg;
          }
          const nameContext: string[] = goal.ctx.map(binding => binding.name);
          function surfaceToKernel(term: TTerm, depth: number = 0): TTKTerm {
            switch (term.tag) {
              case 'Var':
                return { tag: 'Var', index: term.index };
              case 'Const': {
                for (let i = nameContext.length - 1; i >= 0; i--) {
                  if (nameContext[i] === term.name) {
                    const index = nameContext.length - 1 - i + depth;
                    return { tag: 'Var', index };
                  }
                }
                return { tag: 'Const', name: term.name };
              }
              case 'App':
                return insertImplicitHolesForApp(term, surfaceToKernel, depth);
              case 'Sort':
                return { tag: 'Sort', level: surfaceToKernel(term.level, depth) as any };
              case 'Hole':
                return { tag: 'Hole', id: term.id };
              case 'ULevel':
                return { tag: 'ULevel' };
              case 'ULit':
                return { tag: 'ULit', n: term.n };
              case 'UOmega':
                return { tag: 'UOmega' };
              default:
                return elabToKernelWithMap(term, elabMap, [], []);
            }
          }
          return surfaceToKernel(arg);
        });
        return tacticCommandToTactic({ name: focusedCmd.name, args: focusedElabArgs });
      });
    }

    // Convert command to Tactic object with elaborated args
    const tactic = tacticCommandToTactic({ name: cmd.name, args: elabArgs, focusedTactics: elabFocusedTactics });

    const result = tactic.apply(engine, goal, goalId);

    if (!result.success) {
      throw new Error(`Tactic '${tactic.name}' failed: ${result.error}`);
    }

    engine = result.newEngine;

    // Handle structured cases/induction: if cmd has caseBranches, apply each branch's tactics to matching goals
    if ((cmd.name === 'cases' || cmd.name === 'induction') && (cmd as any).caseBranches) {
      const caseBranches = (cmd as any).caseBranches as Array<{ constructor: string; params: string[]; tactics: TacticCommand[] }>;

      for (const branch of caseBranches) {
        // Find the goal with matching caseTag
        const branchGoalId = engine.goals.find(gid => {
          const meta = engine.metaVars.get(gid);
          return meta && meta.caseTag === branch.constructor;
        });

        if (!branchGoalId) {
          throw new Error(`Structured cases: no goal found for constructor '${branch.constructor}'`);
        }

        // Set focus to this branch goal
        const branchGoalIndex = engine.goals.indexOf(branchGoalId);
        engine = engine.withUpdates({ focusIndex: branchGoalIndex });

        // Build paramNameMap once from the initial branch context (before any branch tactics run).
        // Pattern params (e.g., 'n'' in '| Succ n' IH =>') map to the actual context names
        // assigned by the cases/induction tactic. This mapping must stay fixed even as later
        // tactics (like intro) extend the context.
        {
          const initialBranchGoal = engine.getFocusedGoal()!;
          const initialCtx: string[] = initialBranchGoal.ctx.map(b => b.name);
          const paramNameMap = new Map<string, string>();
          for (let i = 0; i < branch.params.length; i++) {
            const patternParamName = branch.params[i];
            const ctxIndex = initialCtx.length - branch.params.length + i;
            if (ctxIndex >= 0 && ctxIndex < initialCtx.length) {
              paramNameMap.set(patternParamName, initialCtx[ctxIndex]);
            }
          }

        // Apply the branch's tactics
        for (const branchTactic of branch.tactics) {
          const branchGoal = engine.getFocusedGoal();
          const branchGoalId2 = engine.getFocusedGoalId();

          if (!branchGoal || !branchGoalId2) {
            throw new Error(`Structured cases: no active goal for constructor '${branch.constructor}'`);
          }

          // Rebuild name context from current goal (may have grown via intro)
          const branchNameContext: string[] = branchGoal.ctx.map(b => b.name);

          function branchSurfaceToKernel(term: TTerm, depth: number = 0): TTKTerm {
            switch (term.tag) {
              case 'Var':
                return { tag: 'Var', index: term.index };

              case 'Const': {
                // First check if this is a pattern param name
                const mappedName = paramNameMap.get(term.name);
                const lookupName = mappedName || term.name;

                for (let i = branchNameContext.length - 1; i >= 0; i--) {
                  if (branchNameContext[i] === lookupName) {
                    const index = branchNameContext.length - 1 - i + depth;
                    return { tag: 'Var', index };
                  }
                }
                return { tag: 'Const', name: term.name };
              }

              case 'App':
                return insertImplicitHolesForApp(term, branchSurfaceToKernel, depth);

              default:
                return elabToKernelWithMap(term, elabMap, [], []);
            }
          }

          const branchElabArgs: Array<TTerm | TTKTerm> = branchTactic.args.map(arg => {
            if (branchTactic.name === 'intro' || branchTactic.name === 'intros') {
              return arg;
            }
            return branchSurfaceToKernel(arg);
          });

          const branchTacticObj = tacticCommandToTactic({ name: branchTactic.name, args: branchElabArgs });
          const branchResult = branchTacticObj.apply(engine, branchGoal, branchGoalId2);

          if (!branchResult.success) {
            throw new Error(`Structured cases (${branch.constructor}): tactic '${branchTactic.name}' failed: ${branchResult.error}`);
          }

          engine = branchResult.newEngine;

          // Handle nested structured cases/induction: if this branch tactic itself
          // has caseBranches (e.g., nested `cases n with | Zero => ... | Succ m => ...`),
          // process them recursively
          if ((branchTactic.name === 'cases' || branchTactic.name === 'induction') && (branchTactic as any).caseBranches) {
            const nestedBranches = (branchTactic as any).caseBranches as Array<{ constructor: string; params: string[]; tactics: TacticCommand[] }>;
            for (const nestedBranch of nestedBranches) {
              const nestedGoalId = engine.goals.find(gid => {
                const meta = engine.metaVars.get(gid);
                return meta && meta.caseTag === nestedBranch.constructor;
              });
              if (!nestedGoalId) {
                throw new Error(`Structured cases: no goal found for nested constructor '${nestedBranch.constructor}'`);
              }
              const nestedGoalIndex = engine.goals.indexOf(nestedGoalId);
              engine = engine.withUpdates({ focusIndex: nestedGoalIndex });

              for (const nestedTactic of nestedBranch.tactics) {
                const nestedGoal = engine.getFocusedGoal();
                const nestedGoalId2 = engine.getFocusedGoalId();
                if (!nestedGoal || !nestedGoalId2) {
                  throw new Error(`Structured cases: no active goal for nested constructor '${nestedBranch.constructor}'`);
                }

                // Build name context with nested pattern param mapping
                const nestedNameContext: string[] = nestedGoal.ctx.map(b => b.name);
                const nestedParamNameMap = new Map<string, string>();
                // Include parent branch params
                for (const [k, v] of paramNameMap) {
                  nestedParamNameMap.set(k, v);
                }
                for (let i = 0; i < nestedBranch.params.length; i++) {
                  const patternParamName = nestedBranch.params[i];
                  const ctxIndex = nestedNameContext.length - nestedBranch.params.length + i;
                  if (ctxIndex >= 0 && ctxIndex < nestedNameContext.length) {
                    nestedParamNameMap.set(patternParamName, nestedNameContext[ctxIndex]);
                  }
                }

                function nestedSurfaceToKernel(term: TTerm, depth: number = 0): TTKTerm {
                  switch (term.tag) {
                    case 'Var':
                      return { tag: 'Var', index: term.index };
                    case 'Const': {
                      const mappedName = nestedParamNameMap.get(term.name);
                      const lookupName = mappedName || term.name;
                      for (let i = nestedNameContext.length - 1; i >= 0; i--) {
                        if (nestedNameContext[i] === lookupName) {
                          const index = nestedNameContext.length - 1 - i + depth;
                          return { tag: 'Var', index };
                        }
                      }
                      return { tag: 'Const', name: term.name };
                    }
                    case 'App':
                      return insertImplicitHolesForApp(term, nestedSurfaceToKernel, depth);
                    default:
                      return elabToKernelWithMap(term, elabMap, [], []);
                  }
                }

                const nestedElabArgs: Array<TTerm | TTKTerm> = nestedTactic.args.map(arg => {
                  if (nestedTactic.name === 'intro' || nestedTactic.name === 'intros') {
                    return arg;
                  }
                  return nestedSurfaceToKernel(arg);
                });

                const nestedTacticObj = tacticCommandToTactic({ name: nestedTactic.name, args: nestedElabArgs });
                const nestedResult = nestedTacticObj.apply(engine, nestedGoal, nestedGoalId2);
                if (!nestedResult.success) {
                  throw new Error(`Structured cases (${nestedBranch.constructor}): tactic '${nestedTactic.name}' failed: ${nestedResult.error}`);
                }
                engine = nestedResult.newEngine;
              }
            }
          }
        }
        } // close paramNameMap scope
      }
    }
  }

  // Check that all goals are solved
  const remainingGoals = engine.getUnsolvedGoals();
  if (remainingGoals.length > 0) {
    throw new Error(`Tactic proof has unsolved goals: ${remainingGoals.length} remaining`);
  }

  // Zonk (substitute solved metas) to get the final proof term
  return engine.zonk();
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
      const sourceMap = adjustSourceMapToAbsolute(block.sourceMaps[declIndex], block.startLine, block.posOffset);
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
          // Check if value is a TacticBlock - skip elaboration here, will be handled during type-checking
          if (decl.value.tag === 'TacticBlock') {
            // TacticBlock will be elaborated during type-checking when we have definitions
            kernelValue = undefined;
          } else {
            const valuePath: IndexPath = [{ kind: 'field', name: 'value' }];
            // Extract namedArgMap and totalArity from type for pattern validation and reordering
            const namedArgMap = decl.type ? extractNamedArgMap(decl.type) : undefined;
            const totalArity = decl.type ? countParameters(decl.type) : undefined;
            // For with-auxiliary functions and functions that call them, defer elaboration to type-checking
            // phase when we have definitions. This allows the elaborator to look up namedArgMaps.
            // With-auxiliaries are marked with withScrutineeCount, and functions calling with-auxiliaries
            // have names ending with the original function's name (main function references auxiliary).
            const isWithRelated = decl.withScrutineeCount !== undefined ||
                                  (decl.name && decl.name.includes('-with-'));
            if (isWithRelated) {
              kernelValue = undefined;
            } else {
              kernelValue = elabToKernelWithMap(decl.value, elabMap, valuePath, valuePath, namedArgMap, undefined, totalArity);
            }
          }
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
// Compile Options
// ============================================================================

export interface CompileOptions {
  /** After zonking, re-check zonked terms in a fresh TCEnv with no metas. */
  recheckZonkedTerms?: boolean;

  /**
   * Assume axiom K (Uniqueness of Identity Proofs).
   *
   * When true, pattern matching on indexed families (like Equal) is unrestricted.
   * When false (default), the deletion rule is enforced: indices must be definitionally equal.
   *
   * Without K, proofs like UIP become unprovable, making the system compatible with
   * HoTT and Cubical Type Theory.
   *
   * Can be overridden per-file with @assumeK directive.
   *
   * Default: false (no K axiom)
   */
  assumeK?: boolean;
}

/**
 * Parse @assumeK directive from source code.
 *
 * Recognizes (with or without -- prefix):
 *   @assumeK         (equivalent to @assumeK=true)
 *   @assumeK=true
 *   @assumeK=false
 *
 * @returns true if @assumeK or @assumeK=true, false if @assumeK=false, undefined if not present
 */
function parseAssumeKDirective(source: string): boolean | undefined {
  const lines = source.split('\n');
  for (const line of lines) {
    const trimmed = line.trim();
    // Match @assumeK directive (with optional -- comment prefix)
    const match = trimmed.match(/^(?:--\s*)?@assumeK(?:=(\w+))?/);
    if (match) {
      const value = match[1];
      if (!value || value === 'true') return true;
      if (value === 'false') return false;
      // Warning instead of throw for incomplete/invalid directive
      console.warn(`Warning: Invalid @assumeK directive value '${value}'. Expected 'true' or 'false'. Treating as 'false'.`);
      return false;
    }
  }
  return undefined;
}

// ============================================================================
// Zonked Term Rechecking
// ============================================================================

/**
 * Check that a zonked term contains no leftover Meta or Hole nodes.
 * This validates that zonking was complete — all metas were solved and substituted.
 *
 * Skips Match nodes (pattern-match compilation output) since Match nodes
 * are trusted compilation output that may contain internal metas.
 */

/**
 * Check if a term contains a reference to the given name (Const node).
 * Used to detect self-references in simple (non-pattern-matching) definitions.
 */
function containsSelfReference(term: TTKTerm, name: string): boolean {
  switch (term.tag) {
    case 'Const': return term.name === name;
    case 'App': return containsSelfReference(term.fn, name) || containsSelfReference(term.arg, name);
    case 'Binder': return containsSelfReference(term.domain, name) || containsSelfReference(term.body, name);
    case 'Sort': return containsSelfReference(term.level, name);
    case 'Annot': return containsSelfReference(term.term, name) || containsSelfReference(term.type, name);
    case 'Match': return term.clauses.some(c => containsSelfReference(c.rhs, name));
    default: return false;
  }
}

function recheckZonkedTerm(
  term: TTKTerm,
  definitions: DefinitionsMap,
  label: string,
): string | undefined {
  // Skip Match values — trusted compilation output
  if (term.tag === 'Match') return undefined;

  // Phase 1: AST walk for leftover metas/holes
  const leftoverMetas: string[] = [];
  const leftoverHoles: string[] = [];

  function walk(t: TTKTerm): void {
    switch (t.tag) {
      case 'Meta':
        leftoverMetas.push(t.id);
        break;
      case 'Hole':
        // Holes that start with ? are user-written holes (?todo etc) — those are fine
        if (!t.id.startsWith('?')) {
          leftoverHoles.push(t.id);
        }
        break;
      case 'App':
        walk(t.fn);
        walk(t.arg);
        break;
      case 'Binder':
        walk(t.domain);
        walk(t.body);
        break;
      case 'Sort':
        walk(t.level);
        break;
      case 'Annot':
        walk(t.term);
        walk(t.type);
        break;
      case 'Match':
        // Skip Match internals — trusted compilation output
        break;
      // Var, Const, ULevel, ULit, UOmega — leaf nodes, nothing to check
    }
  }

  walk(term);

  if (leftoverMetas.length > 0) {
    return `Zonk recheck failed for ${label}: ${leftoverMetas.length} unsolved meta(s) remaining: ${leftoverMetas.join(', ')}`;
  }
  if (leftoverHoles.length > 0) {
    return `Zonk recheck failed for ${label}: ${leftoverHoles.length} unresolved hole(s) remaining: ${leftoverHoles.join(', ')}`;
  }

  // Phase 2: Re-type-check in a fresh environment.
  // This catches type mismatches, wrong de Bruijn indices, and incorrect
  // universe levels that the AST walk cannot detect.
  try {
    const freshEnv = createTCEnv({ definitions, options: { mode: 'check' } });
    const resultEnv = inferType(freshEnv.withValue(term));

    // Solve any constraints generated during inference
    const solvedEnv = resultEnv.solveMetasAndConstraints({ liftMetasToFullContext: false });

    // Check that no unsolved metas were generated (zonked terms should be fully explicit)
    const unsolvedIds: string[] = [];
    for (const [id, m] of solvedEnv.metaVars) {
      if (!m.solution && !m.isHole) unsolvedIds.push(id);
    }
    if (unsolvedIds.length > 0) {
      return `Zonk recheck failed for ${label}: re-type-check generated ${unsolvedIds.length} unsolved meta(s): ${unsolvedIds.join(', ')}`;
    }
  } catch (e) {
    const msg = e instanceof TCEnvError ? e.fullMessage
      : e instanceof Error ? e.message
        : String(e);
    return `Zonk recheck (re-type-check) failed for ${label}: ${msg}`;
  }
  return undefined;
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
  assumeK?: boolean,
): CheckDeclarationResult {
  let checkSuccess = true;
  const checkErrors: TCEnvError[] = [];
  let newDefinitions = definitions;
  let errorCount = 0;
  let indexPositions: number[] | undefined;
  let totalityResult: TotalityResult | undefined;
  let checkedValue: TTKTerm | undefined;
  let zonkedConstructors: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }> | undefined;
  const typeInfoMap: TypeInfoMap = new Map();

  // Check for elaboration errors first (e.g., named argument errors)
  if (decl.elabError) {
    checkSuccess = false;
    // Create TCEnv with the error path so the error points to the correct source location
    const errorPath = decl.elabErrorPath ? deserializeIndexPath(decl.elabErrorPath) : [];
    const env = createTCEnv({ definitions, indexPath: errorPath, options: { mode: 'check', assumeK } });
    const error = TCEnvError.create(decl.elabError, env);
    checkErrors.push(error);
    errorCount = 1;
  } else if (decl.kind === 'inductive') {
    const result = checkInductiveTypeDeclaration(decl, definitions, typeInfoMap);
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
    const result = checkTermDeclaration(decl, definitions, { typeInfoCollector: typeInfoMap, assumeK });
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
    const error = TCEnvError.create('Declaration is not an inductive or term', createTCEnv({ definitions, options: { mode: 'check', assumeK } }));
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
    // Pass namedArgLookup to show implicit args with their labels
    prettyValue: (checkedValue ?? decl.kernelValue) ? prettyPrintFormatted(
      checkedValue ?? decl.kernelValue!,
      [],
      undefined,
      { namedArgLookup: createNamedArgLookup(newDefinitions) }
    ) : undefined,
    prettyConstructors: effectiveConstructors?.map(c => ({
      name: c.name,
      prettyType: prettyPrintTTK(c.type)
    })),
    checkSuccess,
    checkErrors,
    totalityResult,
    elabMap: decl.elabMap,
    sourceMap: decl.sourceMap,
    elabErrorPath: decl.elabErrorPath,
    withScrutineeCount: decl.withScrutineeCount,
    withScrutineeExprs: decl.withScrutineeExprs,
    typeInfoMap: typeInfoMap.size > 0 ? typeInfoMap : undefined,
  };

  return { compiled, newDefinitions, errorCount };
}

function checkInductiveTypeDeclaration(
  decl: ElabDeclaration,
  definitions: DefinitionsMap,
  typeInfoCollector?: TypeInfoMap,
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
    inductiveNamedArgMap && inductiveNamedArgMap.size > 0 ? inductiveNamedArgMap : undefined,
    undefined,  // recordInfo
    typeInfoCollector,
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

/**
 * Remap an auxiliary with-function's elabMap to map its kernel clause paths
 * to the original with-clause surface paths in the block sourceMap.
 *
 * The auxiliary has clauses[0..N] which correspond to withClauses[0..N]
 * in some main clause. The sourceMap records paths like:
 *   value.clauses[mainIdx].withClauses[i].patterns[j]
 *   value.clauses[mainIdx].withClauses[i].rhs
 *
 * We need elabMap entries so the reverse lookup (surface→kernel) works:
 *   kernel: value.clauses[i].rhs  →  surface: value.clauses[mainIdx].withClauses[i].rhs
 */
function remapWithClauseElabMap(
  compiled: CompiledDeclaration,
  sourceMap: SourceMap,
  withScrutineeCount: number,
): void {
  if (!compiled.elabMap) return;

  // Determine the number of function patterns (before with-patterns) in each aux clause.
  // The kernel clauses have: [funcPat0, funcPat1, ..., withPat0, withPat1, ...]
  // withScrutineeCount tells us how many with-patterns there are at the end.
  let numFunctionPatterns = 0;
  if (compiled.kernelValue?.tag === 'Match' && compiled.kernelValue.clauses.length > 0) {
    const totalPatterns = compiled.kernelValue.clauses[0].patterns.length;
    numFunctionPatterns = totalPatterns - withScrutineeCount;
  } else if (compiled.surfaceValue?.tag === 'Match' && compiled.surfaceValue.clauses.length > 0) {
    // Fallback to surface value when kernel value is unavailable (e.g., elaboration failed)
    const totalPatterns = compiled.surfaceValue.clauses[0].patterns.length;
    numFunctionPatterns = totalPatterns - withScrutineeCount;
  }

  // Detect nested Match structure: when the auxiliary has a single clause whose
  // RHS is itself a Match, the with-branches are inside that nested Match
  // (e.g., value.clauses[0].rhs is a Match with sub-clauses for each with-branch).
  let hasNestedMatch = false;
  const surfaceMatch = compiled.surfaceValue?.tag === 'Match' ? compiled.surfaceValue : null;
  if (surfaceMatch && surfaceMatch.clauses.length === 1) {
    const rhs = surfaceMatch.clauses[0].rhs;
    if (rhs.tag === 'Match') {
      hasNestedMatch = true;
    }
  }

  // Find with-clause entries in the sourceMap for this auxiliary
  // Pattern: value.clauses[N].withClauses[M].*
  const withClausePattern = /^value\.clauses\[(\d+)\]\.withClauses\[(\d+)\](.*)/;

  for (const [path] of sourceMap) {
    const match = path.match(withClausePattern);
    if (!match) continue;

    const withIdx = parseInt(match[2]);
    const rawSuffix = match[3]; // e.g., '.patterns[0]', '.rhs', '.rhs.fn'

    // Offset pattern indices: with-pattern j → kernel pattern (numFunctionPatterns + j)
    let suffix = rawSuffix;
    const patternMatch = suffix.match(/^\.patterns\[(\d+)\](.*)/);
    if (patternMatch) {
      const withPatIdx = parseInt(patternMatch[1]);
      const patSuffix = patternMatch[2];
      suffix = `.patterns[${numFunctionPatterns + withPatIdx}]${patSuffix}`;
    }

    const kernelPath = `value.clauses[${withIdx}]${suffix}`;
    compiled.elabMap.set(kernelPath, path);

    // Also map for nested Match structure: with-branches are sub-clauses
    // inside value.clauses[0].rhs (a Match term). No pattern offset needed
    // since the nested Match has its own independent pattern indices.
    if (hasNestedMatch) {
      const nestedPath = `value.clauses[0].rhs.clauses[${withIdx}]${rawSuffix}`;
      compiled.elabMap.set(nestedPath, path);
    }
  }

  // For nested Match: map value.clauses[0].rhs (the whole nested Match)
  // to the parent with-clause entry rather than a specific branch.
  // This ensures errors about the entire Match point to the with-clause line,
  // not to one arbitrary branch.
  if (hasNestedMatch) {
    const parentWithPattern = /^value\.clauses\[(\d+)\]\.withClauses\[0\]/;
    for (const [path] of sourceMap) {
      const m = path.match(parentWithPattern);
      if (m) {
        const clauseIdx = m[1];
        const parentEntry = `value.clauses[${clauseIdx}]`;
        if (sourceMap.has(parentEntry)) {
          compiled.elabMap.set('value.clauses[0].rhs', parentEntry);
          break;
        }
      }
    }
  }
}

/**
 * Remap scrutinee paths from the main declaration's elabMap so type info
 * is accessible for the scrutinee expression in a with-clause.
 *
 * The sourceMap has: value.clauses[N].scrutinee, value.clauses[N].scrutinee.fn, etc.
 * These need to map into the main declaration's kernel paths.
 */
function remapWithScrutineeInMainElabMap(
  compiled: CompiledDeclaration,
  sourceMap: SourceMap,
): void {
  if (!compiled.elabMap) return;

  // Find scrutinee entries in the sourceMap
  // Pattern: value.clauses[N].scrutinee*
  const scrutineePattern = /^value\.clauses\[(\d+)\]\.scrutinee/;

  for (const [path] of sourceMap) {
    const match = path.match(scrutineePattern);
    if (match) {
      // The scrutinee in the main function is desugared into the RHS
      // (a call to the auxiliary). Map scrutinee paths to the RHS path
      // so type info can be found.
      const clauseIdx = parseInt(match[1]);
      const suffix = path.substring(`value.clauses[${clauseIdx}].scrutinee`.length);
      // The scrutinee expression appears in the RHS of the main clause
      // as arguments to the auxiliary function call.
      // Map it to the corresponding RHS sub-path.
      const kernelRhsBase = `value.clauses[${clauseIdx}].rhs`;
      // For the full scrutinee, map to RHS.arg (last argument to aux call)
      // For scrutinee.fn, map to RHS.arg.fn, etc.
      if (suffix === '' || suffix === '.fn' || suffix === '.arg') {
        const kernelPath = suffix === '' ? `${kernelRhsBase}.arg` : `${kernelRhsBase}.arg${suffix}`;
        compiled.elabMap.set(kernelPath, path);
      }
    }
  }
}

/**
 * Merge an auxiliary with-clause declaration's typeInfoMap and elabMap into the
 * main declaration so that type-at-cursor works for with-clause patterns and RHS.
 *
 * The auxiliary's elabMap (after remapWithClauseElabMap) maps auxiliary kernel paths
 * to the main declaration's surface paths (e.g., value.clauses[1].withClauses[0].rhs.fn).
 * We store each auxiliary typeInfoMap entry under its surface path so that
 * resolveTypeInfo's direct surface-path lookup finds them.
 */
function mergeAuxTypeInfoIntoMain(
  mainCompiled: CompiledDeclaration,
  auxCompiled: CompiledDeclaration,
): void {
  if (!auxCompiled.typeInfoMap || !auxCompiled.elabMap) return;
  if (!mainCompiled.typeInfoMap) {
    mainCompiled.typeInfoMap = new Map();
  }
  if (!mainCompiled.elabMap) {
    mainCompiled.elabMap = new Map();
  }

  // Build reverse map: kernel path → surface path (from aux elabMap)
  const auxReverse = new Map<string, string>();
  for (const [kernelPath, surfacePath] of auxCompiled.elabMap) {
    auxReverse.set(kernelPath, surfacePath);
  }

  // Merge typeInfoMap entries: store under surface path for direct lookup
  for (const [kernelPath, entry] of auxCompiled.typeInfoMap) {
    const surfacePath = auxReverse.get(kernelPath);
    if (surfacePath) {
      // Store under the surface path so resolveTypeInfo finds it directly
      mainCompiled.typeInfoMap.set(surfacePath, {
        ...entry,
        kernelPath: surfacePath,
      });
    } else {
      // Walk up kernel path to find a mapped ancestor, append suffix
      let path = kernelPath;
      while (path !== '') {
        const mapped = auxReverse.get(path);
        if (mapped) {
          const suffix = kernelPath.substring(path.length);
          const surfaceKey = mapped + suffix;
          mainCompiled.typeInfoMap.set(surfaceKey, {
            ...entry,
            kernelPath: surfaceKey,
          });
          break;
        }
        const lastDot = path.lastIndexOf('.');
        const lastBracket = path.lastIndexOf('[');
        const cutPoint = Math.max(lastDot, lastBracket);
        if (cutPoint <= 0) break;
        path = path.substring(0, cutPoint);
      }
    }
  }

  // Note: we intentionally do NOT merge the auxiliary's elabMap entries into the
  // main's elabMap. The auxiliary's kernel paths (e.g., value.clauses[1].rhs.fn)
  // conflict with the main's own entries at the same paths. Instead, the typeInfoMap
  // entries stored under surface paths are found via direct surface-path lookup.
}

function failCheck(message: string, env: TCEnv<unknown>): { success: false, errors: TCEnvError[] } {
  return {
    success: false,
    errors: [TCEnvError.create(message, env)],
  }
}

/**
 * Convert any remaining unsolved Meta nodes in a term to Hole nodes.
 * Used after zonking the elaborated type from signature checking: the elaborated type
 * includes implicit argument insertions (Metas from the type checker), and after zonking,
 * solved Metas are replaced with their solutions. Any remaining Metas are unsolved —
 * converting them to Holes allows the pattern matcher's hole-filling code to handle them
 * (e.g., with-clause placeholder Holes like `_scrut0_type` that were converted to Metas
 * during type checking).
 */
function unsolvedMetasToHoles(term: TTKTerm): TTKTerm {
  switch (term.tag) {
    case 'Meta':
      return { tag: 'Hole', id: term.id };
    case 'App':
      return { tag: 'App', fn: unsolvedMetasToHoles(term.fn), arg: unsolvedMetasToHoles(term.arg) };
    case 'Binder': {
      const bk = term.binderKind.tag === 'BLet'
        ? { tag: 'BLet' as const, defVal: unsolvedMetasToHoles(term.binderKind.defVal) }
        : term.binderKind;
      return { tag: 'Binder', name: term.name, binderKind: bk, domain: unsolvedMetasToHoles(term.domain), body: unsolvedMetasToHoles(term.body) };
    }
    case 'Sort': {
      const level = unsolvedMetasToHoles(term.level);
      return level === term.level ? term : { tag: 'Sort', level };
    }
    case 'Annot':
      return { tag: 'Annot', term: unsolvedMetasToHoles(term.term), type: unsolvedMetasToHoles(term.type) };
    case 'Match':
      return { tag: 'Match', scrutinee: unsolvedMetasToHoles(term.scrutinee), clauses: term.clauses.map(c => ({ ...c, rhs: unsolvedMetasToHoles(c.rhs) })) };
    default:
      // Var, Const, Hole, ULevel, ULit, UOmega — no Metas inside
      return term;
  }
}

function checkTermDeclaration(
  decl: ElabDeclaration,
  definitions: DefinitionsMap,
  options?: { allowUnsolvedSigMetas?: boolean; skipTotality?: boolean; withScrutineeCount?: number; typeInfoCollector?: TypeInfoMap; assumeK?: boolean },
): { success: false, errors: TCEnvError[], totalityResult?: TotalityResult } | { success: true, definitions: DefinitionsMap, checkedValue: TTKTerm, zonkedType: TTKTerm, totalityResult?: TotalityResult } {

  if (!decl.name) {
    return failCheck('Term declaration is ill-formed (no name)', createTCEnv({ definitions, options: { mode: 'check', assumeK: options?.assumeK } }))
  }

  let env = createTCEnv({ definitions, options: { mode: 'check', allowDuplicatePiNames: options?.allowUnsolvedSigMetas, assumeK: options?.assumeK }, typeInfoCollector: options?.typeInfoCollector })

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
    const unsolvedSigMetas = Array.from(solvedSigResult.metaVars.values()).filter(m => !m.solution && !m.isHole);
    if (unsolvedSigMetas.length > 0 && !options?.allowUnsolvedSigMetas) {
      return {
        success: false, errors: [
          TCEnvError.create('Checking the signature produced unsolved metas.', env)
        ]
      }
    }

    // Extract named arg info from type for use in definition and pattern elaboration
    const namedArgMap = decl.surfaceType ? extractNamedArgMap(decl.surfaceType) : undefined;
    const totalArity = decl.surfaceType ? countParameters(decl.surfaceType) : undefined;

    // Zonk the kernel type to substitute any solved metas (e.g., implicit params inferred from arguments).
    // Use the elaborated term from signature checking if available, because it includes implicit argument
    // insertions for constructors used as arguments in the type (e.g., bare `refl` in `Equal p refl`
    // becomes `refl A x` with its implicit args filled). The raw kernelType retains bare Const nodes
    // that the type checker later wraps with implicit applications — but those wrappings aren't
    // reflected back into the kernel type. After zonking, any remaining unsolved Metas (e.g., with-clause
    // placeholder Holes like `_scrut0_type` that became Metas during checking) are converted back to
    // Holes so the pattern matcher's hole-filling code can handle them.
    const sigElaboratedType = sigResult.elaboratedTerm ?? decl.kernelType;
    const zonkedKernelType = unsolvedMetasToHoles(solvedSigResult.zonkTerm(sigElaboratedType));

    // Add to context for subsequent declarations, including namedArgMap for lookup
    if (decl.name) {
      termEnv = addDefinitionInTCEnv(termEnv, decl.name, zonkedKernelType, namedArgMap);
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
          let isAbsurd = arePatternsAbsurd(decl.name, patternsEnv, zonkedKernelType);

          // If basic check passes (not absurd), try Agda-style recursive splitting
          // This handles cases like Fin Zero where the type is uninhabited
          if (!isAbsurd) {
            isAbsurd = tryCaseSplitsInSearchOfAbsurdity(
              decl.name,
              kernelPatterns,
              zonkedKernelType,
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

      // Special handling for TacticBlock - elaborate by executing tactics
      let kernelValue: TTKTerm;
      if (decl.surfaceValue.tag === 'TacticBlock') {
        try {
          kernelValue = elaborateTacticBlock(
            decl.surfaceValue,
            zonkedKernelType,
            termEnv.definitions,
            decl.elabMap ?? new Map(),
            [] // Empty context for top-level definitions
          );
        } catch (e) {
          // Convert tactic errors to TCEnvErrors with proper location
          const errorMsg = e instanceof Error ? e.message : String(e);
          throw TCEnvError.create(errorMsg, termEnv);
        }
      } else {
        kernelValue = elabToKernelWithMap(
          decl.surfaceValue,
          decl.elabMap ?? new Map(),
          valuePath,
          valuePath,
          namedArgMap,
          appNamedArgLookup
        );
      }

      // Tactic-produced terms are already validated step-by-step by the tactic engine
      // (ExactTactic uses checkType, ApplyTactic uses inferType+unify, etc.).
      // The outer checkType is redundant and fails for Match terms produced by
      // cases/induction tactics, since the type checker doesn't handle Match inference.
      // Skip re-checking and trust the tactic engine's validation.
      if (decl.surfaceValue.tag === 'TacticBlock') {
        const resultEnv = setDefinitionValueInTCEnv(termEnv, decl.name, kernelValue);
        return { success: true, definitions: resultEnv.definitions, checkedValue: kernelValue, zonkedType: zonkedKernelType };
      }

      try {
        const valueEnv = termEnv.withValue(kernelValue);
        const result = checkType(valueEnv, zonkedKernelType);

        // Solve meta constraints before checking for unsolved metas
        let solvedResult: typeof result;
        try {
          solvedResult = result.solveMetasAndConstraints({ liftMetasToFullContext: false });
        } catch (e) {
          // Convert plain Errors (e.g. from meta constraint solving) to TCEnvErrors
          // so they carry the value-level indexPath for accurate error location.
          if (e instanceof Error && !(e instanceof TCEnvError)) {
            throw TCEnvError.create(e.message, result);
          }
          throw e;
        }
        // Check for UNSOLVED metas in the value (solved metas have a 'solution' property)
        // Exclude hole metas — those are intentionally unsolved (user wrote ?name)
        const unsolvedMetas = Array.from(solvedResult.metaVars.values()).filter(m => !m.solution && !m.isHole);
        if (unsolvedMetas.length > 0) {
          return {
            success: false, errors: [
              TCEnvError.create('Checking the value produced unsolved metas.', termEnv)
            ]
          };
        }
        // Zonk the value to substitute solved metas with their solutions
        const zonkedValue = solvedResult.zonkTerm(solvedResult.value);

        // Check for self-reference in non-pattern-matching definitions.
        // A simple definition `f = expr` with `f` appearing in `expr` is always
        // non-terminating since there's no structural decrease without pattern matching.
        if (decl.name && containsSelfReference(zonkedValue, decl.name)) {
          return {
            success: false, errors: [
              TCEnvError.create(
                `Definition '${decl.name}' is non-terminating: simple definitions cannot be recursive. Use pattern matching for recursive definitions.`,
                termEnv
              )
            ]
          };
        }

        const resultEnv = setDefinitionValueInTCEnv(termEnv, decl.name, zonkedValue);
        return { success: true, definitions: resultEnv.definitions, checkedValue: zonkedValue, zonkedType: zonkedKernelType };
      } catch (e) {
        if (e instanceof TCEnvError) {
          return { success: false, errors: [e] };
        }
        return { success: false, errors: [TCEnvError.create(String(e), termEnv)] };
      }
    }

    // Get surface clauses for incremental elaboration (pattern matching case)
    // IMPORTANT: Preserve original surface indices when filtering absurd clauses
    // This ensures the ElabMap correctly maps kernel clause indices to surface clause indices
    const surfaceClausesWithIndices: Array<{ clause: TClause; originalIndex: number }> =
      decl.surfaceValue?.tag === 'Match'
        ? decl.surfaceValue.clauses
            .map((clause, index) => ({ clause, originalIndex: index }))
            .filter(({ clause }) => clause.rhs.tag !== 'AbsurdMarker')
        : [];
    const surfaceClauses = surfaceClausesWithIndices.map(({ clause }) => clause);
    const surfaceClauseIndices = surfaceClausesWithIndices.map(({ originalIndex }) => originalIndex);

    const result = checkTermValue(
      decl.name,
      termEnv,
      zonkedKernelType,  // Use zonked type - Holes from signature elaboration are resolved
      surfaceClauses,
      surfaceClauseIndices,
      decl.elabMap ?? new Map(),
      namedArgMap,
      totalArity,
      annotatedAbsurdClauses,
      { skipTotality: options?.skipTotality, withScrutineeCount: options?.withScrutineeCount }
    );
    if (!result.success) {
      return { success: false, errors: result.errors, totalityResult: result.totalityResult }
    }

    const resultEnv = setDefinitionValueInTCEnv(termEnv, decl.name, result.checkedValue);
    return { success: true, definitions: resultEnv.definitions, checkedValue: result.checkedValue, zonkedType: zonkedKernelType, totalityResult: result.totalityResult }
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
  assumeK?: boolean,
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
    const result = checkDeclaration(decl, currentDefinitions, assumeK);
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
  assumeK?: boolean,
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

      const result = checkBlock(filteredBlock, blockIndex, currentDefinitions, assumeK);

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
      const result = checkBlock(block, blockIndex, currentDefinitions, assumeK);
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
  definitions?: DefinitionsMap,
  totalityResult?: TotalityResult,
  indexPositions?: number[],
  elabErrorPath?: string,
  isRecord?: boolean,
  surfaceParams?: Array<{ name: string; type: TTerm }>,
  surfaceFields?: Array<{ name: string; type: TTerm }>,
  surfaceExtendsExprs?: TTerm[],
  prettyProjections?: Array<{ name: string; prettyType: string }>,
  typeInfoMap?: TypeInfoMap,
): CompiledDeclaration {
  // Create namedArgLookup for pretty printing implicit args with labels
  const namedArgLookup = definitions ? createNamedArgLookup(definitions) : undefined;
  const prettyPrintOptions = namedArgLookup ? { namedArgLookup } : {};

  // Extract namedArgMap from surfaceType for term declarations
  const namedArgMap = decl.type ? extractNamedArgMap(decl.type) : undefined;

  return {
    name: decl.name,
    kind: decl.kind === 'inductive' ? 'inductive' : 'term',
    surfaceType: decl.type,
    surfaceValue: decl.originalSurfaceValue ?? decl.value,
    surfaceConstructors: decl.constructors,
    isRecord,
    surfaceParams,
    surfaceFields,
    surfaceExtendsExprs,
    kernelType,
    kernelValue,
    kernelConstructors,
    namedArgMap: namedArgMap && namedArgMap.size > 0 ? namedArgMap : undefined,
    indexPositions,
    prettyType: kernelType ? prettyPrintFormatted(kernelType, [], undefined, prettyPrintOptions) : undefined,
    prettyValue: kernelValue ? prettyPrintFormatted(kernelValue, [], undefined, prettyPrintOptions) : undefined,
    prettyConstructors: kernelConstructors?.map(c => ({
      name: c.name,
      prettyType: prettyPrintTTK(c.type)
    })),
    prettyProjections,
    checkSuccess,
    checkErrors,
    totalityResult,
    elabMap,
    sourceMap,
    elabErrorPath,
    withScrutineeCount: decl.withScrutineeCount,
    withScrutineeExprs: decl.withScrutineeExprs,
    typeInfoMap,
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
      false, [error], definitions, undefined, undefined, elabErrorPath
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
  const typeInfoMap: TypeInfoMap = new Map();

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

  // Create a combined lookup that checks both:
  // 1. The current inductive type being defined (not yet in definitions)
  // 2. Other types already in definitions (e.g., Equal from a previous declaration)
  const baseAppLookup = createNamedArgInfoLookup(definitions);
  const ctorAppLookup = (name: string) => {
    // First check if it's the current inductive type
    if (decl.name && name === decl.name && inductiveNamedArgMap && inductiveNamedArgMap.size > 0) {
      return { namedArgMap: inductiveNamedArgMap, totalArity: inductiveTotalArity };
    }
    // Otherwise check existing definitions
    return baseAppLookup(name);
  };

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
    inductiveNamedArgMap,
    undefined,  // recordInfo
    typeInfoMap,
  );
  const finalTypeInfoMap = typeInfoMap.size > 0 ? typeInfoMap : undefined;

  if (!result.success) {
    // Return original context on failure
    return {
      success: false,
      compiled: createCompiledDeclaration(
        decl, kernelType, undefined, kernelConstructors, elabMap, sourceMap,
        false, result.errors, undefined, undefined, undefined, undefined, undefined, undefined, undefined, undefined, undefined, finalTypeInfoMap
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
      true, [], result.newDefinitions, undefined, result.indexPositions,
      undefined, undefined, undefined, undefined, undefined, undefined, finalTypeInfoMap
    ),
    newDefinitions: result.newDefinitions,
    errorCount: 0
  };
}

/**
 * Extract fields from a parent record's compiled form.
 *
 * The parent record is stored as an inductive with a single constructor.
 * Constructor type is: (P1 : T1) → ... → (F1 : FT1) → ... → RecName P1...
 *
 * We need to extract the field binders from the constructor type, skipping params.
 */
function extractParentRecordFields(
  parentName: string,
  definitions: DefinitionsMap
): TTKRecordField[] | { error: string } {
  const parentInductive = definitions.inductiveTypes.get(parentName);
  if (!parentInductive) {
    return { error: `Parent record "${parentName}" not found` };
  }

  const recordInfo = parentInductive.recordInfo;
  if (!recordInfo) {
    return { error: `"${parentName}" is not a record (no recordInfo)` };
  }

  // Get the constructor type (records have exactly one constructor)
  if (parentInductive.constructors.length !== 1) {
    return { error: `"${parentName}" has ${parentInductive.constructors.length} constructors, expected 1` };
  }
  const ctorType = parentInductive.constructors[0].type;

  // Count total Pi binders in constructor type
  // Constructor type: (P1 : T1) → ... → (Pn : Tn) → (F1 : FT1) → ... → (Fm : FTm) → RecName P1 ... Pn
  // countPiBinders counts all Pi binders (params + fields)
  const totalBinders = countPiBinders(ctorType);
  const fieldCount = recordInfo.fieldNames.length;
  const paramCount = totalBinders - fieldCount;

  // Traverse the constructor type, skipping params, collecting fields
  const fields: TTKRecordField[] = [];
  let current: TTKTerm = ctorType;
  let binderIndex = 0;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    if (binderIndex >= paramCount) {
      // This is a field binder
      const fieldIdx = binderIndex - paramCount;
      const isImplicit = recordInfo.implicitFields.includes(fieldIdx);
      fields.push({
        name: current.name,
        type: current.domain,
        implicit: isImplicit
      });
    }
    current = current.body;
    binderIndex++;
  }

  return fields;
}

/**
 * Substitute inherited field references in a surface term and shift param refs.
 *
 * When a child record extends a parent, local field types may reference
 * inherited fields by name. The parser doesn't know about inherited fields,
 * so these references are parsed as Const. This function:
 * 1. Shifts param refs (Var indices >= localFieldIndex) by numInherited
 * 2. Substitutes inherited field Const → Var at the correct indices
 *
 * Example for Monoid extending Semigroup:
 * - Semigroup has fields [op, assoc]
 * - Monoid has local fields [e, identLeft, identRight]
 * - For identLeft (localFieldIndex=1), the original context was [e, A]
 * - After transformation, context is [e, assoc, op, A]
 *   - e stays at index 0
 *   - A shifts from index 1 to index 3
 *   - op is substituted to index 2
 *   - assoc is substituted to index 1
 *
 * @param term - The surface term to transform
 * @param inheritedFieldNames - Names of inherited fields, in order
 * @param localFieldIndex - Index of the current local field (0-based)
 * @returns The transformed term
 */
function substituteInheritedFieldRefs(
  term: TTerm,
  inheritedFieldNames: string[],
  localFieldIndex: number
): TTerm {
  if (inheritedFieldNames.length === 0) {
    return term; // No inherited fields, nothing to transform
  }

  const numInherited = inheritedFieldNames.length;

  function transform(t: TTerm, depth: number): TTerm {
    switch (t.tag) {
      case 'Const': {
        // Check if this Const refers to an inherited field
        const inheritedIdx = inheritedFieldNames.indexOf(t.name);
        if (inheritedIdx >= 0) {
          // Convert to Var with correct de Bruijn index
          // In the combined context, inherited fields are at indices:
          //   [localFieldIndex, localFieldIndex + numInherited)
          // First inherited field (idx 0) is FURTHEST, so has highest index
          // Last inherited field is closest, so has lowest index
          // Formula: localFieldIndex + (numInherited - 1 - inheritedIdx) + depth
          const varIndex = localFieldIndex + (numInherited - 1 - inheritedIdx) + depth;
          return { tag: 'Var', index: varIndex };
        }
        return t;
      }
      case 'Var': {
        // Shift param refs: indices >= localFieldIndex + depth need to shift by numInherited
        // (depth accounts for local binders in the term itself)
        const adjustedCutoff = localFieldIndex + depth;
        if (t.index >= adjustedCutoff) {
          return { tag: 'Var', index: t.index + numInherited };
        }
        return t;
      }
      case 'Sort':
        return { tag: 'Sort', level: transform(t.level, depth) };
      case 'ULevel':
      case 'ULit':
      case 'UOmega':
      case 'Hole':
      case 'AbsurdMarker':
        return t;
      case 'App': {
        const newFn = transform(t.fn, depth);
        const newArg = transform(t.arg, depth);
        if (newFn === t.fn && newArg === t.arg) return t;
        return { tag: 'App', fn: newFn, arg: newArg, argName: t.argName };
      }
      case 'Binder': {
        const newDomain = t.domain ? transform(t.domain, depth) : undefined;
        const newBody = transform(t.body, depth + 1);
        if (newDomain === t.domain && newBody === t.body) return t;
        return { ...t, domain: newDomain, body: newBody };
      }
      case 'MultiBinder': {
        const newDomain = transform(t.domain, depth);
        const numNames = t.names.length;
        const newBody = transform(t.body, depth + numNames);
        if (newDomain === t.domain && newBody === t.body) return t;
        return { ...t, domain: newDomain, body: newBody };
      }
      case 'Match': {
        const newScrutinee = transform(t.scrutinee, depth);
        const newClauses = t.clauses.map(c => ({
          ...c,
          rhs: transform(c.rhs, depth + countPatternBinders(c.patterns))
        }));
        return { tag: 'Match', scrutinee: newScrutinee, clauses: newClauses };
      }
      case 'Annot':
        return { tag: 'Annot', term: transform(t.term, depth), type: transform(t.type, depth) };
      case 'WithClause':
        // WithClause is parsed separately, shouldn't appear in field types
        return t;
      case 'TacticBlock':
        // Transform tactic arguments
        return {
          tag: 'TacticBlock',
          tactics: t.tactics.map(cmd => ({
            name: cmd.name,
            args: cmd.args.map(arg => transform(arg, depth))
          }))
        };
      default: {
        const _exhaustive: never = t;
        return _exhaustive;
      }
    }
  }

  return transform(term, 0);
}

/**
 * Count the number of binders introduced by a list of patterns.
 */
function countPatternBinders(patterns: TPattern[]): number {
  let count = 0;
  for (const p of patterns) {
    count += countSinglePatternBinders(p);
  }
  return count;
}

function countSinglePatternBinders(p: TPattern): number {
  switch (p.tag) {
    case 'PVar':
      return 1;
    case 'PWild':
      return 1; // Wildcards also bind
    case 'PCtor':
      return p.args.reduce((acc, arg) => acc + countSinglePatternBinders(arg), 0);
    default: {
      const _exhaustive: never = p;
      return 0;
    }
  }
}

/**
 * Process a record declaration: elaborate, convert to inductive, and check.
 *
 * Records are converted to single-constructor inductives with extra metadata.
 * The flow is:
 * 1. Elaborate record params and fields to kernel terms
 * 2. Build TTKRecordDef
 * 3. Convert to InductiveDefinition via recordToInductiveDefinition
 * 4. Check using the same infrastructure as inductives
 */
function processRecordDeclaration(
  decl: ParsedDeclaration,
  sourceMap: SourceMap,
  definitions: DefinitionsMap,
): ProcessDeclarationResult {
  const elabMap: ElabMap = new Map();

  // Create lookup for named arguments in field/param types (e.g., Equal {A} ...)
  const appNamedArgLookup = createNamedArgInfoLookup(definitions);

  // ============================================================================
  // Step 1: Process extends FIRST to get inherited field names
  // This must happen before elaborating local fields so we can substitute
  // inherited field references from Const to Var.
  // ============================================================================
  const inheritedFields: TTKRecordField[] = [];
  const inheritedFieldNames: string[] = [];
  if (decl.extends && decl.extends.length > 0) {
    for (const parentName of decl.extends) {
      const parentFields = extractParentRecordFields(parentName, definitions);
      if ('error' in parentFields) {
        const env = createTCEnv({ definitions, options: { mode: 'check' } });
        const error = TCEnvError.create(parentFields.error, env);
        return {
          success: false,
          compiled: createCompiledDeclaration(
            decl, mkType(0), undefined, undefined, elabMap, sourceMap,
            false, [error], undefined, undefined, undefined
          ),
          newDefinitions: definitions,
          errorCount: 1
        };
      }
      // Check for field name clashes with already inherited fields
      for (const field of parentFields) {
        const clash = inheritedFields.find(f => f.name === field.name);
        if (clash) {
          const env = createTCEnv({ definitions, options: { mode: 'check' } });
          const error = TCEnvError.create(`Field "${field.name}" is inherited from multiple parent records`, env);
          return {
            success: false,
            compiled: createCompiledDeclaration(
              decl, mkType(0), undefined, undefined, elabMap, sourceMap,
              false, [error], undefined, undefined, undefined
            ),
            newDefinitions: definitions,
            errorCount: 1
          };
        }
        inheritedFields.push(field);
        inheritedFieldNames.push(field.name);
      }
    }
  }

  // ============================================================================
  // Step 2: Elaborate record parameters
  // Track ULevel params to build levelNamesInScope for field type elaboration.
  // ============================================================================
  const kernelParams: TTKRecordParam[] = [];
  const levelNamesInScope: Set<string> = new Set();
  if (decl.params) {
    for (let i = 0; i < decl.params.length; i++) {
      const param = decl.params[i];
      try {
        const paramTypePath: IndexPath = [
          { kind: 'field', name: 'params' },
          { kind: 'array', index: i },
          { kind: 'field', name: 'type' }
        ];
        // Pass current levelNamesInScope (built from earlier params)
        const kernelType = elabToKernelWithMap(param.type, elabMap, paramTypePath, paramTypePath, undefined, appNamedArgLookup, undefined, levelNamesInScope);
        kernelParams.push({ name: param.name, type: kernelType, implicit: param.implicit });
        // If this param is a ULevel, add its name to scope for subsequent params/fields
        if (kernelType.tag === 'ULevel') {
          levelNamesInScope.add(param.name);
        }
      } catch (e) {
        return createElabErrorResult(e, decl, sourceMap, elabMap, definitions);
      }
    }
  }

  // ============================================================================
  // Step 3: Elaborate record fields with inherited field substitution
  // Before elaborating each local field type, substitute Const references to
  // inherited fields with the correct Var indices.
  // ============================================================================
  const kernelFields: TTKRecordField[] = [];
  if (decl.fields) {
    for (let i = 0; i < decl.fields.length; i++) {
      const field = decl.fields[i];
      try {
        const fieldTypePath: IndexPath = [
          { kind: 'field', name: 'fields' },
          { kind: 'array', index: i },
          { kind: 'field', name: 'type' }
        ];
        // Substitute inherited field references (Const → Var) in the surface term
        const substitutedType = substituteInheritedFieldRefs(field.type, inheritedFieldNames, i);
        // Pass levelNamesInScope so ULevel params (like u) are recognized in field types
        const kernelType = elabToKernelWithMap(substitutedType, elabMap, fieldTypePath, fieldTypePath, undefined, appNamedArgLookup, undefined, levelNamesInScope);
        kernelFields.push({
          name: field.name,
          type: kernelType,
          implicit: field.implicit
        });
      } catch (e) {
        return createElabErrorResult(e, decl, sourceMap, elabMap, definitions);
      }
    }
  }

  // ============================================================================
  // Step 4: Check for clashes between local and inherited fields
  // ============================================================================
  for (const localField of kernelFields) {
    const clash = inheritedFields.find(f => f.name === localField.name);
    if (clash) {
      const env = createTCEnv({ definitions, options: { mode: 'check' } });
      const error = TCEnvError.create(`Field "${localField.name}" clashes with inherited field from parent record`, env);
      return {
        success: false,
        compiled: createCompiledDeclaration(
          decl, mkType(0), undefined, undefined, elabMap, sourceMap,
          false, [error], undefined, undefined, undefined
        ),
        newDefinitions: definitions,
        errorCount: 1
      };
    }
  }

  // ============================================================================
  // Step 5: Combine inherited + local fields
  // ============================================================================
  // The substituteInheritedFieldRefs function already handled:
  // 1. Shifting param refs to make room for inherited fields
  // 2. Substituting inherited field Const → Var
  // So we just need to combine the fields here.
  const allFields = [...inheritedFields, ...kernelFields];

  // Elaborate the record result sort (the type annotation after params)
  // If provided (e.g., `: Type` or `: Prop`), use it; otherwise default to Type_0
  let resultSort: TTKTerm;
  if (decl.type) {
    try {
      const typePath: IndexPath = [{ kind: 'field', name: 'type' }];
      resultSort = elabToKernelWithMap(decl.type, elabMap, typePath, typePath);
    } catch (e) {
      return createElabErrorResult(e, decl, sourceMap, elabMap, definitions);
    }
  } else {
    resultSort = mkType(0); // Type = Sort(1)
  }

  // Build the record type: params → resultSort
  const recordType = buildRecordTypeFromParams(kernelParams, resultSort);

  // Build namedArgMap for the record type from implicit params
  // This allows named argument syntax like `DPair {u:=UZero} Nat (\n => Nat)`
  const recordNamedArgMap: NamedArgMap = new Map();
  if (decl.params) {
    for (let i = 0; i < decl.params.length; i++) {
      const param = decl.params[i];
      if (param.implicit) {
        recordNamedArgMap.set(param.name, i);
      }
    }
  }

  // Build TTKRecordDef
  const recordName = decl.name || 'anonymous';
  const constructorName = decl.constructorName ?? defaultRecordConstructorName(recordName);

  const ttkRecord: TTKRecordDef = {
    name: recordName,
    constructorName,
    type: recordType,
    params: kernelParams,
    fields: allFields  // includes inherited + local fields
  };

  // Convert to InductiveDefinition
  const inductiveDef = recordToInductiveDefinition(ttkRecord);

  // Override namedArgMap with the one we built from record params
  if (recordNamedArgMap.size > 0) {
    inductiveDef.namedArgMap = recordNamedArgMap;
  }

  // Add elabMap entries to map constructor type positions back to original field/param positions.
  // The constructor type is: (P1 : T1) → ... → (Pn : Tn) → (F1 : FT1) → ... → (Fm : FTm) → R P1...Pn
  // We need to map paths like "constructors[0].type.body.body.domain" to "fields[0].type"
  addRecordCtorTypeElabMappings(elabMap, kernelParams.length, kernelFields.length);

  // Check using inductive checking infrastructure
  const result = checkInductiveDeclaration(
    inductiveDef.name,
    inductiveDef.type,
    inductiveDef.constructors,
    definitions,
    inductiveDef.namedArgMap,
    inductiveDef.recordInfo  // Pass record info for special handling
  );

  if (!result.success) {
    // Create a synthetic parsed declaration for error reporting
    const syntheticDecl: ParsedDeclaration = {
      kind: 'inductive',
      name: recordName,
      type: decl.params ? buildSurfaceRecordType(decl.params) : undefined,
      constructors: [{
        name: constructorName,
        type: buildSurfaceConstructorType(decl.params || [], decl.fields || [], recordName)
      }]
    };
    return {
      success: false,
      compiled: createCompiledDeclaration(
        syntheticDecl, inductiveDef.type, undefined, inductiveDef.constructors, elabMap, sourceMap,
        false, result.errors, definitions, undefined, undefined, undefined,
        true, decl.fields  // isRecord, surfaceFields
      ),
      newDefinitions: definitions,
      errorCount: result.errors.length
    };
  }

  // Create a synthetic parsed declaration for the compiled output
  const syntheticDecl: ParsedDeclaration = {
    kind: 'inductive',
    name: recordName,
    type: decl.params ? buildSurfaceRecordType(decl.params) : undefined,
    constructors: [{
      name: constructorName,
      type: buildSurfaceConstructorType(decl.params || [], decl.fields || [], recordName)
    }]
  };

  // Generate projections for record fields using ZONKED field types
  // Extract zonked field types from the zonked constructor type to ensure
  // all implicit args (like {A} in Equal {A} ...) are properly resolved.
  const zonkedCtorType = result.zonkedConstructors[0].type;
  const zonkedFields = extractZonkedFieldTypes(zonkedCtorType, kernelParams.length, allFields);
  const zonkedRecord: TTKRecordDef = {
    ...ttkRecord,
    fields: zonkedFields
  };
  const projections = generateProjections(zonkedRecord);

  // Build namedArgMap for projections: all record params are implicit
  // (they're inferred from the record argument)
  const projectionNamedArgMap: NamedArgMap = new Map();
  for (let i = 0; i < ttkRecord.params.length; i++) {
    projectionNamedArgMap.set(ttkRecord.params[i].name, i);
  }

  // Add projections to definitions with namedArgMap
  let finalDefinitions = result.newDefinitions;
  for (const proj of projections) {
    finalDefinitions = addDefinition(finalDefinitions, proj.name, proj.type, proj.value, projectionNamedArgMap);
  }

  // Build pretty-printed projections for display
  const prettyProjections = projections.map(proj => ({
    name: proj.name,
    prettyType: prettyPrintTTK(proj.type)
  }));

  return {
    success: true,
    compiled: createCompiledDeclaration(
      syntheticDecl, inductiveDef.type, undefined, result.zonkedConstructors, elabMap, sourceMap,
      true, [], finalDefinitions, undefined, result.indexPositions, undefined,
      true, decl.params, decl.fields, decl.extendsExprs, prettyProjections  // isRecord, surfaceParams, surfaceFields, surfaceExtendsExprs, prettyProjections
    ),
    newDefinitions: finalDefinitions,
    errorCount: 0
  };
}

/**
 * Extract zonked field types from a zonked constructor type.
 *
 * The constructor type is: (P1 : T1) → ... → (Pn : Tn) → (F1 : FT1) → ... → (Fm : FTm) → R P1...Pn
 * We skip the first numParams binders (params) and extract the next numFields binders (fields).
 *
 * @param ctorType - The zonked constructor type
 * @param numParams - Number of param binders to skip
 * @param origFields - Original field info for names and implicit flags
 * @returns Array of TTKRecordField with zonked types
 */
function extractZonkedFieldTypes(
  ctorType: TTKTerm,
  numParams: number,
  origFields: TTKRecordField[]
): TTKRecordField[] {
  let current = ctorType;

  // Skip param binders
  for (let i = 0; i < numParams; i++) {
    if (current.tag !== 'Binder') {
      // Unexpected structure, return original fields
      return origFields;
    }
    current = current.body;
  }

  // Extract field binders
  const zonkedFields: TTKRecordField[] = [];
  for (let i = 0; i < origFields.length; i++) {
    if (current.tag !== 'Binder') {
      // Unexpected structure, return what we have so far
      break;
    }
    zonkedFields.push({
      name: origFields[i].name,
      type: current.domain,
      implicit: origFields[i].implicit
    });
    current = current.body;
  }

  return zonkedFields.length === origFields.length ? zonkedFields : origFields;
}

/**
 * Build the kernel record type from parameters and result sort.
 * record R (A : Type) (B : Type) : Type has type (A : Type) → (B : Type) → Type
 * record R (A : Type) : Prop has type (A : Type) → Prop
 */
function buildRecordTypeFromParams(params: TTKRecordParam[], resultSort: TTKTerm): TTKTerm {
  // Build from right to left
  let result: TTKTerm = resultSort;
  for (let i = params.length - 1; i >= 0; i--) {
    result = mkPi(params[i].type, result, params[i].name);
  }
  return result;
}

/**
 * Build a surface record type term for display purposes.
 */
function buildSurfaceRecordType(params: Array<{ name: string; type: TTerm }>): TTerm {
  let result: TTerm = mkTypeTT(0);
  for (let i = params.length - 1; i >= 0; i--) {
    result = mkPiTT(params[i].type, result, params[i].name);
  }
  return result;
}

/**
 * Build a surface constructor type term for display purposes.
 */
function buildSurfaceConstructorType(
  params: Array<{ name: string; type: TTerm }>,
  fields: Array<{ name: string; type: TTerm }>,
  recordName: string
): TTerm {
  // Build return type: Record applied to all params
  let returnType: TTerm = mkConstTT(recordName);
  for (let i = 0; i < params.length; i++) {
    // Params are at indices counting from the innermost
    const paramIndex = fields.length + params.length - 1 - i;
    returnType = mkAppTT(returnType, mkVarTT(paramIndex));
  }

  // Add field types
  let result = returnType;
  for (let i = fields.length - 1; i >= 0; i--) {
    result = mkPiTT(fields[i].type, result, fields[i].name);
  }

  // Add param types
  for (let i = params.length - 1; i >= 0; i--) {
    result = mkPiTT(params[i].type, result, params[i].name);
  }

  return result;
}

/**
 * Add elabMap entries to map constructor type positions to original param/field positions.
 *
 * For a record with n params and m fields, the constructor type is:
 *   (P1 : T1) → (P2 : T2) → ... → (Pn : Tn) → (F1 : FT1) → ... → (Fm : FTm) → R P1...Pn
 *
 * The kernel paths are:
 *   - constructors[0].type.domain → params[0].type
 *   - constructors[0].type.body.domain → params[1].type
 *   - ...
 *   - constructors[0].type.body^n.domain → fields[0].type
 *   - constructors[0].type.body^(n+1).domain → fields[1].type
 *   - ...
 */
function addRecordCtorTypeElabMappings(
  elabMap: ElabMap,
  numParams: number,
  numFields: number
): void {
  const totalBinders = numParams + numFields;

  for (let i = 0; i < totalBinders; i++) {
    // Build the kernel path: constructors[0].type.body.body...domain
    // Each position has i levels of .body before .domain
    let kernelPath = 'constructors[0].type';
    for (let j = 0; j < i; j++) {
      kernelPath += '.body';
    }
    kernelPath += '.domain';

    // Build the surface path: params[i].type or fields[i-numParams].type
    let surfacePath: string;
    if (i < numParams) {
      surfacePath = `params[${i}].type`;
    } else {
      surfacePath = `fields[${i - numParams}].type`;
    }

    elabMap.set(kernelPath, surfacePath);
  }
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
  options?: { allowUnsolvedSigMetas?: boolean; skipTotality?: boolean; withScrutineeCount?: number; assumeK?: boolean },
): ProcessDeclarationResult {

  const elabMap: ElabMap = new Map();
  const typeInfoMap: TypeInfoMap = new Map();

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
    sourceMap,
    withScrutineeCount: decl.withScrutineeCount,
    withScrutineeExprs: decl.withScrutineeExprs,
  };

  // Check the term declaration
  // (This handles: signature check & meta solving, clause checking with LHS/RHS,
  //  totality, recursion, and adds to context if no errors)
  const result = checkTermDeclaration(elabDecl, definitions, { ...options, typeInfoCollector: typeInfoMap });
  const finalTypeInfoMap = typeInfoMap.size > 0 ? typeInfoMap : undefined;

  if (!result.success) {
    return {
      success: false,
      compiled: createCompiledDeclaration(
        decl, kernelType, undefined, undefined, elabMap, sourceMap,
        false, result.errors, definitions, result.totalityResult,
        undefined, undefined, undefined, undefined, undefined, undefined, undefined, finalTypeInfoMap
      ),
      newDefinitions: definitions,
      errorCount: result.errors.length
    };
  }

  return {
    success: true,
    compiled: createCompiledDeclaration(
      decl, result.zonkedType, result.checkedValue, undefined, elabMap, sourceMap,
      true, [], result.definitions, result.totalityResult,
      undefined, undefined, undefined, undefined, undefined, undefined, undefined, finalTypeInfoMap
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
export function compileTTFromText(source: string, options?: CompileOptions): CompileResult {
  // Reset counters for fresh compilation
  resetWildcardCounter();
  resetWithCounter();

  // Parse @assumeK directive from source (overrides options)
  const sourceAssumeK = parseAssumeKDirective(source);
  // Default to true to match Lean's behavior (K enabled by default)
  const assumeK = sourceAssumeK ?? options?.assumeK ?? true;

  if (sourceAssumeK !== undefined) {
  }

  // 1. Parse the source file (parser skips directive lines)
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
      const sourceMap = adjustSourceMapToAbsolute(block.sourceMaps[declIndex], block.startLine, block.posOffset);

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

      // Save original surface value before desugaring (for semantic highlighting)
      // After desugaring, WithClause is replaced by a call to the auxiliary function,
      // losing the original source structure needed for syntax highlighting.
      const originalSurfaceValue = resolvedDecl.value;

      // Desugar with-clauses (may produce auxiliary declarations)
      const desugaredDecls = desugarWithClauses([resolvedDecl]);

      // Separate main declaration from auxiliaries
      // Auxiliaries must be processed FIRST because the main declaration references them
      const mainDecl = desugaredDecls[0];
      const auxiliaryDecls = desugaredDecls.slice(1);

      // Preserve original surface value on main declaration for semantic token extraction
      if (auxiliaryDecls.length > 0 && originalSurfaceValue) {
        mainDecl.originalSurfaceValue = originalSurfaceValue;
      }

      // First: register all auxiliary declarations in symbol context
      for (const auxDecl of auxiliaryDecls) {
        const auxNameResult = validateDeclarations([auxDecl], symbolContext);
        if (auxNameResult.success) {
          symbolContext = auxNameResult.value;
        }
      }

      // Pre-register the main function's type signature if there are auxiliaries
      // This allows auxiliaries to make recursive calls to the main function
      if (auxiliaryDecls.length > 0 && mainDecl.kind === 'def' && mainDecl.type && mainDecl.name) {
        try {
          const typePath: IndexPath = [{ kind: 'field', name: 'type' }];
          const appNamedArgLookup = createNamedArgInfoLookup(definitions);
          const elabMap: ElabMap = new Map();
          const mainKernelType = elabToKernelWithMap(mainDecl.type, elabMap, typePath, typePath, undefined, appNamedArgLookup);
          // Extract namedArgMap so implicit args are recognized when auxiliaries call the main function
          const mainNamedArgMap = extractNamedArgMap(mainDecl.type);
          definitions = addDefinition(definitions, mainDecl.name, mainKernelType, undefined, mainNamedArgMap.size > 0 ? mainNamedArgMap : undefined);
        } catch (_e) {
          // If type elaboration fails, continue - the error will be caught when we process the main decl
        }
      }

      // Resolve scrutinee types for auxiliaries with non-variable scrutinees.
      // This replaces Holes in the auxiliary type signatures with the actual
      // scrutinee types inferred from the definitions available at this point.
      // Must happen AFTER pre-registering the main type (so recursive calls work)
      // and BEFORE processing auxiliaries (so clause checking uses correct types).
      resolveAuxScrutineeTypes(auxiliaryDecls, definitions);

      // Process auxiliary declarations FIRST (so their types are available)
      // Note: auxiliary declarations are always term definitions (kind === 'def')
      const failedAuxNames = new Set<string>();
      const auxErrorsForMain: TCEnvError[] = [];
      const auxElabMapForMain: ElabMap = new Map();
      const compiledAuxiliaries: CompiledDeclaration[] = [];

      for (const auxDecl of auxiliaryDecls) {
        const result = processTermDeclaration(auxDecl, sourceMap, definitions, { allowUnsolvedSigMetas: true, withScrutineeCount: auxDecl.withScrutineeCount, assumeK });
        // Remap elabMap so with-clause surface paths map to aux kernel paths
        remapWithClauseElabMap(result.compiled, sourceMap, auxDecl.withScrutineeCount ?? 0);
        result.compiled.isWithAuxiliary = true;
        compiledAuxiliaries.push(result.compiled);
        compiledDecls.push(result.compiled);
        if (result.success) {
          definitions = result.newDefinitions;
        } else {
          // Track failed auxiliaries so we can filter cascading errors on the main declaration
          if (auxDecl.name) failedAuxNames.add(auxDecl.name);
          // Promote errors to the main declaration, replacing internal auxiliary name with main name
          const mainName = mainDecl.name ?? '';
          for (const err of result.compiled.checkErrors) {
            if (auxDecl.name && mainName && err.message.includes(auxDecl.name)) {
              auxErrorsForMain.push(TCEnvError.create(err.message.split(auxDecl.name).join(mainName), err.env));
            } else {
              auxErrorsForMain.push(err);
            }
          }
          // Collect auxiliary's elabMap for source range mapping of promoted errors
          if (result.compiled.elabMap) {
            for (const [key, value] of result.compiled.elabMap) {
              auxElabMapForMain.set(key, value);
            }
          }
        }
        totalCheckErrors += result.errorCount;
      }

      // Now process the main declaration
      if (mainDecl.kind === 'inductive') {
        // 3. If it is an inductive type def...
        const result = processInductiveDeclaration(mainDecl, sourceMap, definitions);
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
          // Recheck zonked constructor types if enabled
          if (options?.recheckZonkedTerms && result.compiled.kernelConstructors) {
            for (const ctor of result.compiled.kernelConstructors) {
              const recheckErr = recheckZonkedTerm(ctor.type, definitions, `${mainDecl.name}.${ctor.name} constructor type`);
              if (recheckErr) {
                const errEnv = createTCEnv({ definitions, options: { mode: 'check' } });
                result.compiled.checkErrors.push(TCEnvError.create(recheckErr, errEnv));
                result.compiled.checkSuccess = false;
                totalCheckErrors++;
              }
            }
          }
        }
        totalCheckErrors += result.errorCount;
      } else if (mainDecl.kind === 'record') {
        // 3b. If it is a record definition...
        const result = processRecordDeclaration(mainDecl, sourceMap, definitions);
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
          // Recheck zonked constructor types if enabled
          if (options?.recheckZonkedTerms && result.compiled.kernelConstructors) {
            for (const ctor of result.compiled.kernelConstructors) {
              const recheckErr = recheckZonkedTerm(ctor.type, definitions, `${mainDecl.name}.${ctor.name} constructor type`);
              if (recheckErr) {
                const errEnv = createTCEnv({ definitions, options: { mode: 'check' } });
                result.compiled.checkErrors.push(TCEnvError.create(recheckErr, errEnv));
                result.compiled.checkSuccess = false;
                totalCheckErrors++;
              }
            }
          }
        }
        totalCheckErrors += result.errorCount;
      } else {
        // 4. If we are looking at a term...
        const result = processTermDeclaration(mainDecl, sourceMap, definitions, { assumeK });
        // For declarations with with-clauses, remap scrutinee paths in elabMap
        // and merge auxiliary typeInfoMap entries so type-at-cursor works in with-clauses
        if (auxiliaryDecls.length > 0) {
          remapWithScrutineeInMainElabMap(result.compiled, sourceMap);
          for (const auxCompiled of compiledAuxiliaries) {
            mergeAuxTypeInfoIntoMain(result.compiled, auxCompiled);
          }
        }

        // Filter cascading "Type definition not found" errors for failed auxiliaries
        if (failedAuxNames.size > 0) {
          const originalCount = result.compiled.checkErrors.length;
          result.compiled.checkErrors = result.compiled.checkErrors.filter(err => {
            for (const auxName of failedAuxNames) {
              if (err.message.includes(`Type definition not found: ${auxName}`)) return false;
            }
            return true;
          });
          const suppressedCount = originalCount - result.compiled.checkErrors.length;
          totalCheckErrors -= suppressedCount;
        }

        // Attach promoted auxiliary errors to the main declaration
        if (auxErrorsForMain.length > 0) {
          result.compiled.withClauseErrors = auxErrorsForMain;
          if (auxElabMapForMain.size > 0) {
            result.compiled.withClauseElabMap = auxElabMapForMain;
          }
        }

        compiledDecls.push(result.compiled);

        if (result.success) {
          definitions = result.newDefinitions;
          // Recheck zonked type signature if enabled
          if (options?.recheckZonkedTerms && result.compiled.kernelType) {
            const recheckErr = recheckZonkedTerm(result.compiled.kernelType, definitions, `${mainDecl.name} type signature`);
            if (recheckErr) {
              const errEnv = createTCEnv({ definitions, options: { mode: 'check' } });
              result.compiled.checkErrors.push(TCEnvError.create(recheckErr, errEnv));
              result.compiled.checkSuccess = false;
              totalCheckErrors++;
            }
          }
          // Recheck zonked value if enabled (skip Match values)
          if (options?.recheckZonkedTerms && result.compiled.kernelValue) {
            const recheckErr = recheckZonkedTerm(result.compiled.kernelValue, definitions, `${mainDecl.name} value`);
            if (recheckErr) {
              const errEnv = createTCEnv({ definitions, options: { mode: 'check' } });
              result.compiled.checkErrors.push(TCEnvError.create(recheckErr, errEnv));
              result.compiled.checkSuccess = false;
              totalCheckErrors++;
            }
          }
        }
        totalCheckErrors += result.errorCount;
      }
    } // end for (let declIndex = 0; ...)

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
    totalCheckErrors,
    definitions
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
  originalSurfaceIndex: number,
  namedArgMap: NamedArgMap | undefined,
  totalArity: number | undefined,
): TTKClause {
  // Surface path uses the ORIGINAL surface index (before filtering absurd clauses)
  // Kernel path uses the filtered kernel index (after absurd clauses are removed)
  const clauseSurfacePath: IndexPath = [
    { kind: 'field', name: 'value' },
    { kind: 'field', name: 'clauses' },
    { kind: 'array', index: originalSurfaceIndex }
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

  // Remove elabMap entries for synthetic patterns (auto-inserted wildcards).
  // These patterns have no real source counterpart, so their elabMap entries
  // (which use fallback surface indices) would conflict with real pattern entries.
  if (sourceIndexMap) {
    for (let i = 0; i < sourceIndexMap.length; i++) {
      if (sourceIndexMap[i] === null) {
        const syntheticPath = serializeIndexPath(appendPath(clauseKernelPath, fieldSeg('patterns'), arraySeg(i)));
        elabMap.delete(syntheticPath);
      }
    }
  }

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
  surfaceClauseIndices: number[],
  elabMap: ElabMap,
  namedArgMap: NamedArgMap | undefined,
  totalArity: number | undefined,
  annotatedAbsurdClauses: number[] = [],
  options?: { skipTotality?: boolean; withScrutineeCount?: number },
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
    const originalSurfaceIndex = surfaceClauseIndices[clauseIndex];
    const rootPatternsCount = surfaceClause.patterns.length;

    if (rootPatternsCount !== firstClauseRootPatternsCount) {
      errors.push(TCEnvError.create(`Mismatch in pattern count: clause ${clauseIndex + 1} has ${rootPatternsCount} patterns, expected ${firstClauseRootPatternsCount}.`, termEnv));
    } else if (rootPatternsCount > maxAllowedPatternsCount) {
      errors.push(TCEnvError.create(`Pattern count exceeds type binders count: clause ${clauseIndex + 1} has ${rootPatternsCount} patterns, expected <= ${maxAllowedPatternsCount}.`, termEnv));
    } else {
      try {
        // Following the flow: elaborate LHS, unify & solve, then elaborate and check RHS
        // IMPORTANT: Pass originalSurfaceIndex (not clauseIndex) so ElabMap correctly maps
        // kernel clause indices to original surface clause indices
        const checkedClause = checkMatchClauseFromSurface(
          name ?? '???',
          surfaceClause,
          type,
          termEnv,
          elabMap,
          clauseIndex,
          originalSurfaceIndex,
          namedArgMap,
          totalArity
        );
        checkedClauses.push(checkedClause);
      } catch (e) {
        // Anchor the error to the specific clause, not the whole function
        // Use originalSurfaceIndex for error path so it maps correctly via sourceMap
        const clauseEnv = termEnv.atIndexPath(
          appendPath(termEnv.indexPath, fieldSeg('value'), fieldSeg('clauses'), arraySeg(originalSurfaceIndex))
        );
        if (e instanceof TCEnvError) {
          errors.push(e);
        } else {
          errors.push(TCEnvError.create(String(e), clauseEnv));
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
  let totalityClauses = checkedClauses.map(c => ({
    patterns: c.patterns,
    elabArgs: c.elabArgs,
    contextNames: c.contextNames
  }));

  // For with-clause auxiliaries: replace frozen function-pattern positions with PVar
  // so the totality checker only checks exhaustiveness over the scrutinee dimensions.
  // The frozen positions are guaranteed to be covered by construction (the caller
  // always passes specific constructor patterns from the parent clause context).
  if (options?.withScrutineeCount && options.withScrutineeCount > 0 && totalityClauses.length > 0) {
    const totalPatterns = totalityClauses[0].patterns.length;
    const frozenCount = totalPatterns - options.withScrutineeCount;
    if (frozenCount > 0) {
      totalityClauses = totalityClauses.map(c => ({
        ...c,
        patterns: [
          ...c.patterns.slice(0, frozenCount).map((_p, i) =>
            ({ tag: 'PVar' as const, name: `_ctxt${i}` })),
          ...c.patterns.slice(frozenCount),
        ],
      }));
    }
  }

  const totalityResult = checkTotality(name ?? '???', totalityClauses, termEnv.definitions, absurdityChecker);

  // Annotate frozen position count for with-clause auxiliary case tree rendering
  if (options?.withScrutineeCount && options.withScrutineeCount > 0 && totalityClauses.length > 0) {
    const totalPatterns = totalityClauses[0].patterns.length;
    const frozenCount = totalPatterns - options.withScrutineeCount;
    if (frozenCount > 0) {
      totalityResult.frozenPositionCount = frozenCount;
    }
  }

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

  // Convert totality issues to errors (skip for auxiliary with-functions)
  const totalityErrors: TCEnvError[] = [];
  if (!options?.skipTotality) {
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

/**
 * Count the number of leading implicit (named) parameters in a type.
 * Returns the count of parameters before the first explicit parameter.
 */
function countLeadingImplicitParams(type: TTerm): number {
  let count = 0;
  let current = type;

  while (true) {
    if (current.tag === 'Binder' && current.binderKind.tag === 'BPiTT') {
      const isNamed = !!(current as any).named;
      if (!isNamed) break; // Stop at first explicit parameter
      count++;
      current = current.body;
    } else if (current.tag === 'MultiBinder' && current.binderKind.tag === 'BPiTT') {
      const isNamed = !!(current as any).named;
      if (!isNamed) break; // Stop at first explicit parameter
      count += current.names.length;
      current = current.body;
    } else {
      break;
    }
  }

  return count;
}

/**
 * Shift all free Var indices in a TTKTerm by the given amount.
 * This is used to adjust de Bruijn indices when moving a term between contexts.
 */
function shiftTTKVars(term: TTKTerm, amount: number, cutoff: number = 0): TTKTerm {
  if (amount === 0) return term;

  switch (term.tag) {
    case 'Var':
      if (term.index >= cutoff) {
        return { ...term, index: term.index + amount };
      }
      return term;

    case 'App': {
      const newFn = shiftTTKVars(term.fn, amount, cutoff);
      const newArg = shiftTTKVars(term.arg, amount, cutoff);
      if (newFn === term.fn && newArg === term.arg) return term;
      return { ...term, fn: newFn, arg: newArg };
    }

    case 'Binder': {
      const newDomain = shiftTTKVars(term.domain, amount, cutoff);
      const newBody = shiftTTKVars(term.body, amount, cutoff + 1);
      if (newDomain === term.domain && newBody === term.body) return term;
      return { ...term, domain: newDomain, body: newBody };
    }

    default:
      // For other term types, recursively shift (or return as-is for constants)
      // This is a simplified version - extend as needed
      return term;
  }
}

/**
 * Resolve Holes in a TTKTerm by inferring their values from variable types.
 * For example, if we have `Equal {?A} (Var 3) (Var 2)` and we know that
 * Var 3 has type `Leq a b`, then we can resolve `?A` to `Leq a b`.
 */
function resolveImplicitHoles(term: TTKTerm, auxType: TTerm | undefined): TTKTerm {
  if (!auxType) return term;

  // Build a map of variable indices to their types from the auxiliary's type signature
  const varTypes: TTKTerm[] = [];
  let current = auxType;
  let depth = 0;

  while (current.tag === 'Binder' || current.tag === 'MultiBinder') {
    if (current.tag === 'Binder') {
      const kernelDomain = surfaceTermToKernel(current.domain);
      // Shift to account for the depth of this binder in the context
      const shiftedDomain = shiftTTKVars(kernelDomain, depth);
      varTypes.push(shiftedDomain);
      current = current.body;
      depth++;
    } else {
      // MultiBinder - all names share the same domain, shift by current depth ONCE
      const kernelDomain = surfaceTermToKernel(current.domain);
      const shiftedDomain = shiftTTKVars(kernelDomain, depth);
      for (let i = 0; i < current.names.length; i++) {
        varTypes.push(shiftedDomain);
      }
      depth += current.names.length;
      current = current.body;
    }
  }

  // Now walk the term and resolve Holes by looking at adjacent Vars
  function resolve(t: TTKTerm): TTKTerm {
    if (t.tag === 'App') {
      // Check if this is `Equal {?Hole} (Var n) ...` pattern
      const resolvedFn = resolve(t.fn);
      const resolvedArg = resolve(t.arg);

      // If fn is `Equal {?Hole}` and arg is a Var, use Var's type for the Hole
      if (resolvedFn.tag === 'App' && resolvedFn.fn.tag === 'Const' &&
          resolvedFn.fn.name === 'Equal' && resolvedFn.arg.tag === 'Hole' &&
          resolvedArg.tag === 'Var' && resolvedArg.index < varTypes.length) {
        // Var i refers to the variable bound i positions ago, so we need to
        // look up varTypes in reverse: varTypes[n - 1 - i]
        const varTypeIndex = varTypes.length - 1 - resolvedArg.index;
        const varType = varTypes[varTypeIndex];
        // Replace the Hole with the variable's type
        return { ...t, fn: { ...resolvedFn, arg: varType }, arg: resolvedArg };
      }

      if (resolvedFn === t.fn && resolvedArg === t.arg) return t;
      return { ...t, fn: resolvedFn, arg: resolvedArg };
    } else if (t.tag === 'Binder') {
      const resolvedDomain = resolve(t.domain);
      const resolvedBody = resolve(t.body);
      if (resolvedDomain === t.domain && resolvedBody === t.body) return t;
      return { ...t, domain: resolvedDomain, body: resolvedBody };
    }
    return t;
  }

  return resolve(term);
}

/**
 * Resolve scrutinee types for with-clause auxiliary declarations.
 *
 * When computeAuxiliaryType in with-desugar.ts encounters a non-variable
 * scrutinee (e.g., `decEqNat x y`), it uses a Hole for the scrutinee
 * Pi-binder domain because the scrutinee's type isn't available at
 * desugaring time. This leaves the type free during clause checking,
 * allowing it to be solved unsoundly (matching the return type after
 * pattern refinement rather than the actual scrutinee type).
 *
 * This function computes the correct scrutinee types by:
 * 1. Looking up the scrutinee expression's head function type
 * 2. Walking its Pi chain, substituting the applied arguments
 * 3. Replacing the Hole in the auxiliary's surface type with the result
 *
 * This ensures clause checking uses the correct scrutinee type,
 * preventing unsound pattern matching in with-clause auxiliaries.
 */
function resolveAuxScrutineeTypes(
  auxiliaryDecls: ParsedDeclaration[],
  definitions: DefinitionsMap,
): void {
  for (const auxDecl of auxiliaryDecls) {
    if (!auxDecl.withScrutineeExprs || auxDecl.withScrutineeExprs.length === 0) continue;
    if (!auxDecl.type) continue;

    for (let i = 0; i < auxDecl.withScrutineeExprs.length; i++) {
      const scrutExpr = auxDecl.withScrutineeExprs[i];

      // Skip variable scrutinees — computeAuxiliaryType already handles them
      if (scrutExpr.tag === 'Var') continue;

      try {
        const scrutType = inferScrutineeExprType(scrutExpr, definitions);
        if (scrutType) {
          // The inferred type's Var indices are from the clause context, which includes
          // all function parameters (implicit and explicit). The auxiliary has the SAME
          // context structure (implicit params + explicit params from patterns), so NO
          // shift is needed. However, we do need to resolve implicit argument Holes.

          // Resolve any implicit argument Holes by looking up variable types
          const resolvedScrutType = resolveImplicitHoles(scrutType, auxDecl.type);

          // Convert kernel type to surface term and replace the hole
          const surfaceScrutType = kernelTypeToSurface(resolvedScrutType);
          auxDecl.type = replaceHoleInSurfaceTerm(auxDecl.type!, `_scrut${i}_type`, surfaceScrutType);
        }
      } catch (_e) {
        // If inference fails, leave the hole as-is (best effort)
      }
    }
  }
}

/**
 * Infer the type of a scrutinee expression by walking the head function's
 * Pi type and substituting applied arguments.
 *
 * For `decEqNat x y` where `decEqNat : (x : Nat) -> (y : Nat) -> DecEq x y`:
 *   1. Head = Const("decEqNat"), args = [Var(1), Var(0)]
 *   2. Look up type: (x : Nat) -> (y : Nat) -> DecEq x y
 *   3. Substitute Var(1) for x: (y : Nat) -> DecEq (Var(1)) y
 *   4. Substitute Var(0) for y: DecEq (Var(1)) (Var(0))
 *   Result: DecEq (Var(1)) (Var(0))
 */
function inferScrutineeExprType(scrutExpr: TTerm, definitions: DefinitionsMap): TTKTerm | undefined {
  // Flatten the application spine: f a b c → head=f, args=[a, b, c]
  const args: TTerm[] = [];
  let head = scrutExpr;
  while (head.tag === 'App') {
    args.unshift(head.arg);
    head = head.fn;
  }

  if (head.tag !== 'Const') return undefined;

  // Look up the head function's type and namedArgMap from definitions
  const termDef = definitions.terms.get(head.name);
  if (!termDef?.type) return undefined;
  const headType = termDef.type;
  const namedArgMap = termDef.namedArgMap;

  // Build a set of implicit positions from namedArgMap
  const implicitPositions = new Set<number>();
  if (namedArgMap) {
    for (const pos of namedArgMap.values()) {
      implicitPositions.add(pos);
    }
  }

  // Walk Pi chain, matching explicit args and skipping implicits
  let type = headType;
  let argIdx = 0;
  let piIdx = 0;

  while (type.tag === 'Binder' && type.binderKind.tag === 'BPi') {
    if (implicitPositions.has(piIdx)) {
      // Implicit parameter: substitute a Hole (will be resolved during checking)
      type = subst(0, { tag: 'Hole', id: `_impl_scrut_${piIdx}` }, type.body);
      piIdx++;
    } else if (argIdx < args.length) {
      // Explicit parameter: substitute the corresponding argument
      const kernelArg = surfaceTermToKernel(args[argIdx]);
      type = subst(0, kernelArg, type.body);
      argIdx++;
      piIdx++;
    } else {
      break;
    }
  }

  // If we consumed all arguments, `type` is the return type
  return argIdx === args.length ? type : undefined;
}

/**
 * Convert a surface TTerm to a kernel TTKTerm (structural conversion).
 * Only handles the term forms that commonly appear in scrutinee expressions.
 */
function surfaceTermToKernel(t: TTerm): TTKTerm {
  switch (t.tag) {
    case 'Var': return { tag: 'Var', index: t.index };
    case 'Const': return { tag: 'Const', name: t.name };
    case 'App': return { tag: 'App', fn: surfaceTermToKernel(t.fn), arg: surfaceTermToKernel(t.arg) };
    case 'Hole': return { tag: 'Hole', id: t.id };
    case 'Sort': return { tag: 'Sort', level: surfaceTermToKernel(t.level) };
    case 'ULit': return { tag: 'ULit', n: t.n };
    default: return { tag: 'Hole', id: `_unsupported_${t.tag}` };
  }
}

/**
 * Convert a kernel TTKTerm to a surface TTerm (structural conversion).
 * Only handles the type forms that commonly appear as scrutinee types.
 */
function kernelTypeToSurface(t: TTKTerm): TTerm {
  const prop = mkPropTT();
  switch (t.tag) {
    case 'Var': return mkVarTT(t.index);
    case 'Const': return mkConstTT(t.name);
    case 'App': return mkAppTT(kernelTypeToSurface(t.fn), kernelTypeToSurface(t.arg));
    case 'Sort': return { tag: 'Sort', level: kernelTypeToSurface(t.level) } as TTerm;
    case 'ULit': return mkULitTT(t.n);
    case 'Hole': return mkHoleTT(t.id, prop);
    case 'Binder': {
      if (t.binderKind.tag === 'BPi') {
        return mkPiTT(kernelTypeToSurface(t.domain), kernelTypeToSurface(t.body), t.name);
      }
      return mkHoleTT('_unsupported_binder', prop);
    }
    default: return mkHoleTT(`_unsupported_${t.tag}`, prop);
  }
}

/**
 * Replace a Hole with a given name in a surface term tree.
 * Used to substitute computed scrutinee types into auxiliary function types.
 */
function replaceHoleInSurfaceTerm(term: TTerm, holeName: string, replacement: TTerm): TTerm {
  switch (term.tag) {
    case 'Hole':
      if (term.id === holeName) return replacement;
      return term;
    case 'Binder': {
      const newDomain = term.domain ? replaceHoleInSurfaceTerm(term.domain, holeName, replacement) : undefined;
      const newBody = replaceHoleInSurfaceTerm(term.body, holeName, replacement);
      if (newDomain === term.domain && newBody === term.body) return term;
      return { ...term, domain: newDomain, body: newBody };
    }
    case 'MultiBinder': {
      const newDomain = replaceHoleInSurfaceTerm(term.domain, holeName, replacement);
      const newBody = replaceHoleInSurfaceTerm(term.body, holeName, replacement);
      if (newDomain === term.domain && newBody === term.body) return term;
      return { ...term, domain: newDomain, body: newBody };
    }
    case 'App': {
      const newFn = replaceHoleInSurfaceTerm(term.fn, holeName, replacement);
      const newArg = replaceHoleInSurfaceTerm(term.arg, holeName, replacement);
      if (newFn === term.fn && newArg === term.arg) return term;
      return { ...term, fn: newFn, arg: newArg };
    }
    case 'Annot': {
      const newTerm = replaceHoleInSurfaceTerm(term.term, holeName, replacement);
      const newType = replaceHoleInSurfaceTerm(term.type, holeName, replacement);
      if (newTerm === term.term && newType === term.type) return term;
      return { tag: 'Annot', term: newTerm, type: newType };
    }
    default:
      return term;
  }
}
