/**
 * Fresh TT Compiler - A clean implementation of the compilation pipeline
 *
 * This module provides a simple interface for compiling TT source code
 * to elaborated kernel terms (TTK).
 */

import { ParsedDeclaration, ParseError } from '../parser/parser';
import { elabPatternToKernel, elabPatternToKernelWithMap, resetWildcardCounter, extractConstructorParamNames, setConstructorParamNames, setCurrentTermParamNames, reorderPatterns, hasNamedPatterns, applyVarPermutation, fixRhsForConstructorPatterns, fixRhsForVariablePatterns, NamedArgMap, elabToKernel } from './elab';
import { TTKTerm, TTKContext, TTKClause, TTKPattern, prettyPrintPattern, prettyPrintPatternList, mkType } from './kernel';
import { TTerm, TPattern, TClause, mkULitTT, mkSortTT, mkUOmegaTT } from './surface';
import { arraySeg, fieldSeg, appendPath, ElabMap, IndexPath, SourceMap, serializeIndexPath } from '../types/source-position'
import { addDefinitionInTCEnv, countPiBinders, DefinitionsMap, extractPiSpine, InductiveDefinition, MatchPartIndex, TCEnv, TCEnvError, TermDefinition, TermDefinitionPartIndex, validateTermNameNotDefined } from './term';
import { checkMatchClause, arePatternsAbsurd } from './patterns';
import { checkTotality, TotalityResult, CaseTree } from './totality';
import { checkStructuralRecursion } from './recursion';
import { resetWithCounter } from './with-desugar';
import { subst } from './subst';
import { IncrementalCache } from './incremental';
import { whnf } from './whnf';
import type { TypeInfoMap } from './type-info';
import { parseTTSource } from './compile-parse';
import type {
  CompileOptions,
  CompileResult,
  ElabDeclaration,
  ProcessDeclarationResult,
} from './compile-types';
import {
  extractHoleLocations,
  extractSemanticTokens,
  extractWildcardInlayHints,
} from './compile-editor-data';
import {
  collectAppSpine,
  kernelTypeToSurface,
  lookupNamedArgMap,
} from './compile-bridge';
import { tryCaseSplitsInSearchOfAbsurdity } from './compile-term-value';
import { resolveWithScrutineeTypes } from './compile-with-scrutinee-resolution';
import {
  compileParsedBlocks,
  compileParsedBlocksIncrementally,
  reuseLastIncrementalResult,
} from './compile-loop-orchestration';
import { parseAssumeKDirective } from './compile-directives';
import { elaborateTacticBlock } from './compile-tactic-block';
import { recheckZonkedTerm } from './compile-zonk-recheck';
export type {
  CompileOptions,
  CompileResult,
  CompiledBlock,
  CompiledDeclaration,
  ElabDeclaration,
  NameResolutionErrorWithRange,
  ParseResult,
  ParsedBlock,
  ProcessDeclarationResult,
} from './compile-types';
export type { TotalityResult, CaseTree };
export {
  extractDirectiveTokens,
  extractHoleLocations,
  extractSemanticTokens,
  extractWildcardInlayHints,
  SHOW_WILDCARD_INLAY_HINTS,
  type HoleLocation,
  type SemanticToken,
  type SemanticTokenType,
  type WildcardInlayHint,
} from './compile-editor-data';

// ============================================================================
// SourceMap Adjustment Helper
// ============================================================================



export { parseTTSource };



// ============================================================================
// Main Compile Function
// ============================================================================

// ============================================================================
// Full compilation
// ============================================================================

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

  return compileParsedBlocks(parseResult, {
    assumeK,
    elaborateTacticBlock,
    recheckZonkedTerm,
    options,
  });
}
// ============================================================================
// Incremental compilation
// ============================================================================


/**
 * Incrementally compile TT source, reusing cached results for unchanged blocks.
 *
 * Algorithm:
 * 1. Parse the source, compare block texts with cache to find changed blocks
 * 2. Compute the transitive recheck set via dependency DAG
 * 3. Walk blocks in order: replay cached contributions or recompile
 * 4. Return CompileResult (same shape as compileTTFromText)
 *
 * The cache is mutated in-place for efficiency (designed for useRef).
 */
export function compileIncrementalTT(
  source: string,
  cache: IncrementalCache,
  options?: CompileOptions
): CompileResult {
  const reusableResult = reuseLastIncrementalResult(source, cache);
  if (reusableResult) {
    return reusableResult;
  }

  // Reset counters for fresh compilation
  resetWildcardCounter();
  resetWithCounter();

  const sourceAssumeK = parseAssumeKDirective(source);
  const assumeK = sourceAssumeK ?? options?.assumeK ?? true;

  // 1. Parse the source
  const parseResult = parseTTSource(source);

  return compileParsedBlocksIncrementally(parseResult, cache, {
    assumeK,
    elaborateTacticBlock,
    recheckZonkedTerm,
    options,
  });
}

// ============================================================================
// Helper Functions for Absurdity Checking
// ============================================================================
