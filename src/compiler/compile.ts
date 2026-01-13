/**
 * Fresh TT Compiler - A clean implementation of the compilation pipeline
 *
 * This module provides a simple interface for compiling TT source code
 * to elaborated kernel terms (TTK).
 */

import { groupByIndentation } from '../parser/indentation-grouper';
import { Parser, ParsedDeclaration, ParseError } from '../parser/tt-parser';
import { elabToKernelWithMap } from '../types/tt-elab-source';
import { TTKTerm, TTKContext, prettyPrint as prettyPrintTTK, TTKClause, TTKPattern, prettyPrintPattern, prettyPrint, shiftTerm } from '../types/tt-kernel';
import { validateDeclarations, emptySymbolContext, SymbolContext } from '../types/name-resolution';
import { resolvePatternsInDeclarations } from '../parser/pattern-resolution';
import { ElabMap, IndexPath, SourceMap } from '../types/source-position';
import { checkInductiveDeclaration, CheckError } from '../types/tt-typecheck-decl';
import { inferParameterIndices } from '../types/tt-inductive-inference';
import { mkApp, mkConst, mkType, mkVar } from '../types/tt-core';

// ============================================================================
// Parse Result Types
// ============================================================================

type DefinitionsMap = Map<string, TTKTerm>

class TypeCheckError extends Error {
  constructor(message: string, public term?: TTKTerm, public context?: TTKContext, public termPath?: IndexPath, public definitions?: DefinitionsMap) {
    super(message);
    this.name = 'TypeCheckError';
  }
}

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
  kernelType?: TTKTerm;
  kernelValue?: TTKTerm;
  kernelConstructors?: Array<{ name: string; type: TTKTerm }>;
  /** For inductive types: positions that are indices (not parameters) */
  indexPositions?: number[];
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
  checkErrors: CheckError[];

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
 * Elaborate parsed TT to kernel terms (TTK).
 *
 * Pipeline:
 * 1. Name resolution (validate all identifiers are defined)
 * 2. Pattern resolution (resolve PCtor vs PVar in patterns)
 * 3. Elaborate TT -> TTK
 *
 * @param parseResult - Result from parseTTSource
 * @param _initialContext - Optional initial typing context (for imports/prelude)
 * @returns ElabResult with elaborated blocks
 */
export function elabTT(parseResult: ParseResult, _initialContext: TTKContext = []): ElabResult {
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

        // Elaborate value
        if (decl.value) {
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

        // Compute index positions for inductive types (BEFORE elaboration, on TT)
        let indexPositions: number[] | undefined;
        if (decl.kind === 'inductive' && decl.name && decl.type && decl.constructors) {
          indexPositions = inferParameterIndices({
            name: decl.name,
            type: decl.type,
            constructors: decl.constructors
          });
        }

        elabDeclarations.push({
          name: decl.name,
          kind: decl.kind === 'inductive' ? 'inductive' : 'term',
          kernelType,
          kernelValue,
          kernelConstructors,
          indexPositions,
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
  const checkErrors: CheckError[] = [];
  let newDefinitions = definitions;
  let errorCount = 0;

  const result = decl.kind === 'inductive' ?
    checkInductiveTypeDeclaration(decl, definitions) :
    decl.kind === 'term' ? checkTermDeclaration(decl, definitions) :
      { success: false as const, errors: [{ message: 'Declaration is not an inductive or term', path: [] }] };

  if (result.success) {
    newDefinitions = result.definitions;
  } else {
    checkSuccess = false;
    checkErrors.push(...result.errors);
    errorCount = result.errors.length;
  }

  // Build compiled declaration with pretty-printed versions
  const compiled: CompiledDeclaration = {
    name: decl.name,
    kind: decl.kind,
    kernelType: decl.kernelType,
    kernelValue: decl.kernelValue,
    kernelConstructors: decl.kernelConstructors,
    indexPositions: decl.indexPositions,
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
): { success: false, errors: CheckError[] } | { success: true, definitions: DefinitionsMap } {
  if (decl.kind !== 'inductive') {
    return failCheck('Declaration is not an inductive type', [])
  }

  if (!decl.kernelType) {
    return failCheck('Inductive type declaration is ill-formed', [])
  }
  if (!decl.kernelConstructors) {
    return failCheck('Inductive type declaration is ill-formed', [])
  }

  const result = checkInductiveDeclaration(
    decl.name || 'anonymous',
    decl.kernelType,
    decl.kernelConstructors,
    [],
    decl.indexPositions
  );
  if (!result.success) {
    return {
      success: false,
      errors: result.errors,
    }
  } else {
    let newDefinitions = new Map<string, TTKTerm>(definitions);
    newDefinitions.set(decl.name || 'anonymous', decl.kernelType);
    for (const ctor of decl.kernelConstructors) {
      newDefinitions.set(ctor.name, ctor.type);
    }
    return {
      success: true,
      definitions: newDefinitions,
    }
  }
}

function failCheck(message: string, path: IndexPath): { success: false, errors: CheckError[] } {
  return {
    success: false,
    errors: [{
      message,
      path,
    }],
  }
}

function checkTermDeclaration(
  decl: ElabDeclaration,
  definitions: DefinitionsMap,
): { success: false, errors: CheckError[] } | { success: true, definitions: DefinitionsMap } {
  if (decl.kind !== 'term') {
    return failCheck('Declaration is not a term', [])
  }

  if (!decl.kernelType) {
    return failCheck('Term declaration is ill-formed', [])
  }

  let newDefinitions = definitions

  try {
    if (!decl.kernelValue) {
      return failCheck('Term declaration is ill-formed', [])
    }

    const _inferredType = inferType(decl.kernelType, [], definitions);

    // Add to context for subsequent declarations
    if (decl.name) {
      newDefinitions.set(decl.name, decl.kernelType);
    }

    const x = checkTermValue(decl.name, decl.kernelValue, decl.kernelType, newDefinitions);
    if (!x.success) {
      return {
        success: false,
        errors: x.errors,
      }
    }

    return { success: true, definitions: newDefinitions }
  } catch (e) {
    const message = e instanceof TypeCheckError ? e.message :
      (e instanceof Error ? e.message : String(e));
    const path: IndexPath = e instanceof TypeCheckError && e.termPath ? e.termPath :
      [{ kind: 'field', name: 'type' }];

    return {
      success: false,
      errors: [{
        message,
        path,
        term: e instanceof TypeCheckError ? e.term : decl.kernelType,
        definitions: e instanceof TypeCheckError ? e.definitions : definitions
      }],
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
 * Check all elaborated blocks and return compiled blocks with type check results.
 */
function checkBlocks(
  elabResult: ElabResult,
  initialDefinitions: DefinitionsMap = new Map<string, TTKTerm>(),
): CheckBlocksResult {
  const compiledBlocks: CompiledBlock[] = [];
  let currentDefinitions = initialDefinitions;
  let totalCheckErrors = 0;

  for (let blockIndex = 0; blockIndex < elabResult.blocks.length; blockIndex++) {
    const block = elabResult.blocks[blockIndex];
    const result = checkBlock(block, blockIndex, currentDefinitions);
    compiledBlocks.push(result.compiled);
    currentDefinitions = result.newDefinitions;
    totalCheckErrors += result.errorCount;
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
 * Pipeline:
 * 1. Parse source (grouping, parsing)
 * 2. Elaborate to TTK (name resolution, pattern resolution, TT -> TTK)
 * 3. Type check
 *
 * @param source - The full source code
 * @returns CompileResult with elaborated declarations
 */
export function compileTTFromText(source: string): CompileResult {
  const parseResult = parseTTSource(source);
  const elabResult = elabTT(parseResult);
  const checkResult = checkBlocks(elabResult);

  return {
    success: parseResult.totalErrors === 0 && checkResult.totalCheckErrors === 0,
    blocks: checkResult.blocks,
    totalParseErrors: parseResult.totalErrors,
    totalNameErrors: 0,
    totalCheckErrors: checkResult.totalCheckErrors
  };
}

type Signature = { name: string, type: TTKTerm }[];
type PiSpine = { binders: Signature, body: TTKTerm, term: TTKTerm };
type AppSpine = { fn: TTKTerm, args: TTKTerm[] };

function signatureToNamesStack(signature: Signature): string[] {
  return signature.map(n => n.name).reverse()
}

function extractPiSpine(term: TTKTerm): PiSpine {
  const binders: Signature = [];
  let current = term;
  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    binders.push({ name: current.name, type: current.domain });
    current = current.body;
  }
  return { binders, body: current, term };
}

function extractAppSpine(term: TTKTerm): AppSpine {
  const args: TTKTerm[] = [];
  let current = term;
  while (current.tag === 'App') {
    args.unshift(current.arg);
    current = current.fn;
  }
  return { fn: current, args };
}

function checkTermValue(
  name: string | undefined,
  value: TTKTerm,
  type: TTKTerm,
  definitions: DefinitionsMap
): { success: false, errors: CheckError[] } | { success: true } {
  if (value.tag !== 'Match') {
    try {
      checkType(value, type, [], definitions);
      return { success: true };
    } catch (e) {
      return {
        success: false, errors: [{ message: e instanceof TypeCheckError ? e.message : String(e), path: [], term: value, definitions }]
      }
    }
  }

  const typePiSpine = extractPiSpine(type);

  const errors: CheckError[] = [];

  // TODO - ensure all clauses have same pattern count
  // TODO - ensure pattern count is less than or equal type binders count

  value.clauses.forEach((clause, _clauseIndex) => {
    const result = checkMatchClause(name ?? '???', clause, typePiSpine, definitions);
    if (!result.success) {
      errors.push(...result.errors);
    }
  });

  // TODO: structural recursion check
  // TODO: totality check

  return { success: errors.length === 0, errors };
}

function contextLookup(name: string, ctx: TTKContext): TTKTerm | undefined {
  for (const binding of ctx) {
    if (binding.name === name) {
      return binding.type;
    }
  }
  return undefined;
}

function loopupTypeAtIndexSignature(signature: Signature, index: number): TTKTerm {
  const type = signature[index].type;

  // Shift indices to be at tail of signature
  // The type at position `index` needs to be shifted by (signature.length - 1 - index)
  // to move it to the tail position
  const shiftAmount = signature.length - 1 - index;
  return shiftAmount > 0 ? shiftTerm(type, shiftAmount, 0) : type;
}

/* PATTERNS */

function checkMatchClause(
  termName: string,
  clause: TTKClause,
  typePiSpine: PiSpine,
  definitions: DefinitionsMap
): { success: false, errors: CheckError[] } | { success: true } {
  const result = processMatchClauseLhs(termName, clause.patterns, typePiSpine, definitions)
  // TODO
  return { success: true };
}

const originalConsoleLog = console.log

function processMatchClauseLhs(termName: string, patterns: TTKPattern[], typePiSpine: PiSpine, definitions: DefinitionsMap) {
  if (termName === 'vecConcat') {
    console.log = originalConsoleLog
  } else {
    console.log = () => { }
  }
  console.log(`LHS: ${prettyPrintPattern({ tag: 'PCtor', name: termName, args: patterns })}`);

  let sig: Signature = []
  for (let i = 0; i < patterns.length; i++) {
    const binder = typePiSpine.binders[i];
    const checkType = typePiSpine.binders[i].type;
    const result = checkPattern(patterns[i], binder.name, checkType, sig, definitions);

    if (result.success) {
      sig = result.newSignature;
    } else {
      console.error(`Error: ${result.errors.map(e => e.message).join(', ')}`);
      return result
    }
  }

  return { success: true, newSignature: sig };
}

function checkPattern(pattern: TTKPattern, preferredName: string | undefined, checkType: TTKTerm, signature: Signature, definitions: DefinitionsMap): {
  success: true,
  newSignature: Signature;
} | {
  success: false,
  errors: CheckError[];
} {
  if (pattern.tag === 'PCtor') {
    const { name, args } = pattern;
    return checkCtorPattern(name, args, checkType, signature, definitions);
  } else if (pattern.tag === 'PVar') {
    let name = pattern.name

    if (pattern.name === '_') {
      name = `?${preferredName ?? ''}${signature.length}`
    }

    const type = checkType.tag === 'Var' ? loopupTypeAtIndexSignature(signature, checkType.index) :
      (checkType.tag === 'Const' || checkType.tag === 'Sort' || checkType.tag === 'App') ? checkType :
        undefined

    if (!type) {
      debugger
      return failCheck(`Unknown pattern type: ${prettyPrint(checkType)}`, []);
    }

    console.log(`  ${name}: ${prettyPrint(type, signatureToNamesStack(signature))}`);

    return {
      success: true,
      newSignature: [...signature, { name, type: checkType }]
    }
  }

  return failCheck(`Unknown pattern type: ${prettyPrintPattern(pattern)}`, []);
}

function checkCtorPattern(
  patternCtorName: string,
  patternArgs: TTKPattern[],
  checkType: TTKTerm,
  signature: Signature,
  definitions: DefinitionsMap
): {
  success: true,
  newSignature: Signature;
} | {
  success: false,
  errors: CheckError[];
} {
  const definition = definitions.get(patternCtorName);
  if (!definition) {
    return { success: false, errors: [{ message: `Constructor '${patternCtorName}' not found`, path: [], term: checkType, definitions } as CheckError] };
  }

  const { binders: definitionBinders, body: definitionBody } = extractPiSpine(definition);

  if (patternArgs.length !== definitionBinders.length) {
    return failCheck(`Constructor '${patternCtorName}' has wrong number of arguments`, [])
  }

  let sig = signature
  for (let i = 0; i < patternArgs.length; i++) {
    const result = checkPattern(patternArgs[i], definitionBinders[i].name, definitionBinders[i].type, sig, definitions);
    if (result.success) {
      sig = result.newSignature;
    } else {
      return result
    }
  }

  const result = checkElaboratedPattern(patternCtorName, patternArgs, signature, sig, checkType, definitions)
  if (!result.success) {
    return result
  }

  // TODO?

  return result
}

function convertCtorPatternToAppTerm(patternCtorName: string, patternArgs: TTKPattern[], newNames: string[], _preSignature: Signature, signature: Signature): TTKTerm {
  const fn = mkConst(patternCtorName, mkType(-1) /* HACK */)

  let term = fn

  for (let i = 0; i < patternArgs.length; i++) {
    const pattern = patternArgs[i]
    if (pattern.tag === 'PCtor') {
      debugger
    } else {
      const patternName = newNames[i] ?? pattern.name
      const sigIndex = signature.findIndex(b => b.name === patternName)
      const arg = mkVar(signature.length - sigIndex - 1)
      term = mkApp(term, arg)
    }
  }

  return term
}

function checkElaboratedPattern(
  patternCtorName: string,
  patternArgs: TTKPattern[],
  preSignature: Signature,
  signature: Signature,
  checkType: TTKTerm,
  definitions: DefinitionsMap,
): { success: true, newSignature: Signature } | { success: false, errors: CheckError[] } {
  const newNames = signature.slice(preSignature.length).map(({ name }) => name)
  const namesStack = signatureToNamesStack(signature)

  const inferredTerm = convertCtorPatternToAppTerm(patternCtorName, patternArgs, newNames, preSignature, signature)
  const inferredType = inferType(inferredTerm, [], definitions)

  console.log(`  CHECK: ${prettyPrint(inferredTerm, namesStack)} : ? = ${prettyPrint(checkType, namesStack)}`);

  return { success: true, newSignature: signature }
}

function inferType(_term: TTKTerm, _path: IndexPath, _definitions: DefinitionsMap): TTKTerm {
  throw new Error('Not implemented')
}

function checkType(_term: TTKTerm, _expectedType: TTKTerm, _definitions: DefinitionsMap, _path: IndexPath): void {
  throw new Error('Not implemented')
}