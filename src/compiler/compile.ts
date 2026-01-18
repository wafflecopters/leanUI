/**
 * Fresh TT Compiler - A clean implementation of the compilation pipeline
 *
 * This module provides a simple interface for compiling TT source code
 * to elaborated kernel terms (TTK).
 */

import { groupByIndentation } from '../parser/indentation-grouper';
import { Parser, ParsedDeclaration, ParseError } from '../parser/tt-parser';
import { elabToKernelWithMap } from '../types/tt-elab-source';
import { TTKTerm, TTKContext, prettyPrint as prettyPrintTTK, TTKClause, TTKPattern, prettyPrintPattern } from '../types/tt-kernel';
import { validateDeclarations, emptySymbolContext, SymbolContext } from '../types/name-resolution';
import { resolvePatternsInDeclarations } from '../parser/pattern-resolution';
import { ElabMap, IndexPath, SourceMap } from '../types/source-position'
import { mkApp, mkConst, mkType, mkVar, prettyPrint } from '../types/tt-core';
import { checkType, inferType } from './checker';
import { addDefinitionInTCEnv, createDefinitionsMap, createTCEnv, DefinitionsMap, extractPiSpine, PiSpine, setDefinitionValueInTCEnv, Signature, signatureToNamesStack, TCEnv, TCEnvError, TermDefinition, transformVarsInTerm } from './term';
import { checkInductiveDeclaration } from './inductive';

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

        elabDeclarations.push({
          name: decl.name,
          kind: decl.kind === 'inductive' ? 'inductive' : 'term',
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
 * Check all elaborated blocks and return compiled blocks with type check results.
 */
function checkBlocks(
  elabResult: ElabResult,
  initialDefinitions: DefinitionsMap = createDefinitionsMap(),
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

const originalConsoleLog = console.log

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

  const typePiSpine = extractPiSpine(type);

  const errors: TCEnvError<unknown>[] = [];

  // TODO - ensure all clauses have same pattern count
  // TODO - ensure pattern count is less than or equal type binders count

  const clausesEnv = env.inMatchClauses();
  for (let clauseIndex = 0; clauseIndex < clausesEnv.value.length; clauseIndex++) {
    if (name === 'nth' && clauseIndex === 1) {
      console.log = originalConsoleLog
    } else {
      console.log = () => { }
    }

    try {
      checkMatchClause(name ?? '???', clausesEnv.inMatchClause(clauseIndex), typePiSpine);
    } catch (e) {
      if (e instanceof TCEnvError) {
        errors.push(e);
      } else {
        errors.push(new TCEnvError(String(e), clausesEnv.inMatchClause(clauseIndex)));
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
  typePiSpine: PiSpine,
): TCEnv<void> {
  const result = processMatchClauseLhs(termName, env.inMatchClausePatterns(), typePiSpine)
  // TODO
  return result.withoutValue();
}

function processMatchClauseLhs(termName: string, env: TCEnv<TTKPattern[]>, typePiSpine: PiSpine): TCEnv<unknown> {
  console.log(`\n\nLHS: ${prettyPrintPattern({ tag: 'PCtor', name: termName, args: env.value })}`);
  const checkStack: PiSpine[] = [typePiSpine]
  const patternStack: TTKPattern[] = [...env.value].reverse()

  let workEnv: TCEnv<unknown> = env

  console.log(`\n  ~~ INITIAL STATE ~~`)
  console.log(`    P = [${patternStack.map(p => prettyPrintPattern(p)).join(', ')}]`)
  console.log(`    T = [${checkStack.map(prettyPrintPiSpine).join(', ')}]`)

  for (let i = 0; i < 100 && patternStack.length > 0; i++) {
    const pattern = patternStack.pop() as TTKPattern
    if (pattern.tag === 'PVar') {
      const checkType = checkStack.pop() as PiSpine
      const binder = checkType.binders[0] as { name: string, type: TTKTerm }

      console.log(`\nSTEP ${prettyPrintPattern(pattern)} against (${binder.name}: ${prettyPrint(binder.type)})`);
      console.log(`  Binding (${pattern.name} : ${prettyPrint(binder.type)})`);
      workEnv = workEnv.extendSignature(pattern.name, binder.type)

      checkStack.push(dropPiSpineOuterMostBinder(checkType))
    } else {
      console.log('TODO: handle PCtor pattern');
    }

    console.log(`\n  ~~ RESULT STATE ~~`)
    console.log(`    Γ = ${workEnv.printSignature()}`)
    console.log(`    P = [${patternStack.map(p => prettyPrintPattern(p)).join(', ')}]`)
    console.log(`    T = [${checkStack.map(prettyPrintPiSpine).join(', ')}]`)
  }

  return env
}

function dropPiSpineOuterMostBinder(piSpine: PiSpine): PiSpine {
  return {
    binders: piSpine.binders.slice(1),
    body: piSpine.body,
  }
}

function prettyPrintPiSpine(piSpine: PiSpine): string {
  let names: string[] = []
  const binders = `(${piSpine.binders.map(b => {
    const result = b.name && b.name !== '_' ? `(${b.name} : ${prettyPrint(b.type, names)})` : prettyPrint(b.type, names)
    names.push(b.name)
    return result
  }).join(' -> ')})`
  return `${binders} -> ${prettyPrint(piSpine.body, names.reverse())}`
}

// function processMatchClauseLhs(termName: string, env: TCEnv<TTKPattern[]>, typePiSpine: PiSpine): TCEnv<PatternTerm[]> {
//   console.log(`LHS: ${prettyPrintPattern({ tag: 'PCtor', name: termName, args: env.value })}`);

//   let patternTerms: PatternTerm[] = []
//   let newEnv: TCEnv<TTKPattern[]> = env

//   for (let i = 0; i < env.value.length; i++) {
//     const binder = typePiSpine.binders[i];
//     const checkType = typePiSpine.binders[i].type;
//     const result = checkPattern(newEnv.inMatchClausePattern(i), binder.name, patternTerms, checkType);
//     patternTerms = result.value;
//     newEnv = result.atValueAndPathOfEnv(env);
//   }

//   return newEnv.withValue(patternTerms);
// }

// type PatternTerm = TTKTerm | { tag: 'patternVar', name: string }

// function checkPattern(env: TCEnv<TTKPattern>, preferredName: string | undefined, patternTerms: PatternTerm[], checkType: TTKTerm): TCEnv<PatternTerm[]> {
//   if (env.isMatchClauseCtorPattern()) {
//     return checkCtorPattern(env, patternTerms, checkType);
//   } else if (env.isMatchClauseVarPattern()) {
//     const name = env.value.name === '_' ? `?${preferredName ?? ''}${env.signature.length}` : env.value.name

//     const adjustedType = transformVarsInTerm(checkType, (index, _signature) => {
//       const p = patternTerms
//       if (name === 'tail') {
//         // debugger
//       }
//       return mkVar(index)
//     });

//     const newPatternTerms: PatternTerm[] = [...patternTerms, { tag: 'patternVar', name }];
//     const newEnv = env.extendSignature(name, adjustedType).withValue(newPatternTerms);
//     console.log(`  SIG: ${newEnv.printSignature()}`);
//     console.log(`  PAT: ${prettyPrintPatternTerms(newPatternTerms, env)}\n\n`);
//     return newEnv;
//   }

//   throw env.unknownTagError(env.value, 'pattern', `Unknown pattern type: ${prettyPrintPattern(env.value)}`);
// }

// function checkCtorPattern(
//   env: TCEnv<TTKPattern & { tag: 'PCtor' }>,
//   patternTerms: PatternTerm[],
//   checkType: TTKTerm,
// ): TCEnv<PatternTerm[]> {
//   const patternCtorName = env.value.name;
//   if (patternCtorName === 'Succ') {
//     // debugger
//   }

//   const definition = env.getTypeDefinitionAssert(patternCtorName).value;
//   const { binders: definitionBinders, body: _definitionBody } = extractPiSpine(definition);

//   const patternArgs = env.value.args;
//   env.assertEqualLengths(patternArgs, definitionBinders, `Constructor '${patternCtorName}' has wrong number of arguments in pattern. Has ${patternArgs.length} but expected ${definitionBinders.length}`)

//   const patternsEnv = env.inMatchClauseCtorArgs()

//   let newEnv: TCEnv<unknown> = patternsEnv
//   let newPatternTerms = patternTerms

//   for (let i = 0; i < patternArgs.length; i++) {
//     const result = checkPattern(newEnv.atValueAndPathOfEnv(patternsEnv).inMatchClausePattern(i), definitionBinders[i].name, newPatternTerms, definitionBinders[i].type);
//     newPatternTerms = result.value;
//     newEnv = result.atValueAndPathOfEnv(patternsEnv);
//   }

//   const result = checkElaboratedPattern(newEnv.atValueAndPathOfEnv(env), env.signature.length, checkType)
//   newPatternTerms.length -= patternArgs.length;
//   newPatternTerms.push(result.value);
//   console.log(`  SIG: ${newEnv.printSignature()}`);
//   console.log(`  PAT: ${prettyPrintPatternTerms(newPatternTerms, env)}.\n\n`);
//   return newEnv.withValue(newPatternTerms);
// }

// function convertCtorPatternToAppTerm(patternCtorName: string, patternArgs: TTKPattern[], newNames: string[], signature: Signature): {
//   term: TTKTerm,
//   patternsTraversed: number,
// } {
//   const fn = mkConst(patternCtorName, mkType(-1) /* HACK */)

//   let term = fn
//   let sig = signature
//   let patternsTraversed = 0

//   for (let i = 0; i < patternArgs.length; i++) {
//     const pattern = patternArgs[i]
//     if (pattern.tag === 'PCtor') {
//       const arg = convertCtorPatternToAppTerm(pattern.name, pattern.args, newNames.slice(patternsTraversed), sig)
//       term = mkApp(term, arg.term)
//       patternsTraversed += arg.patternsTraversed
//     } else {
//       const patternName = newNames[i] ?? pattern.name
//       const sigIndex = sig.findIndex(b => b.name === patternName)
//       const arg = mkVar(sig.length - sigIndex - 1)
//       term = mkApp(term, arg)
//       patternsTraversed++
//     }
//   }

//   return { term, patternsTraversed }
// }

// function checkElaboratedPattern(
//   env: TCEnv<TTKPattern & { tag: 'PCtor' }>,
//   preSignatureLength: number,
//   checkType: TTKTerm,
// ): TCEnv<TTKTerm> {
//   const newNames = env.signature.slice(preSignatureLength).map(({ name }) => name)
//   const namesStack = signatureToNamesStack(env.signature)

//   const pattern = env.value;
//   const patternTerm = convertCtorPatternToAppTerm(pattern.name, pattern.args, newNames, env.signature).term

//   const patternTermEnv = env.withValue(patternTerm)

//   const inferredType = inferType(patternTermEnv)
//   console.log(`  CHECK: ${prettyPrint(patternTerm, namesStack)} : ${prettyPrint(inferredType.value, namesStack)} = ${prettyPrint(checkType, namesStack)}`);

//   return patternTermEnv
// }
