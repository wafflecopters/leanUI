/**
 * Block-Level Type Checking Pipeline
 *
 * This module orchestrates the full pipeline from source code to type-checked
 * blocks with error reporting:
 *
 * 1. Group source into blocks (indentation-based)
 * 2. Parse each block → ParsedDeclaration + SourceMap
 * 3. Name resolution → Validate all symbols are defined
 * 4. Elaborate all parsed declarations together → TTKTerm + ElabMap
 * 5. Type check all elaborated declarations together (parallel error collection)
 * 6. Map errors back to source blocks via declaration indices
 * 7. Return comprehensive results for UI display
 */

import { groupByIndentation, SourceBlock } from './indentation-grouper';
import { Parser, ParsedDeclaration, ParsedDeclarationWithSource, ParseError } from './tt-parser';
import { elabToKernelWithMap } from '../types/tt-elab-source';
import { checkTermDeclaration, checkInductiveDeclaration, CheckError } from '../types/tt-typecheck-decl';
import { resolveErrorLocation, resolveCheckErrorLocation, resolveNameResolutionErrorLocation } from '../types/error-resolution';
import { SourceMap, ElabMap, SourceRange, adjustSourceMapLines } from '../types/source-position';
import { TTKTerm } from '../types/tt-kernel';
import { validateDeclarations, NameResolutionError, emptySymbolContext, SymbolContext } from '../types/name-resolution';

/**
 * Result of checking a single source block.
 */
export interface BlockCheckResult {
  block: SourceBlock;
  blockIndex: number;

  // Parse result
  parseSuccess: boolean;
  parseErrors: ParseError[];
  declarations: ParsedDeclaration[];

  // Name resolution result
  nameResolutionSuccess: boolean;
  nameResolutionErrors: Array<{
    error: NameResolutionError;
    location: SourceRange | null;
  }>;

  // Type check result
  checkSuccess: boolean;
  checkErrors: Array<{
    error: CheckError;
    location: SourceRange | null;
  }>;

  // Display metadata
  blockType: 'Inductive' | 'Term' | 'Comment' | 'Unknown';
  name?: string;
  inferredType?: string;  // String representation of inferred type
}

/**
 * Internal structure for tracking elaborated declarations.
 */
interface ElaboratedDeclaration {
  blockIndex: number;
  declIndex: number;
  decl: ParsedDeclaration;
  sourceMap: SourceMap;
  elabMap: ElabMap;
  kernelType?: TTKTerm;
  kernelValue?: TTKTerm;
  kernelConstructors?: Array<{ name: string; type: TTKTerm }>;
}

/**
 * Check all source blocks in a file.
 *
 * Pipeline:
 * 1. Group source into blocks by indentation
 * 2. Parse each block (collect parse errors)
 * 3. Name resolution across all blocks (validate symbols)
 * 4. Elaborate all successfully parsed declarations together
 * 5. Type check all elaborated declarations together (parallel error collection)
 * 6. Map check results back to blocks via declaration indices
 *
 * @param source - The full source code
 * @returns Array of check results, one per block
 */
export function checkSourceBlocks(source: string): BlockCheckResult[] {
  // Phase 1: Group source into blocks
  const blocks = groupByIndentation(source);

  // Accumulate all previous declarations for pattern matching detection across blocks
  let allPreviousDeclarations: ParsedDeclaration[] = [];

  // Phase 2: Parse each block
  const parseResults: Array<{
    block: SourceBlock;
    blockIndex: number;
    parseSuccess: boolean;
    parseErrors: ParseError[];
    declarations: ParsedDeclaration[];
    sourceMaps: SourceMap[];
  }> = [];

  for (let blockIndex = 0; blockIndex < blocks.length; blockIndex++) {
    const block = blocks[blockIndex];

    // Skip comment blocks (don't attempt to parse)
    if (block.isComment) {
      parseResults.push({
        block,
        blockIndex,
        parseSuccess: true,
        parseErrors: [],
        declarations: [],
        sourceMaps: []
      });
      continue;
    }

    const blockSource = block.lines.join('\n');
    const parser = new Parser();

    try {
      // Pass all previous declarations so pattern matching detection works across blocks
      const declsWithSource = parser.parseDeclarationsWithSource(blockSource, allPreviousDeclarations);
      const newDeclarations = declsWithSource.map(d => d.decl);

      // Add these declarations to the accumulator for next block
      allPreviousDeclarations = [...allPreviousDeclarations, ...newDeclarations];

      // Adjust source map line numbers to be relative to the full file
      // Block line numbers start at startLine, but parser sees them starting at line 1
      const lineOffset = block.startLine - 1;
      const adjustedSourceMaps = declsWithSource.map(d => adjustSourceMapLines(d.sourceMap, lineOffset));

      parseResults.push({
        block,
        blockIndex,
        parseSuccess: true,
        parseErrors: [],
        declarations: newDeclarations,
        sourceMaps: adjustedSourceMaps
      });
    } catch (e) {
      if (e instanceof Error && 'errors' in e) {
        // Parse error with multiple errors
        // Adjust line numbers to be relative to the original source file
        const parseErrors = (e as any).errors as ParseError[];
        const adjustedErrors = parseErrors.map(err => ({
          ...err,
          line: err.line + block.startLine - 1
        }));
        parseResults.push({
          block,
          blockIndex,
          parseSuccess: false,
          parseErrors: adjustedErrors,
          declarations: [],
          sourceMaps: []
        });
      } else {
        // Unknown error
        parseResults.push({
          block,
          blockIndex,
          parseSuccess: false,
          parseErrors: [{
            name: 'ParseError',
            message: e instanceof Error ? e.message : String(e),
            line: block.startLine,
            col: 1
          }],
          declarations: [],
          sourceMaps: []
        });
      }
    }
  }

  // Phase 2.5: Name resolution - validate all symbols across all blocks
  interface NameResolutionResultWithBlock {
    blockIndex: number;
    success: boolean;
    errors: Array<{
      error: NameResolutionError;
      location: SourceRange | null;
    }>;
  }

  const nameResolutionResults: NameResolutionResultWithBlock[] = [];
  let globalSymbolContext = emptySymbolContext();

  for (const parseResult of parseResults) {
    if (!parseResult.parseSuccess || parseResult.declarations.length === 0) {
      // No declarations to validate (parse failed or empty block or comment)
      nameResolutionResults.push({
        blockIndex: parseResult.blockIndex,
        success: true,
        errors: []
      });
      continue;
    }

    // Validate this block's declarations against the global context
    const result = validateDeclarations(parseResult.declarations, globalSymbolContext);

    if (result.success) {
      // Update global context with new symbols
      globalSymbolContext = result.value;
      nameResolutionResults.push({
        blockIndex: parseResult.blockIndex,
        success: true,
        errors: []
      });
    } else {
      // Collect errors and resolve to source locations
      // NOTE: validateDeclarations already adds symbols to context even on error
      // So we need to rebuild the context ourselves to continue processing
      let updatedCtx = globalSymbolContext;
      for (const decl of parseResult.declarations) {
        if (decl.name) {
          updatedCtx = new Set([...updatedCtx, decl.name]);
        }
        if (decl.constructors) {
          for (const ctor of decl.constructors) {
            updatedCtx = new Set([...updatedCtx, ctor.name]);
          }
        }
      }
      globalSymbolContext = updatedCtx;

      // Resolve each error to a source location
      // Use the first sourceMap from this block (all declarations in a block share the same source context)
      const sourceMap = parseResult.sourceMaps[0] || new Map();
      const resolvedErrors = result.errors.map(error => ({
        error,
        location: resolveNameResolutionErrorLocation(error, sourceMap)
      }));

      nameResolutionResults.push({
        blockIndex: parseResult.blockIndex,
        success: false,
        errors: resolvedErrors
      });
    }
  }

  // Phase 3: Elaborate all successfully parsed declarations together
  const elaboratedDecls: ElaboratedDeclaration[] = [];

  for (const parseResult of parseResults) {
    if (!parseResult.parseSuccess || parseResult.declarations.length === 0) {
      continue;
    }

    for (let declIndex = 0; declIndex < parseResult.declarations.length; declIndex++) {
      const decl = parseResult.declarations[declIndex];
      const sourceMap = parseResult.sourceMaps[declIndex];
      const elabMap: ElabMap = new Map();

      let kernelType: TTKTerm | undefined;
      let kernelValue: TTKTerm | undefined;
      let kernelConstructors: Array<{ name: string; type: TTKTerm }> | undefined;

      try {
        // Elaborate type if present
        if (decl.type) {
          kernelType = elabToKernelWithMap(decl.type, elabMap);
        }

        // Elaborate value if present
        if (decl.value) {
          kernelValue = elabToKernelWithMap(decl.value, elabMap);
        }

        // Elaborate constructors if present (inductive)
        if (decl.constructors) {
          kernelConstructors = decl.constructors.map(ctor => ({
            name: ctor.name,
            type: elabToKernelWithMap(ctor.type, elabMap)
          }));
        }

        elaboratedDecls.push({
          blockIndex: parseResult.blockIndex,
          declIndex,
          decl,
          sourceMap,
          elabMap,
          kernelType,
          kernelValue,
          kernelConstructors
        });
      } catch (e) {
        // Elaboration error - treat as parse error for now
        // In practice, elaboration is mostly structural and shouldn't fail
        // (errors should be caught in type checking)
      }
    }
  }

  // Phase 4: Type check all elaborated declarations together
  interface CheckResultWithBlock {
    blockIndex: number;
    declIndex: number;
    sourceMap: SourceMap;
    elabMap: ElabMap;
    checkSuccess: boolean;
    checkErrors: CheckError[];
  }

  const checkResults: CheckResultWithBlock[] = elaboratedDecls.map(elab => {
    const { blockIndex, declIndex, decl, sourceMap, elabMap, kernelType, kernelValue, kernelConstructors } = elab;

    // Check based on declaration kind
    if (decl.kind === 'inductive' && kernelType && kernelConstructors) {
      const result = checkInductiveDeclaration(
        decl.name || 'anonymous',
        kernelType,
        kernelConstructors,
        []  // Empty context for now (TODO: build global context)
      );

      return {
        blockIndex,
        declIndex,
        sourceMap,
        elabMap,
        checkSuccess: result.success,
        checkErrors: result.success ? [] : result.errors
      };
    } else {
      // Term declaration (def, theorem, axiom, expr)
      const result = checkTermDeclaration(
        decl.name || 'anonymous',
        kernelType,
        kernelValue,
        []  // Empty context for now (TODO: build global context)
      );

      return {
        blockIndex,
        declIndex,
        sourceMap,
        elabMap,
        checkSuccess: result.success,
        checkErrors: result.success ? [] : result.errors
      };
    }
  });

  // Phase 5: Map results back to blocks
  const blockResults: BlockCheckResult[] = blocks.map((block, blockIndex) => {
    const parseResult = parseResults[blockIndex];

    // Comment blocks - no checking needed
    if (block.isComment) {
      return {
        block,
        blockIndex,
        parseSuccess: true,
        parseErrors: [],
        declarations: [],
        nameResolutionSuccess: true,
        nameResolutionErrors: [],
        checkSuccess: true,
        checkErrors: [],
        blockType: 'Comment'
      };
    }

    // Parse failed - return parse errors
    if (!parseResult.parseSuccess) {
      return {
        block,
        blockIndex,
        parseSuccess: false,
        parseErrors: parseResult.parseErrors,
        declarations: [],
        nameResolutionSuccess: true,  // N/A when parse fails
        nameResolutionErrors: [],
        checkSuccess: false,
        checkErrors: [],
        blockType: 'Unknown'
      };
    }

    // Parse succeeded but no declarations (empty block)
    if (parseResult.declarations.length === 0) {
      return {
        block,
        blockIndex,
        parseSuccess: true,
        parseErrors: [],
        declarations: [],
        nameResolutionSuccess: true,
        nameResolutionErrors: [],
        checkSuccess: true,
        checkErrors: [],
        blockType: 'Unknown'
      };
    }

    // Find check results for this block
    const blockCheckResults = checkResults.filter(r => r.blockIndex === blockIndex);

    // Get name resolution result for this block
    const nameResResult = nameResolutionResults.find(r => r.blockIndex === blockIndex);

    if (blockCheckResults.length === 0) {
      // No check results (shouldn't happen if parse succeeded)
      return {
        block,
        blockIndex,
        parseSuccess: true,
        parseErrors: [],
        declarations: parseResult.declarations,
        nameResolutionSuccess: nameResResult?.success ?? true,
        nameResolutionErrors: nameResResult?.errors ?? [],
        checkSuccess: true,
        checkErrors: [],
        blockType: 'Unknown'
      };
    }

    // Collect all check errors with their source locations
    const allCheckErrors: Array<{ error: CheckError; location: SourceRange | null }> = [];

    for (const checkResult of blockCheckResults) {
      for (const error of checkResult.checkErrors) {
        const location = resolveCheckErrorLocation(
          error,
          checkResult.elabMap,
          checkResult.sourceMap
        );
        allCheckErrors.push({ error, location });
      }
    }

    // Determine block type and name from first declaration
    const firstDecl = parseResult.declarations[0];
    const blockType: BlockCheckResult['blockType'] =
      firstDecl.kind === 'inductive' ? 'Inductive' : 'Term';
    const name = firstDecl.name;

    return {
      block,
      blockIndex,
      parseSuccess: true,
      parseErrors: [],
      declarations: parseResult.declarations,
      nameResolutionSuccess: nameResResult?.success ?? true,
      nameResolutionErrors: nameResResult?.errors ?? [],
      checkSuccess: allCheckErrors.length === 0,
      checkErrors: allCheckErrors,
      blockType,
      name
    };
  });

  return blockResults;
}

/**
 * Get a summary of check results.
 */
export interface CheckSummary {
  totalBlocks: number;
  commentBlocks: number;
  successfulBlocks: number;
  parseErrorBlocks: number;
  nameResolutionErrorBlocks: number;
  checkErrorBlocks: number;
  totalErrors: number;
}

export function summarizeCheckResults(results: BlockCheckResult[]): CheckSummary {
  return {
    totalBlocks: results.length,
    commentBlocks: results.filter(r => r.blockType === 'Comment').length,
    successfulBlocks: results.filter(r => r.parseSuccess && r.nameResolutionSuccess && r.checkSuccess).length,
    parseErrorBlocks: results.filter(r => !r.parseSuccess).length,
    nameResolutionErrorBlocks: results.filter(r => r.parseSuccess && !r.nameResolutionSuccess).length,
    checkErrorBlocks: results.filter(r => r.parseSuccess && r.nameResolutionSuccess && !r.checkSuccess).length,
    totalErrors: results.reduce((sum, r) =>
      sum + r.parseErrors.length + r.nameResolutionErrors.length + r.checkErrors.length, 0)
  };
}
