/**
 * Test utilities for the compiler.
 * Provides helper functions for testing the compilation pipeline.
 */

import { compileTTFromText, CompileResult, CompiledBlock, CompiledDeclaration, CompileOptions } from './compiler/compile';

/**
 * Block check result - a simplified view of compilation results for tests.
 * This provides a convenient interface for test assertions.
 */
export interface TestBlockResult {
  blockIndex: number;
  parseSuccess: boolean;
  parseErrors: Array<{ message: string; line: number; col: number }>;
  nameResolutionSuccess: boolean;
  nameResolutionErrors: Array<{ symbolName: string; message: string }>;
  checkSuccess: boolean;
  checkErrors: Array<{ message: string }>;
  blockType: 'Inductive' | 'Term' | 'Comment' | 'Unknown';
  name: string | undefined;
  declarations: CompiledDeclaration[];
  isComment: boolean;
  /** For inductive types: index positions */
  indexPositions?: number[];
}

/**
 * Compile source code and return test-friendly results.
 * This is a wrapper around compileTTFromText that provides a simpler interface.
 */
export function compileSource(source: string, options?: CompileOptions): TestBlockResult[] {
  const result = compileTTFromText(source, options);
  return result.blocks.map(block => blockToTestResult(block));
}

/**
 * Convert a CompiledBlock to a TestBlockResult.
 */
function blockToTestResult(block: CompiledBlock): TestBlockResult {
  // Determine block type
  let blockType: 'Inductive' | 'Term' | 'Comment' | 'Unknown' = 'Unknown';
  if (block.isComment) {
    blockType = 'Comment';
  } else if (block.declarations.length > 0) {
    const firstDecl = block.declarations[0];
    if (firstDecl.kind === 'inductive') {
      blockType = 'Inductive';
    } else if (firstDecl.kind === 'term') {
      blockType = 'Term';
    }
  }

  // Aggregate check success and errors from all declarations
  // If parse failed, check also fails
  // If parse succeeded and has declarations, check succeeds if all declarations succeed
  // If parse succeeded but no declarations (empty block or comment), check succeeds
  const checkSuccess = block.parseSuccess && (
    block.declarations.length === 0 ||
    block.declarations.every(d => d.checkSuccess)
  );

  const checkErrors = block.declarations.flatMap(d =>
    d.checkErrors.map(e => ({ message: e.message }))
  );

  // Get name from first declaration
  const name = block.declarations[0]?.name;

  // Name resolution errors already have symbolName and message
  const nameResolutionErrors = block.nameResolutionErrors.map(err => ({
    symbolName: err.symbolName,
    message: err.message
  }));

  // Get index positions from first inductive declaration
  const indexPositions = block.declarations[0]?.indexPositions;

  return {
    blockIndex: block.blockIndex,
    parseSuccess: block.parseSuccess,
    parseErrors: block.parseErrors.map(e => ({
      message: e.message,
      line: e.line,
      col: e.col
    })),
    nameResolutionSuccess: block.nameResolutionSuccess,
    nameResolutionErrors,
    checkSuccess,
    checkErrors,
    blockType,
    name,
    declarations: block.declarations,
    isComment: block.isComment,
    indexPositions
  };
}

/**
 * Extract symbol name from an error message like "Undefined symbol: Foo"
 */
function extractSymbolName(message: string): string {
  const match = message.match(/Undefined symbol[:\s]+['"]?(\w+)['"]?/i);
  return match ? match[1] : 'unknown';
}

/**
 * Summary of compile results.
 */
export interface CompileSummary {
  totalBlocks: number;
  commentBlocks: number;
  successfulBlocks: number;
  parseErrorBlocks: number;
  nameResolutionErrorBlocks: number;
  checkErrorBlocks: number;
  totalErrors: number;
}

/**
 * Summarize compile results.
 */
export function summarizeResults(results: TestBlockResult[]): CompileSummary {
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
