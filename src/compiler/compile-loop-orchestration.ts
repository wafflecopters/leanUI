import { groupByIndentation } from '../parser/indentation-grouper';
import { emptySymbolContext, type SymbolContext } from '../types/name-resolution';
import { setConstructorParamNames, type ConstructorParamNames } from './elab';
import {
  computeRecheckSet,
  extractBlockDepInfo,
  type IncrementalCache,
} from './incremental';
import type { TTKTerm } from './kernel';
import { createDefinitionsMap, type DefinitionsMap } from './term';
import { compileOneBlock } from './compile-block-processing';
import { applyImplAnnotationsForBlock } from './compile-impl-annotations';
import {
  applyBlockContributions,
  computeBlockContributions,
} from './compile-incremental-state';
import type { ElaborateTacticBlockFn } from './compile-term-simple-value';
import type { CompileOptions, CompileResult, ParseResult } from './compile-types';
import type { RecheckZonkedTermFn } from './compile-zonk-recheck';

export interface CompileLoopServices {
  assumeK: boolean;
  elaborateTacticBlock: ElaborateTacticBlockFn;
  recheckZonkedTerm: RecheckZonkedTermFn;
  options?: CompileOptions;
}

interface CompileLoopState {
  definitions: DefinitionsMap;
  constructorParamNames: ConstructorParamNames;
  symbolContext: SymbolContext;
  compiledBlocks: CompileResult['blocks'];
  totalCheckErrors: number;
  totalNameErrors: number;
}

function createInitialLoopState(): CompileLoopState {
  return {
    definitions: createDefinitionsMap(),
    constructorParamNames: new Map(),
    symbolContext: emptySymbolContext(),
    compiledBlocks: [],
    totalCheckErrors: 0,
    totalNameErrors: 0,
  };
}

function appendCompiledBlock(
  state: CompileLoopState,
  compiledBlock: CompileResult['blocks'][number],
  checkErrorCount: number,
  nameErrorCount: number,
): void {
  state.compiledBlocks.push(compiledBlock);
  state.totalCheckErrors += checkErrorCount;
  state.totalNameErrors += nameErrorCount;
}

function finishCompileResult(
  parseResult: ParseResult,
  state: CompileLoopState,
): CompileResult {
  return {
    success:
      parseResult.totalErrors === 0
      && state.totalNameErrors === 0
      && state.totalCheckErrors === 0,
    blocks: state.compiledBlocks,
    totalParseErrors: parseResult.totalErrors,
    totalNameErrors: state.totalNameErrors,
    totalCheckErrors: state.totalCheckErrors,
    definitions: state.definitions,
  };
}

function compileFreshBlock(
  state: CompileLoopState,
  block: ParseResult['blocks'][number],
  blockIndex: number,
  services: CompileLoopServices,
): ReturnType<typeof compileOneBlock> {
  return compileOneBlock(
    block,
    blockIndex,
    state.definitions,
    state.symbolContext,
    state.constructorParamNames,
    services.assumeK,
    services.elaborateTacticBlock,
    services.recheckZonkedTerm,
    services.options,
  );
}

function applyBlockResult(
  state: CompileLoopState,
  result: ReturnType<typeof compileOneBlock>,
): void {
  appendCompiledBlock(
    state,
    result.compiled,
    result.checkErrorCount,
    result.nameErrorCount,
  );
  state.definitions = result.newDefinitions;
  state.symbolContext = result.newSymbolContext;
  state.constructorParamNames = result.newConstructorParamNames;
  applyImplAnnotationsForBlock(result.compiled, state.definitions);
}

export function reuseLastIncrementalResult(
  source: string,
  cache: IncrementalCache,
): CompileResult | undefined {
  const sourceBlocks = groupByIndentation(source);
  if (!cache.lastResult || sourceBlocks.length !== cache.blocks.length) {
    return undefined;
  }

  for (let i = 0; i < sourceBlocks.length; i++) {
    const sourceText = sourceBlocks[i].lines.join('\n');
    if (!cache.blocks[i] || cache.blocks[i]!.sourceText !== sourceText) {
      return undefined;
    }
  }

  return cache.lastResult;
}

export function collectChangedBlockIndices(
  parseResult: ParseResult,
  cache: IncrementalCache,
): Set<number> {
  const changedIndices = new Set<number>();
  for (let i = 0; i < parseResult.blocks.length; i++) {
    const block = parseResult.blocks[i];
    const sourceText = block.sourceLines.join('\n');
    const cached = cache.blocks[i];
    if (!cached || cached.sourceText !== sourceText) {
      changedIndices.add(i);
    }
  }
  return changedIndices;
}

export function compileParsedBlocks(
  parseResult: ParseResult,
  services: CompileLoopServices,
): CompileResult {
  const state = createInitialLoopState();

  for (let blockIndex = 0; blockIndex < parseResult.blocks.length; blockIndex++) {
    const block = parseResult.blocks[blockIndex];
    const result = compileFreshBlock(state, block, blockIndex, services);
    applyBlockResult(state, result);
  }

  return finishCompileResult(parseResult, state);
}

export function compileParsedBlocksIncrementally(
  parseResult: ParseResult,
  cache: IncrementalCache,
  services: CompileLoopServices,
): CompileResult {
  const changedIndices = collectChangedBlockIndices(parseResult, cache);
  const blockInfos = parseResult.blocks.map((block, i) => extractBlockDepInfo(block, i));
  const recheckSet = computeRecheckSet(blockInfos, changedIndices);
  const state = createInitialLoopState();

  for (let blockIndex = 0; blockIndex < parseResult.blocks.length; blockIndex++) {
    const block = parseResult.blocks[blockIndex];
    const cached = cache.blocks[blockIndex];

    if (!recheckSet.has(blockIndex) && cached) {
      appendCompiledBlock(
        state,
        cached.compiledBlock,
        cached.checkErrorCount,
        cached.nameErrorCount,
      );

      const applied = applyBlockContributions(
        state.definitions,
        state.symbolContext,
        state.constructorParamNames,
        cached.contributions,
      );
      state.definitions = applied.definitions;
      state.symbolContext = applied.symbolContext;
      state.constructorParamNames = applied.constructorParamNames;

      setConstructorParamNames(state.constructorParamNames);
      applyImplAnnotationsForBlock(cached.compiledBlock, state.definitions);
      continue;
    }

    setConstructorParamNames(state.constructorParamNames);

    const beforeDefs = state.definitions;
    const beforeSymbols = state.symbolContext;
    const beforeCtorParams = state.constructorParamNames;

    const result = compileFreshBlock(state, block, blockIndex, services);
    applyBlockResult(state, result);

    const contributions = computeBlockContributions(
      beforeDefs,
      state.definitions,
      beforeSymbols,
      state.symbolContext,
      beforeCtorParams,
      state.constructorParamNames,
    );

    cache.blocks[blockIndex] = {
      sourceText: block.sourceLines.join('\n'),
      compiledBlock: result.compiled,
      contributions,
      checkErrorCount: result.checkErrorCount,
      nameErrorCount: result.nameErrorCount,
    };
  }

  cache.blocks.length = parseResult.blocks.length;
  const result = finishCompileResult(parseResult, state);
  cache.lastResult = result;
  return result;
}
