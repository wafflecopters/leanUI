import { groupByIndentation } from '../parser/indentation-grouper';
import {
  DEFAULT_OPERATORS,
  OperatorInfo,
  ParsedDeclaration,
  ParseError,
  Parser,
} from '../parser/parser';
import type { SourceMap } from '../types/source-position';
import type { ParsedBlock, ParseResult } from './compile';
import { lineToCharOffset } from './compile-source-utils';

export function parseTTSource(source: string): ParseResult {
  const sourceBlocks = groupByIndentation(source);
  const parsedBlocks: ParsedBlock[] = [];
  let totalErrors = 0;

  let allPreviousDeclarations: ParsedDeclaration[] = [];
  let customOperators: Record<string, OperatorInfo> = { ...DEFAULT_OPERATORS };

  for (const block of sourceBlocks) {
    const posOffset = lineToCharOffset(source, block.startLine);

    if (block.isComment) {
      parsedBlocks.push({
        kind: 'comment',
        sourceLines: block.lines,
        startLine: block.startLine,
        posOffset,
      });
      continue;
    }

    const blockSource = block.lines.join('\n');
    const parser = new Parser(customOperators);

    let declarations: ParsedDeclaration[] = [];
    let sourceMaps: SourceMap[] = [];

    try {
      const declsWithSource = parser.parseDeclarationsWithSource(blockSource, allPreviousDeclarations);
      declarations = declsWithSource.map(d => d.decl);
      sourceMaps = declsWithSource.map(d => d.sourceMap);
      allPreviousDeclarations = [...allPreviousDeclarations, ...declarations];
    } catch (e) {
      const parseErrors = normalizeParseErrors(e, block.startLine);
      totalErrors += parseErrors.length;
      parsedBlocks.push({
        kind: 'error',
        errors: parseErrors,
        sourceLines: block.lines,
        startLine: block.startLine,
        posOffset,
      });
      continue;
    }

    customOperators = extendOperatorsWithDeclarations(customOperators, declarations);

    parsedBlocks.push({
      kind: 'declarations',
      declarations,
      sourceMaps,
      sourceLines: block.lines,
      startLine: block.startLine,
      posOffset,
    });
  }

  return { blocks: parsedBlocks, totalErrors };
}

function normalizeParseErrors(error: unknown, blockStartLine: number): ParseError[] {
  if (error instanceof Error && 'errors' in error) {
    return ((error as { errors: ParseError[] }).errors).map(err => ({
      name: err.name,
      message: err.message,
      line: err.line + blockStartLine - 1,
      col: err.col,
    }));
  }

  return [{
    name: 'ParseError',
    message: error instanceof Error ? error.message : String(error),
    line: blockStartLine,
    col: 1,
  }];
}

function extendOperatorsWithDeclarations(
  operators: Record<string, OperatorInfo>,
  declarations: ParsedDeclaration[]
): Record<string, OperatorInfo> {
  let nextOperators = operators;

  for (const decl of declarations) {
    if (decl.kind !== 'notation' || !decl.symbol || !decl.target) {
      continue;
    }

    nextOperators = { ...nextOperators };
    nextOperators[decl.symbol] = {
      symbol: decl.symbol,
      precedence: decl.precedence ?? 50,
      associativity:
        decl.notationKind === 'infixl'
          ? 'left'
          : decl.notationKind === 'infixr'
            ? 'right'
            : 'none',
      constName: decl.target,
      binding: decl.notationBinding,
    };
  }

  return nextOperators;
}
