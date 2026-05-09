import type { CompileResult, HoleLocation } from '../compiler/compile';
import type { SourceRange } from '../types/source-position';
import { mapErrorPathToSourceRange } from './textEditorModel';

export interface TextEditorMarker {
  severity: 'error' | 'warning';
  message: string;
  startLineNumber: number;
  startColumn: number;
  endLineNumber: number;
  endColumn: number;
  source: string;
}

interface MarkerContext {
  getLineContent: (lineNumber: number) => string;
}

function createBlockFallbackMarker(
  firstLine: number,
  message: string,
  severity: 'error' | 'warning',
  source: string,
  context: MarkerContext
): TextEditorMarker {
  return {
    severity,
    message,
    startLineNumber: firstLine,
    startColumn: 1,
    endLineNumber: firstLine,
    endColumn: context.getLineContent(firstLine).length + 1,
    source,
  };
}

function createRangeMarker(
  sourceRange: SourceRange,
  message: string,
  severity: 'error' | 'warning',
  source: string
): TextEditorMarker {
  return {
    severity,
    message,
    startLineNumber: sourceRange.start.line,
    startColumn: sourceRange.start.col,
    endLineNumber: sourceRange.end.line,
    endColumn: sourceRange.end.col,
    source,
  };
}

export function buildCompileMarkers(
  compileResult: CompileResult,
  holeLocations: HoleLocation[],
  context: MarkerContext
): TextEditorMarker[] {
  const markers: TextEditorMarker[] = [];

  for (const block of compileResult.blocks) {
    for (const error of block.parseErrors) {
      const lineContent = context.getLineContent(error.line);
      const endCol = Math.max(error.col + 1, lineContent.length + 1);

      markers.push({
        severity: 'error',
        message: (error.message || 'Parse error').replace(/^Parse error at line \d+, col \d+: /, ''),
        startLineNumber: error.line,
        startColumn: error.col,
        endLineNumber: error.line,
        endColumn: endCol,
        source: 'TT Parser',
      });
    }

    for (const err of block.nameResolutionErrors) {
      let sourceRange: SourceRange | null = null;

      if (err.path && err.declarationIndex !== undefined) {
        const decl = block.declarations[err.declarationIndex];
        if (decl?.sourceMap) {
          sourceRange = decl.sourceMap.get(err.path) ?? null;
        }
      }

      if (sourceRange) {
        markers.push(createRangeMarker(sourceRange, err.message, 'error', 'TT Name Resolution'));
      } else {
        markers.push(
          createBlockFallbackMarker(
            block.codeStartLine,
            err.message,
            'error',
            'TT Name Resolution',
            context
          )
        );
      }
    }

    for (const decl of block.declarations) {
      if (decl.isWithAuxiliary) continue;

      for (const err of decl.checkErrors ?? []) {
        const sourceRange = mapErrorPathToSourceRange(
          err.env.indexPath,
          decl.elabMap,
          decl.sourceMap
        );

        if (sourceRange) {
          markers.push(
            createRangeMarker(
              sourceRange,
              err.message,
              err.severity === 'warning' ? 'warning' : 'error',
              'TT Type Checker'
            )
          );
        } else {
          markers.push(
            createBlockFallbackMarker(
              block.codeStartLine,
              err.message,
              err.severity === 'warning' ? 'warning' : 'error',
              'TT Type Checker',
              context
            )
          );
        }
      }

      for (const err of decl.withClauseErrors ?? []) {
        const sourceRange = decl.withClauseElabMap && decl.sourceMap
          ? mapErrorPathToSourceRange(err.env.indexPath, decl.withClauseElabMap, decl.sourceMap)
          : null;

        if (sourceRange) {
          markers.push(createRangeMarker(sourceRange, err.message, 'error', 'TT Type Checker'));
        } else {
          markers.push(
            createBlockFallbackMarker(
              block.codeStartLine,
              err.message,
              'error',
              'TT Type Checker',
              context
            )
          );
        }
      }
    }
  }

  for (const hole of holeLocations) {
    markers.push({
      severity: 'warning',
      message: 'Holes are unsound.',
      startLineNumber: hole.line,
      startColumn: hole.column,
      endLineNumber: hole.line,
      endColumn: hole.endColumn,
      source: 'TT Holes',
    });
  }

  return markers;
}
