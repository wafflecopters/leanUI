/**
 * Hook for querying type information at the cursor position or selection.
 *
 * This hook:
 * 1. Listens to Monaco editor cursor/selection changes
 * 2. Finds which block contains the cursor
 * 3. Queries the type of the expression at that position
 * 4. Returns formatted information for UI display
 */

import { useState, useCallback, useEffect, useMemo } from 'react';
import type { editor as MonacoEditor } from 'monaco-editor';
import { BlockCheckResult, BlockTypeQueryData } from '../parser/block-checker';
import { SourcePos, SourceRange, SourceMap, IndexPath, deserializeIndexPath, serializeIndexPath } from '../types/source-position';
import { queryTypeAtPosition, queryTypeForSelection, formatTypeQueryResult } from '../types/tt-source-query';
import { prettyPrint } from '../types/tt-kernel';

/**
 * Information about the type at the current selection.
 */
export interface SelectionTypeInfo {
  // Whether we have valid type information
  hasInfo: boolean;

  // The selected code text (or expression at cursor)
  selectedCode: string;

  // The type of the selected expression
  typeString: string;

  // The full formatted display (term : type)
  formattedDisplay: string;

  // Source range of the selected expression (for highlighting)
  sourceRange?: SourceRange;

  // Error message if type query failed
  error?: string;
}

const NO_INFO: SelectionTypeInfo = {
  hasInfo: false,
  selectedCode: '',
  typeString: '',
  formattedDisplay: ''
};

/**
 * Create a source map adjusted to be relative to the value term.
 *
 * The parser stores paths like `value.clauses[0].rhs.body...` but when querying
 * the kernelValue term directly, we need paths relative to the value
 * (e.g., `clauses[0].rhs.body...`).
 *
 * @param sourceMap - The original source map from parsing
 * @param prefix - The prefix to strip (e.g., 'value')
 * @returns A new source map with adjusted paths
 */
function createValueRelativeSourceMap(sourceMap: SourceMap, prefix: string): SourceMap {
  const adjustedMap: SourceMap = new Map();
  const prefixWithDot = prefix + '.';

  for (const [pathKey, range] of sourceMap) {
    if (pathKey.startsWith(prefixWithDot)) {
      // Strip the prefix and add to new map
      const relativePath = pathKey.slice(prefixWithDot.length);
      adjustedMap.set(relativePath, range);
    } else if (pathKey === prefix) {
      // The root of the value term
      adjustedMap.set('', range);
    }
    // Also keep entries without the prefix (like 'type', 'domain', etc.)
    // as they might be relevant for type declarations
    if (!pathKey.startsWith('value')) {
      adjustedMap.set(pathKey, range);
    }
  }

  return adjustedMap;
}

/**
 * Find which block contains a given line number.
 */
function findBlockForLine(
  lineNumber: number,
  blockResults: BlockCheckResult[]
): BlockCheckResult | null {
  for (const block of blockResults) {
    const endLine = block.block.startLine + block.block.lines.length - 1;
    if (lineNumber >= block.block.startLine && lineNumber <= endLine) {
      return block;
    }
  }
  return null;
}

/**
 * Hook to track cursor position and query type information.
 *
 * @param editor - Monaco editor instance
 * @param blockResults - Results from block checking
 * @param sourceCode - The full source code
 * @returns Selection type information
 */
export function useSelectionTypeInfo(
  editor: MonacoEditor.IStandaloneCodeEditor | null,
  blockResults: BlockCheckResult[],
  sourceCode: string
): SelectionTypeInfo {
  const [cursorPosition, setCursorPosition] = useState<{ lineNumber: number; column: number } | null>(null);
  const [selection, setSelection] = useState<{ startLineNumber: number; startColumn: number; endLineNumber: number; endColumn: number } | null>(null);

  // Subscribe to cursor position changes
  useEffect(() => {
    if (!editor) return;

    const disposable = editor.onDidChangeCursorPosition((e) => {
      setCursorPosition({
        lineNumber: e.position.lineNumber,
        column: e.position.column
      });
    });

    // Also track selection
    const selectionDisposable = editor.onDidChangeCursorSelection((e) => {
      const sel = e.selection;
      // Check if there's an actual selection (not just cursor)
      if (sel.startLineNumber !== sel.endLineNumber ||
          sel.startColumn !== sel.endColumn) {
        setSelection({
          startLineNumber: sel.startLineNumber,
          startColumn: sel.startColumn,
          endLineNumber: sel.endLineNumber,
          endColumn: sel.endColumn
        });
      } else {
        setSelection(null);
      }
    });

    // Initialize with current position
    const pos = editor.getPosition();
    if (pos) {
      setCursorPosition({ lineNumber: pos.lineNumber, column: pos.column });
    }

    return () => {
      disposable.dispose();
      selectionDisposable.dispose();
    };
  }, [editor]);

  // Compute type info based on cursor position
  const typeInfo = useMemo((): SelectionTypeInfo => {
    if (!cursorPosition) {
      return NO_INFO;
    }

    // Find which block contains this cursor
    const block = findBlockForLine(cursorPosition.lineNumber, blockResults);
    if (!block) {
      return NO_INFO;
    }

    // Need type query data to proceed
    const queryData = block.typeQueryData;
    if (!queryData) {
      return NO_INFO;
    }

    // Decide which term to query and create the appropriate source map
    // For value terms, paths are stored as "value.clauses[0].rhs..." but we need
    // them relative to the value term itself
    let term = queryData.kernelValue;
    let sourceMapToUse = queryData.sourceMap;

    if (term) {
      // When querying the value, adjust paths to be relative to 'value'
      sourceMapToUse = createValueRelativeSourceMap(queryData.sourceMap, 'value');
    } else {
      term = queryData.kernelType;
      if (term) {
        // When querying the type, adjust paths to be relative to 'type'
        sourceMapToUse = createValueRelativeSourceMap(queryData.sourceMap, 'type');
      }
    }

    if (!term) {
      return NO_INFO;
    }

    // Query based on whether we have a selection or just a cursor position
    // Pass the kernel type as expectedType so pattern bindings can be computed correctly
    // Pass the definition name so recursive references can be resolved
    // Pass the elaboration context so unification results are applied to pattern types
    const expectedType = queryData.kernelType;
    const definitionName = block.name;
    const elabContext = queryData.clauseResults ? {
      clauseResults: queryData.clauseResults,
      functionType: queryData.kernelType
    } : undefined;

    let result;
    if (selection &&
        selection.startLineNumber >= block.block.startLine &&
        selection.endLineNumber <= block.block.startLine + block.block.lines.length - 1) {
      // User has selected a range - find the smallest containing expression
      const selectionRange: SourceRange = {
        start: { line: selection.startLineNumber, col: selection.startColumn, pos: 0 },
        end: { line: selection.endLineNumber, col: selection.endColumn, pos: 0 }
      };
      result = queryTypeForSelection(selectionRange, sourceMapToUse, term, queryData.context, expectedType, definitionName, elabContext);
    } else {
      // Just a cursor position - find the smallest expression at this point
      const pos: SourcePos = {
        line: cursorPosition.lineNumber,
        col: cursorPosition.column,
        pos: 0  // We don't have character offset readily available
      };
      result = queryTypeAtPosition(pos, sourceMapToUse, term, queryData.context, expectedType, definitionName, sourceCode, elabContext);
    }

    if (!result.success) {
      // If cursor is at a position with no AST node, show block-level info
      if (queryData.kernelType) {
        const typeStr = prettyPrint(queryData.kernelType, queryData.context.map(b => b.name));
        return {
          hasInfo: true,
          selectedCode: block.name || 'expression',
          typeString: typeStr,
          formattedDisplay: `${block.name || 'expression'} : ${typeStr}`,
          error: result.error
        };
      }
      return {
        hasInfo: false,
        selectedCode: '',
        typeString: '',
        formattedDisplay: '',
        error: result.error
      };
    }

    // Format the result
    const names = result.context.map(b => b.name);
    const termStr = prettyPrint(result.term, names);
    const typeStr = prettyPrint(result.type, names);

    // Get the selected code from source if we have a range
    let selectedCode = termStr;
    if (result.sourceRange) {
      try {
        const lines = sourceCode.split('\n');
        if (result.sourceRange.start.line === result.sourceRange.end.line) {
          // Single line
          const line = lines[result.sourceRange.start.line - 1] || '';
          selectedCode = line.slice(result.sourceRange.start.col - 1, result.sourceRange.end.col - 1);
          // For lambdas, ensure we show the backslash (nested lambdas don't include it in source range)
          const isLambda = result.term.tag === 'Binder' && result.term.binderKind.tag === 'BLam';
          if (isLambda && !selectedCode.startsWith('\\')) {
            selectedCode = '\\ ' + selectedCode;
          }
        }
        // Multi-line - already using termStr
      } catch {
        // Already using termStr
      }
    }

    return {
      hasInfo: true,
      selectedCode: selectedCode || termStr,
      typeString: typeStr,
      formattedDisplay: `${selectedCode || termStr} : ${typeStr}`,
      sourceRange: result.sourceRange
    };
  }, [cursorPosition, selection, blockResults, sourceCode]);

  return typeInfo;
}
