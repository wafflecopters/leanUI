import type { SourceMap } from '../types/source-position';

/**
 * Adjust a sourceMap's line numbers by adding a block offset.
 * This converts block-relative positions to file-absolute positions.
 */
export function adjustSourceMapToAbsolute(
  sourceMap: SourceMap,
  blockStartLine: number,
  posOffset: number
): SourceMap {
  if (blockStartLine === 1 && posOffset === 0) {
    return sourceMap;
  }

  const lineOffset = blockStartLine - 1;
  const adjusted = new Map<
    string,
    {
      start: { line: number; col: number; pos: number };
      end: { line: number; col: number; pos: number };
    }
  >();

  for (const [key, range] of sourceMap) {
    adjusted.set(key, {
      start: {
        line: range.start.line + lineOffset,
        col: range.start.col,
        pos: range.start.pos + posOffset,
      },
      end: {
        line: range.end.line + lineOffset,
        col: range.end.col,
        pos: range.end.pos + posOffset,
      },
    });
  }

  return adjusted;
}

/**
 * Compute the first code line (1-based) in a block, skipping leading comment
 * and directive lines.
 */
export function computeCodeStartLine(sourceLines: string[], startLine: number): number {
  for (let i = 0; i < sourceLines.length; i++) {
    const trimmed = sourceLines[i].trim();
    if (trimmed.length === 0) continue;
    if (trimmed.startsWith('--')) continue;
    if (trimmed.startsWith('/-')) continue;
    if (trimmed.startsWith('{-')) continue;
    if (trimmed.startsWith('@')) continue;
    return startLine + i;
  }
  return startLine;
}

/**
 * Compute the character offset of a 1-based line number in a source string.
 * Returns the index of the first character of the given line.
 */
export function lineToCharOffset(source: string, line: number): number {
  let offset = 0;
  for (let i = 1; i < line; i++) {
    const nl = source.indexOf('\n', offset);
    if (nl < 0) return source.length;
    offset = nl + 1;
  }
  return offset;
}

/**
 * Serialize a path array to the format used by elabMap/sourceMap lookups.
 */
export function serializePathForLookup(path: (string | number)[]): string {
  return path
    .map(seg => (typeof seg === 'number' ? `[${seg}]` : `.${seg}`))
    .join('')
    .replace(/^\./, '');
}
