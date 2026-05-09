import type { CompileResult, CompiledDeclaration } from '../compiler/compile';
import { getTypeAtCursor, getTypeAtSelection, type CursorQueryResult } from '../compiler/type-info';
import { serializeIndexPath, type ElabMap, type IndexPath, type SourceMap, type SourceRange } from '../types/source-position';

export interface PresetLike {
  name: string;
  code: string;
}

export interface CompiledDeclEntry {
  decl: CompiledDeclaration;
  blockSource: string;
  blockStartLine: number;
}

export interface EditorCursorInfo {
  lineNumber: number;
  column: number;
  selStartLine?: number;
  selStartCol?: number;
  selEndLine?: number;
  selEndCol?: number;
}

export type CursorInfoAtPosition = CursorQueryResult & { expression?: string };

export function slugifyPresetName(name: string): string {
  return name.toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/(^-|-$)/g, '');
}

export function resolveInitialEditorCode(
  presets: PresetLike[],
  presetParam: string | null | undefined
): string {
  if (presetParam) {
    const preset = presets.find(candidate => slugifyPresetName(candidate.name) === presetParam);
    if (preset) {
      return preset.code;
    }
  }

  return presets[0]?.code ?? '';
}

export function findRangeByWalkingPath(
  path: IndexPath,
  sourceMap: SourceMap,
  mapper?: (pathStr: string) => string | undefined
): SourceRange | null {
  let currentPath = path;
  while (currentPath.length >= 0) {
    const pathStr = serializeIndexPath(currentPath);
    const lookupKey = mapper ? mapper(pathStr) : pathStr;
    if (lookupKey) {
      const range = sourceMap.get(lookupKey);
      if (range) return range;
    }
    if (currentPath.length === 0) break;
    currentPath = currentPath.slice(0, -1);
  }
  return null;
}

export function findRangeViaElabMapWithSuffix(
  errorPath: IndexPath,
  elabMap: ElabMap,
  sourceMap: SourceMap
): SourceRange | null {
  for (let prefixLen = errorPath.length; prefixLen >= 0; prefixLen--) {
    const prefix = errorPath.slice(0, prefixLen);
    const suffix = errorPath.slice(prefixLen);
    const prefixStr = serializeIndexPath(prefix);
    const mappedPrefix = elabMap.get(prefixStr);
    if (mappedPrefix !== undefined) {
      const suffixStr = serializeIndexPath(suffix);
      const fullSurfacePath = mappedPrefix + (suffixStr ? '.' + suffixStr : '');
      const range = sourceMap.get(fullSurfacePath);
      if (range) return range;
    }
  }
  return null;
}

export function mapErrorPathToSourceRange(
  errorPath: IndexPath,
  elabMap: ElabMap | undefined,
  sourceMap: SourceMap | undefined
): SourceRange | null {
  if (!sourceMap) return null;

  if (elabMap) {
    const mappedRange = findRangeViaElabMapWithSuffix(errorPath, elabMap, sourceMap);
    if (mappedRange) return mappedRange;

    const fallbackRange = findRangeByWalkingPath(errorPath, sourceMap, path => elabMap.get(path));
    if (fallbackRange) return fallbackRange;
  }

  return findRangeByWalkingPath(errorPath, sourceMap);
}

export function collectCompiledDeclEntries(
  compileResult: CompileResult,
  includeDeclarations: boolean
): CompiledDeclEntry[] {
  if (!includeDeclarations) {
    return [];
  }

  const result: CompiledDeclEntry[] = [];
  for (const block of compileResult.blocks) {
    const blockSource = block.sourceLines.join('\n');
    for (const decl of block.declarations) {
      if (!decl.isWithAuxiliary) {
        result.push({ decl, blockSource, blockStartLine: block.startLine });
      }
    }
  }
  return result;
}

export function replaceDeclarationNameInSource(
  code: string,
  entry: CompiledDeclEntry | undefined,
  newName: string
): string {
  if (!entry) return code;

  const nameRange = entry.decl.sourceMap?.get('name');
  if (!nameRange) return code;

  const absLine = entry.blockStartLine + nameRange.start.line - 1;
  const lines = code.split('\n');
  if (absLine < 0 || absLine >= lines.length) return code;

  const line = lines[absLine];
  lines[absLine] =
    line.slice(0, nameRange.start.col - 1) +
    newName +
    line.slice(nameRange.end.col - 1);

  return lines.join('\n');
}

export function collectAllCompiledDeclarations(
  compileResult: CompileResult,
  includeDeclarations: boolean
): CompiledDeclaration[] {
  if (!includeDeclarations) {
    return [];
  }
  return compileResult.blocks.flatMap(block => block.declarations);
}

function toFileOffset(lines: string[], line: number, col: number): number {
  let offset = 0;
  for (let i = 0; i < line - 1; i++) {
    offset += lines[i].length + 1;
  }
  offset += col - 1;
  return offset;
}

function extractSourceExpression(
  codeLines: string[],
  result: Extract<CursorQueryResult, { kind: 'term' }>
): string {
  if (!result.info.sourceRange) {
    return '';
  }

  const { start, end } = result.info.sourceRange;
  if (start.line === end.line) {
    return codeLines[start.line - 1].substring(start.col - 1, end.col - 1);
  }

  const parts: string[] = [];
  parts.push(codeLines[start.line - 1].substring(start.col - 1));
  for (let i = start.line; i < end.line - 1; i++) {
    parts.push(codeLines[i]);
  }
  parts.push(codeLines[end.line - 1].substring(0, end.col - 1));
  return parts.join(' ');
}

function findTargetDeclarationAtLine(
  compileResult: CompileResult,
  cursorLine: number
): CompiledDeclaration | null {
  for (const block of compileResult.blocks) {
    const blockEndLine = block.startLine + block.sourceLines.length - 1;
    if (cursorLine < block.startLine || cursorLine > blockEndLine) {
      continue;
    }

    let targetDecl: CompiledDeclaration | undefined;
    for (const decl of block.declarations) {
      if (!decl.sourceMap || (!decl.typeInfoMap && !decl.tacticInfoTree)) {
        continue;
      }

      targetDecl = decl;
      for (const [, range] of decl.sourceMap) {
        if (range.start.line <= cursorLine && cursorLine <= range.end.line) {
          targetDecl = decl;
          break;
        }
      }
    }

    if (targetDecl?.sourceMap && (targetDecl.typeInfoMap || targetDecl.tacticInfoTree)) {
      return targetDecl;
    }
  }

  return null;
}

export function getTypeInfoAtCursor(
  cursorInfo: EditorCursorInfo | null,
  compileResult: CompileResult,
  code: string
): CursorInfoAtPosition | undefined {
  if (!cursorInfo) return undefined;

  const lines = code.split('\n');
  const target = findTargetDeclarationAtLine(compileResult, cursorInfo.lineNumber);
  if (!target) return undefined;

  const declaration = target;
  const hasSelection =
    cursorInfo.selStartLine !== undefined &&
    cursorInfo.selEndLine !== undefined &&
    (cursorInfo.selStartLine !== cursorInfo.selEndLine ||
      cursorInfo.selStartCol !== cursorInfo.selEndCol);

  let cursorQueryResult: CursorQueryResult | undefined;

  try {
    if (hasSelection) {
      const startOffset = toFileOffset(lines, cursorInfo.selStartLine!, cursorInfo.selStartCol!);
      const endOffset = toFileOffset(lines, cursorInfo.selEndLine!, cursorInfo.selEndCol!);
      cursorQueryResult = getTypeAtSelection(
        startOffset,
        endOffset,
        declaration.sourceMap!,
        declaration.elabMap,
        declaration.typeInfoMap,
        declaration.tacticInfoTree,
        compileResult.definitions,
        code
      );
    }

    if (!cursorQueryResult) {
      const cursorOffset = toFileOffset(lines, cursorInfo.lineNumber, cursorInfo.column);
      cursorQueryResult = getTypeAtCursor(
        cursorOffset,
        declaration.sourceMap!,
        declaration.elabMap,
        declaration.typeInfoMap,
        declaration.tacticInfoTree,
        compileResult.definitions,
        code
      );
    }

    if (!cursorQueryResult) {
      return undefined;
    }
  } catch {
    return undefined;
  }

  if (cursorQueryResult.kind !== 'term') {
    return cursorQueryResult;
  }

  return {
    ...cursorQueryResult,
    expression: extractSourceExpression(lines, cursorQueryResult),
  };
}
