import type { SemanticToken, WildcardInlayHint } from '../compiler/compile';

export const TEXT_EDITOR_SEMANTIC_TOKEN_TYPES = [
  'termName',
  'constName',
  'boundVar',
  'patternVar',
  'absurd',
  'namedBrace',
  'tacticName',
  'directive',
  'directiveValue',
] as const;

export const TEXT_EDITOR_SEMANTIC_TOKEN_MODIFIERS: string[] = [];

export interface EditorInlayHintData {
  lineNumber: number;
  column: number;
  label: string;
}

export interface EditorVisibleLineRange {
  startLineNumber: number;
  endLineNumber: number;
}

export interface SemanticTokenEncodingContext {
  getLineCount: () => number;
  getLineLength: (lineNumber: number) => number;
}

export function buildWildcardInlayHintData(
  hints: WildcardInlayHint[],
  range: EditorVisibleLineRange
): EditorInlayHintData[] {
  return hints
    .filter(hint => hint.line >= range.startLineNumber && hint.line <= range.endLineNumber)
    .map(hint => ({
      lineNumber: hint.line,
      column: hint.column,
      label: hint.name,
    }));
}

export function encodeSemanticTokensForMonaco(
  tokens: SemanticToken[],
  context: SemanticTokenEncodingContext
): Uint32Array {
  const data: number[] = [];
  let prevLine = 0;
  let prevCol = 0;

  const sortedTokens = [...tokens].sort((a, b) => {
    if (a.line !== b.line) return a.line - b.line;
    return a.column - b.column;
  });

  for (const token of sortedTokens) {
    const tokenTypeIndex = TEXT_EDITOR_SEMANTIC_TOKEN_TYPES.indexOf(token.type);
    if (tokenTypeIndex === -1) continue;

    const monacoLine = token.line;
    if (monacoLine < 1 || monacoLine > context.getLineCount()) continue;

    const lineLength = context.getLineLength(monacoLine);
    const startCol0 = token.column - 1;
    if (startCol0 < 0 || startCol0 >= lineLength) continue;

    const clampedLength = Math.min(token.length, lineLength - startCol0);
    const deltaLine = monacoLine - 1 - prevLine;
    const deltaCol = deltaLine === 0 ? startCol0 - prevCol : startCol0;

    data.push(deltaLine, deltaCol, clampedLength, tokenTypeIndex, 0);
    prevLine = monacoLine - 1;
    prevCol = startCol0;
  }

  return new Uint32Array(data);
}
