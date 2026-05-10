import type { editor as MonacoEditor } from 'monaco-editor';
import type { SemanticToken, WildcardInlayHint } from '../compiler/compile';
import {
  buildWildcardInlayHintData,
  encodeSemanticTokensForMonaco,
  TEXT_EDITOR_SEMANTIC_TOKEN_MODIFIERS,
  TEXT_EDITOR_SEMANTIC_TOKEN_TYPES,
} from './textEditorSemanticData';
import type { EditorCursorInfo } from './textEditorModel';

export type Monaco = typeof import('monaco-editor');
export type IStandaloneCodeEditor = MonacoEditor.IStandaloneCodeEditor;

export const MONACO_WIDGET_STYLES = `
  .monaco-hover,
  .monaco-editor .suggest-widget,
  .monaco-editor .parameter-hints-widget,
  .monaco-editor-overlaymessage,
  .monaco-editor .monaco-hover-content {
    z-index: 10001 !important;
  }
`;

const UNICODE_ABBREVIATIONS: Record<string, string> = {
  '\\alpha': 'α',
  '\\beta': 'β',
  '\\gamma': 'γ',
  '\\delta': 'δ',
  '\\epsilon': 'ε',
  '\\zeta': 'ζ',
  '\\eta': 'η',
  '\\theta': 'θ',
  '\\iota': 'ι',
  '\\kappa': 'κ',
  '\\lambda': 'λ',
  '\\mu': 'μ',
  '\\nu': 'ν',
  '\\xi': 'ξ',
  '\\pi': 'π',
  '\\rho': 'ρ',
  '\\sigma': 'σ',
  '\\tau': 'τ',
  '\\upsilon': 'υ',
  '\\phi': 'φ',
  '\\chi': 'χ',
  '\\psi': 'ψ',
  '\\omega': 'ω',
  '\\Gamma': 'Γ',
  '\\Delta': 'Δ',
  '\\Theta': 'Θ',
  '\\Lambda': 'Λ',
  '\\Xi': 'Ξ',
  '\\Pi': 'Π',
  '\\Sigma': 'Σ',
  '\\Phi': 'Φ',
  '\\Psi': 'Ψ',
  '\\Omega': 'Ω',
  '\\to': '→',
  '\\rightarrow': '→',
  '\\leftarrow': '←',
  '\\Rightarrow': '⇒',
  '\\Leftarrow': '⇐',
  '\\forall': '∀',
  '\\exists': '∃',
  '\\neg': '¬',
  '\\and': '∧',
  '\\or': '∨',
  '\\times': '×',
  '\\cdot': '·',
  '\\circ': '∘',
  '\\le': '≤',
  '\\ge': '≥',
  '\\ne': '≠',
  '\\equiv': '≡',
  '\\approx': '≈',
  '\\infty': '∞',
  '\\nat': 'ℕ',
  '\\int': 'ℤ',
  '\\rat': 'ℚ',
  '\\real': 'ℝ',
  '\\complex': 'ℂ',
  '\\0': '₀',
  '\\1': '₁',
  '\\2': '₂',
  '\\3': '₃',
  '\\4': '₄',
  '\\5': '₅',
  '\\6': '₆',
  '\\7': '₇',
  '\\8': '₈',
  '\\9': '₉',
};

const ABBREV_PATTERN = new RegExp(
  '(' + Object.keys(UNICODE_ABBREVIATIONS)
    .map(k => k.replace(/\\/g, '\\\\'))
    .sort((a, b) => b.length - a.length)
    .join('|') + ')$'
);

const SYNTAX_COLORS = {
  keyword: '569cd6',
  keywordOperator: '94d0ff',
  typeKeyword: 'cf92cd',
  comment: '6a9955',
  string: 'ce9178',
  number: 'b5cea8',
  identifier: 'd4d4d4',
  constName: '4ec9b0',
  termName: 'e5b387',
  patternVar: '9cdcfe',
  delimiter: 'e5c995',
  namedBrace: '6e7681',
  hole: 'e5c07b',
  absurd: '4fc1ff',
  tacticName: 'ffb0d8',
  directive: 'ff79c6',
  directiveValue: '8b949e',
};

export const MONACO_THEME: MonacoEditor.IStandaloneThemeData = {
  base: 'vs-dark',
  inherit: true,
  rules: [
    { token: 'comment', foreground: SYNTAX_COLORS.comment, fontStyle: 'italic' },
    { token: 'keyword', foreground: SYNTAX_COLORS.keyword },
    { token: 'keyword.operator', foreground: SYNTAX_COLORS.keywordOperator },
    { token: 'type.identifier', foreground: SYNTAX_COLORS.typeKeyword },
    { token: 'string', foreground: SYNTAX_COLORS.string },
    { token: 'number', foreground: SYNTAX_COLORS.number },
    { token: 'identifier', foreground: SYNTAX_COLORS.identifier },
    { token: 'identifier.const', foreground: SYNTAX_COLORS.constName },
    { token: 'identifier.term', foreground: SYNTAX_COLORS.termName },
    { token: 'identifier.pattern', foreground: SYNTAX_COLORS.patternVar },
    { token: 'delimiter', foreground: SYNTAX_COLORS.delimiter },
    { token: 'delimiter.bracket', foreground: SYNTAX_COLORS.delimiter },
    { token: 'variable.predefined', foreground: SYNTAX_COLORS.hole },
    { token: 'variable.wildcard', foreground: SYNTAX_COLORS.patternVar },
    { token: 'termName', foreground: SYNTAX_COLORS.termName },
    { token: 'constName', foreground: SYNTAX_COLORS.constName },
    { token: 'boundVar', foreground: SYNTAX_COLORS.patternVar },
    { token: 'patternVar', foreground: SYNTAX_COLORS.patternVar },
    { token: 'absurd', foreground: SYNTAX_COLORS.absurd },
    { token: 'namedBrace', foreground: SYNTAX_COLORS.namedBrace },
    { token: 'tacticName', foreground: SYNTAX_COLORS.tacticName },
    { token: 'directive', foreground: SYNTAX_COLORS.directive },
    { token: 'directiveValue', foreground: SYNTAX_COLORS.directiveValue },
  ],
  colors: {
    'editor.background': '#161b22',
    'editor.foreground': '#c9d1d9',
    'editor.lineHighlightBackground': '#161b22',
    'editor.selectionBackground': '#264f78',
    'editorCursor.foreground': '#58a6ff',
    'editorLineNumber.foreground': '#6e7681',
    'editorLineNumber.activeForeground': '#c9d1d9',
    'editorIndentGuide.background': '#21262d',
    'editorIndentGuide.activeBackground': '#30363d',
    'editorBracketMatch.background': '#2d333b',
    'editorBracketMatch.border': '#58a6ff',
    'editorWarning.foreground': '#' + SYNTAX_COLORS.hole,
  },
};

export interface SemanticTokensEventController {
  fire: () => void;
  event: import('monaco-editor').IEvent<void>;
}

export interface UnicodeReplacement {
  startColumn: number;
  endColumn: number;
  text: string;
}

export function findUnicodeAbbreviationReplacement(
  textUpToCursor: string,
  cursorColumn: number
): UnicodeReplacement | null {
  const match = textUpToCursor.match(ABBREV_PATTERN);
  if (!match) return null;
  const replacement = UNICODE_ABBREVIATIONS[match[1]];
  if (!replacement) return null;
  return {
    startColumn: cursorColumn - match[1].length,
    endColumn: cursorColumn,
    text: replacement,
  };
}

export function toCursorInfo(selection: {
  positionLineNumber: number;
  positionColumn: number;
  startLineNumber: number;
  startColumn: number;
  endLineNumber: number;
  endColumn: number;
}): EditorCursorInfo {
  return {
    lineNumber: selection.positionLineNumber,
    column: selection.positionColumn,
    selStartLine: selection.startLineNumber,
    selStartCol: selection.startColumn,
    selEndLine: selection.endLineNumber,
    selEndCol: selection.endColumn,
  };
}

export interface ConfigureTextEditorMonacoOptions {
  monaco: Monaco;
  editor: IStandaloneCodeEditor;
  getWildcardHints: () => WildcardInlayHint[];
  getSemanticTokens: () => SemanticToken[];
  setCursorInfo: (info: EditorCursorInfo) => void;
  setSemanticTokensEventController: (controller: SemanticTokensEventController) => void;
}

export function configureTextEditorMonaco({
  monaco,
  editor,
  getWildcardHints,
  getSemanticTokens,
  setCursorInfo,
  setSemanticTokensEventController,
}: ConfigureTextEditorMonacoOptions): void {
  monaco.languages.register({ id: 'tt' });

  monaco.languages.setLanguageConfiguration('tt', {
    comments: {
      lineComment: '--',
      blockComment: ['{-', '-}'],
    },
    brackets: [
      ['{', '}'],
      ['[', ']'],
      ['(', ')'],
    ],
    autoClosingPairs: [
      { open: '{', close: '}' },
      { open: '[', close: ']' },
      { open: '(', close: ')' },
      { open: '"', close: '"', notIn: ['string'] },
      { open: '{-', close: '-}' },
    ],
    surroundingPairs: [
      { open: '{', close: '}' },
      { open: '[', close: ']' },
      { open: '(', close: ')' },
      { open: '"', close: '"' },
    ],
  });

  monaco.languages.setMonarchTokensProvider('tt', {
    tokenizer: {
      root: [
        [/\{-/, 'comment', '@comment'],
        [/--.*$/, 'comment'],
        [/\b(Type|Prop|ULevel|USucc|UMax|UIMax)\b/, 'type.identifier'],
        [/\b(inductive|record|constructor|extends|where|let|in|fun|with|by|postulate)\b/, 'keyword'],
        [/#absurd\b/, 'keyword'],
        [/\.\.\./, 'keyword.operator'],
        [/\?[a-zA-Z_][a-zA-Z0-9_']*/, 'variable.predefined'],
        [/_/, 'variable.wildcard'],
        [/\d+/, 'number'],
        [/ω/, 'number'],
        [/[a-zA-Z_][a-zA-Z0-9_']*/, 'identifier'],
        [/->|=>/, 'keyword.operator'],
        [/[=:+\-*/\\<>!|]+/, 'delimiter'],
        [/[()[\]{}]/, 'delimiter.bracket'],
        [/[,.]/, 'delimiter'],
        [/\s+/, 'white'],
      ],
      comment: [
        [/[^{-]+/, 'comment'],
        [/-\}/, 'comment', '@pop'],
        [/[{-]/, 'comment'],
      ],
    }
  });

  monaco.editor.defineTheme('tt-dark', MONACO_THEME);
  monaco.editor.setTheme('tt-dark');

  const model = editor.getModel();
  if (model) {
    monaco.editor.setModelLanguage(model, 'tt');
  }

  monaco.languages.registerInlayHintsProvider('tt', {
    provideInlayHints: (_model: MonacoEditor.ITextModel, range: { startLineNumber: number; endLineNumber: number }) => {
      const hints = buildWildcardInlayHintData(getWildcardHints(), range).map(hint => ({
        kind: monaco.languages.InlayHintKind.Parameter,
        position: { lineNumber: hint.lineNumber, column: hint.column },
        label: hint.label,
        paddingLeft: false,
        paddingRight: false,
      }));

      return { hints, dispose: () => { } };
    }
  });

  let cursorRafId: number | null = null;
  editor.onDidChangeCursorSelection((e) => {
    if (cursorRafId !== null) cancelAnimationFrame(cursorRafId);
    cursorRafId = requestAnimationFrame(() => {
      cursorRafId = null;
      setCursorInfo(toCursorInfo(e.selection));
    });
  });

  const emitter = new monaco.Emitter<void>();
  setSemanticTokensEventController({
    fire: () => emitter.fire(),
    event: emitter.event,
  });

  monaco.languages.registerDocumentSemanticTokensProvider('tt', {
    getLegend: () => ({
      tokenTypes: [...TEXT_EDITOR_SEMANTIC_TOKEN_TYPES],
      tokenModifiers: TEXT_EDITOR_SEMANTIC_TOKEN_MODIFIERS
    }),
    onDidChange: emitter.event,
    provideDocumentSemanticTokens: (currentModel: MonacoEditor.ITextModel) => ({
      data: encodeSemanticTokensForMonaco(getSemanticTokens(), {
        getLineCount: () => currentModel.getLineCount(),
        getLineLength: (lineNumber) => currentModel.getLineLength(lineNumber),
      }),
      resultId: undefined,
    }),
    releaseDocumentSemanticTokens: () => { }
  });

  editor.onDidChangeModelContent((e) => {
    if (e.isUndoing || e.isRedoing) return;
    if (e.changes.length !== 1) return;
    const change = e.changes[0];
    if (change.text.length !== 1) return;

    const currentModel = editor.getModel();
    const position = editor.getPosition();
    if (!currentModel || !position) return;

    const replacement = findUnicodeAbbreviationReplacement(
      currentModel.getLineContent(position.lineNumber).substring(0, position.column - 1),
      position.column
    );
    if (!replacement) return;

    setTimeout(() => {
      editor.pushUndoStop();
      editor.executeEdits('unicode-abbrev', [{
        range: {
          startLineNumber: position.lineNumber,
          startColumn: replacement.startColumn,
          endLineNumber: position.lineNumber,
          endColumn: replacement.endColumn,
        },
        text: replacement.text,
        forceMoveMarkers: true
      }]);
    }, 0);
  });
}
