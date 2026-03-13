/**
 * Core types for the structured math editor.
 *
 * The math expression is a tree of MathNodes. Each compound node has named
 * "slots" that are MathRows (sequences of child nodes). The cursor always
 * lives at an offset within some MathRow.
 */

// ============================================================================
// Node IDs
// ============================================================================

export type NodeId = number;

let _nextNodeId = 1;
export function freshId(): NodeId { return _nextNodeId++; }
export function resetIds(start = 1): void { _nextNodeId = start; }

// ============================================================================
// MathRow — the fundamental container
// ============================================================================

export interface MathRow {
  readonly id: NodeId;
  readonly children: readonly MathNode[];
}

// ============================================================================
// MathNode — discriminated union
// ============================================================================

export type MathNode =
  | SymbolNode
  | HoleNode
  | FracNode
  | SubNode
  | SupNode
  | SubSupNode
  | BigOpNode
  | AccentNode
  | DelimiterNode
  | TextNode
  | GroupNode;

export interface SymbolNode {
  readonly tag: 'Symbol';
  readonly id: NodeId;
  readonly value: string; // display char or LaTeX command: "x", "+", "\\alpha", "\\in"
}

export interface HoleNode {
  readonly tag: 'Hole';
  readonly id: NodeId;
}

export interface FracNode {
  readonly tag: 'Frac';
  readonly id: NodeId;
  readonly numer: MathRow;
  readonly denom: MathRow;
}

/** x_{sub} — base is wrapped from the node left of cursor when _ is typed */
export interface SubNode {
  readonly tag: 'Sub';
  readonly id: NodeId;
  readonly base: MathRow;
  readonly sub: MathRow;
}

/** x^{sup} */
export interface SupNode {
  readonly tag: 'Sup';
  readonly id: NodeId;
  readonly base: MathRow;
  readonly sup: MathRow;
}

/** x_{sub}^{sup} — promoted from Sub or Sup */
export interface SubSupNode {
  readonly tag: 'SubSup';
  readonly id: NodeId;
  readonly base: MathRow;
  readonly sub: MathRow;
  readonly sup: MathRow;
}

/** \sum, \int, \prod, \lim — body is the expression being operated on */
export interface BigOpNode {
  readonly tag: 'BigOp';
  readonly id: NodeId;
  readonly operator: 'sum' | 'int' | 'prod' | 'lim';
  readonly below: MathRow | null;
  readonly above: MathRow | null;
  readonly body: MathRow;
}

/** \vec{body}, \hat{body}, \overline{body} */
export interface AccentNode {
  readonly tag: 'Accent';
  readonly id: NodeId;
  readonly accent: 'vec' | 'hat' | 'bar' | 'tilde' | 'dot' | 'overline';
  readonly body: MathRow;
}

/** \left( ... \right), \left| ... \right|, \left\| ... \right\| */
export interface DelimiterNode {
  readonly tag: 'Delimiter';
  readonly id: NodeId;
  readonly open: string;  // '(', '[', '|', '\\|', '\\{'
  readonly close: string; // ')', ']', '|', '\\|', '\\}'
  readonly inner: MathRow;
}

/** \text{and}, \text{where}, etc. — upright text in math mode */
export interface TextNode {
  readonly tag: 'Text';
  readonly id: NodeId;
  readonly content: string;
}

/** Wrapper node that annotates children with an HTML id for interactive selection. */
export interface GroupNode {
  readonly tag: 'Group';
  readonly id: NodeId;
  readonly htmlId: string;
  readonly children: readonly MathNode[];
}

// ============================================================================
// Cursor and Editor State
// ============================================================================

export interface RowPathSegment {
  readonly nodeId: NodeId;
  readonly slot: string; // 'numer', 'denom', 'base', 'sub', 'sup', 'below', 'above', 'body', 'inner'
}

export type RowPath = readonly RowPathSegment[];

export interface CursorState {
  readonly path: RowPath;
  readonly offset: number; // 0..children.length
}

export interface MathEditorState {
  readonly root: MathRow;
  readonly cursor: CursorState;
  readonly commandBuffer: string | null; // null = not in command mode; string = chars after '\'
  readonly textBuffer: string | null;    // null = not in text mode; string = chars accumulated so far
}

// ============================================================================
// Constructors
// ============================================================================

export function mkRow(children: MathNode[]): MathRow {
  return { id: freshId(), children };
}

export function mkSymbol(value: string): SymbolNode {
  return { tag: 'Symbol', id: freshId(), value };
}

export function mkHole(): HoleNode {
  return { tag: 'Hole', id: freshId() };
}

export function mkFrac(numer: MathRow, denom: MathRow): FracNode {
  return { tag: 'Frac', id: freshId(), numer, denom };
}

export function mkSub(base: MathRow, sub: MathRow): SubNode {
  return { tag: 'Sub', id: freshId(), base, sub };
}

export function mkSup(base: MathRow, sup: MathRow): SupNode {
  return { tag: 'Sup', id: freshId(), base, sup };
}

export function mkSubSup(base: MathRow, sub: MathRow, sup: MathRow): SubSupNode {
  return { tag: 'SubSup', id: freshId(), base, sub, sup };
}

export function mkBigOp(operator: BigOpNode['operator'], below: MathRow | null, above: MathRow | null, body?: MathRow): BigOpNode {
  return { tag: 'BigOp', id: freshId(), operator, below, above, body: body ?? mkRow([mkHole()]) };
}

export function mkAccent(accent: AccentNode['accent'], body: MathRow): AccentNode {
  return { tag: 'Accent', id: freshId(), accent, body };
}

export function mkDelimiter(open: string, close: string, inner: MathRow): DelimiterNode {
  return { tag: 'Delimiter', id: freshId(), open, close, inner };
}

export function mkText(content: string): TextNode {
  return { tag: 'Text', id: freshId(), content };
}

export function mkGroup(htmlId: string, children: readonly MathNode[]): GroupNode {
  return { tag: 'Group', id: freshId(), htmlId, children };
}

/** Create a fresh empty editor state */
export function createEditorState(): MathEditorState {
  return {
    root: mkRow([]),
    cursor: { path: [], offset: 0 },
    commandBuffer: null,
    textBuffer: null,
  };
}
