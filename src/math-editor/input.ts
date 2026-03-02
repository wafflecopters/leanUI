/**
 * Input handling for the structured math editor.
 *
 * All functions are pure: (state, input) → newState.
 * The tree is immutable — mutations produce new trees.
 */

import {
  MathNode, MathRow, MathEditorState, CursorState,
  mkRow, mkSymbol, mkHole, mkFrac, mkSub, mkSup, mkSubSup,
  mkBigOp, mkAccent, mkDelimiter, mkText, freshId,
} from './types';
import { resolveRow, getSlots, getSlotRow, findChildIndex, moveRight } from './navigation';

// ============================================================================
// Tree mutation helpers
// ============================================================================

/** Replace a MathRow anywhere in the tree by walking the cursor path. */
function replaceRowAtPath(
  root: MathRow,
  path: CursorState['path'],
  newRow: MathRow
): MathRow {
  if (path.length === 0) return newRow;

  const [seg, ...rest] = path;
  const newChildren = root.children.map(child => {
    if (child.id !== seg.nodeId) return child;
    return replaceSlot(child, seg.slot, row => replaceRowAtPath(row, rest, newRow));
  });
  return { ...root, children: newChildren };
}

/** Replace a named slot's MathRow within a node. */
function replaceSlot(
  node: MathNode,
  slotName: string,
  transform: (row: MathRow) => MathRow
): MathNode {
  switch (node.tag) {
    case 'Frac':
      if (slotName === 'numer') return { ...node, numer: transform(node.numer) };
      if (slotName === 'denom') return { ...node, denom: transform(node.denom) };
      return node;
    case 'Sub':
      if (slotName === 'base') return { ...node, base: transform(node.base) };
      if (slotName === 'sub') return { ...node, sub: transform(node.sub) };
      return node;
    case 'Sup':
      if (slotName === 'base') return { ...node, base: transform(node.base) };
      if (slotName === 'sup') return { ...node, sup: transform(node.sup) };
      return node;
    case 'SubSup':
      if (slotName === 'base') return { ...node, base: transform(node.base) };
      if (slotName === 'sub') return { ...node, sub: transform(node.sub) };
      if (slotName === 'sup') return { ...node, sup: transform(node.sup) };
      return node;
    case 'BigOp':
      if (slotName === 'below') return { ...node, below: transform(node.below!) };
      if (slotName === 'above') return { ...node, above: transform(node.above!) };
      if (slotName === 'body') return { ...node, body: transform(node.body) };
      return node;
    case 'Accent':
      if (slotName === 'body') return { ...node, body: transform(node.body) };
      return node;
    case 'Delimiter':
      if (slotName === 'inner') return { ...node, inner: transform(node.inner) };
      return node;
    default:
      return node;
  }
}

/** Insert a node into a row at a given offset. */
function insertAtOffset(row: MathRow, offset: number, node: MathNode): MathRow {
  const children = [...row.children];
  children.splice(offset, 0, node);
  return { ...row, children };
}

/** Remove a node from a row at a given index. */
function removeAtIndex(row: MathRow, index: number): MathRow {
  const children = [...row.children];
  children.splice(index, 1);
  return { ...row, children };
}

/** Replace a node at a given index within a row. */
function replaceAtIndex(row: MathRow, index: number, newNode: MathNode): MathRow {
  const children = [...row.children];
  children[index] = newNode;
  return { ...row, children };
}

/** Replace a node at a given index with multiple nodes (splice). */
function spliceAtIndex(row: MathRow, index: number, ...newNodes: MathNode[]): MathRow {
  const children = [...row.children];
  children.splice(index, 1, ...newNodes);
  return { ...row, children };
}

// ============================================================================
// Command table
// ============================================================================

interface CommandEntry {
  create: () => MathNode;
  /** Which slot to place cursor in after creation */
  cursorSlot: string;
  /** Optional extra nodes to insert after the main node (e.g., a body Hole) */
  afterNodes?: () => MathNode[];
}

const COMMAND_TABLE: Record<string, CommandEntry> = {
  frac: {
    create: () => mkFrac(mkRow([mkHole()]), mkRow([mkHole()])),
    cursorSlot: 'numer',
  },
  vec: {
    create: () => mkAccent('vec', mkRow([mkHole()])),
    cursorSlot: 'body',
  },
  hat: {
    create: () => mkAccent('hat', mkRow([mkHole()])),
    cursorSlot: 'body',
  },
  bar: {
    create: () => mkAccent('bar', mkRow([mkHole()])),
    cursorSlot: 'body',
  },
  overline: {
    create: () => mkAccent('overline', mkRow([mkHole()])),
    cursorSlot: 'body',
  },
  tilde: {
    create: () => mkAccent('tilde', mkRow([mkHole()])),
    cursorSlot: 'body',
  },
  dot: {
    create: () => mkAccent('dot', mkRow([mkHole()])),
    cursorSlot: 'body',
  },
  sum: {
    create: () => mkBigOp('sum', mkRow([mkHole()]), mkRow([mkHole()])),
    cursorSlot: 'below',
  },
  int: {
    create: () => mkBigOp('int', mkRow([mkHole()]), mkRow([mkHole()])),
    cursorSlot: 'below',
  },
  prod: {
    create: () => mkBigOp('prod', mkRow([mkHole()]), mkRow([mkHole()])),
    cursorSlot: 'below',
  },
  lim: {
    create: () => mkBigOp('lim', mkRow([mkHole(), mkSymbol('\\to'), mkHole()]), null),
    cursorSlot: 'below',
  },
};

/** Symbol shortcuts — single characters or short names that map to LaTeX symbols */
const SYMBOL_TABLE: Record<string, string> = {
  alpha: '\\alpha',
  beta: '\\beta',
  gamma: '\\gamma',
  delta: '\\delta',
  epsilon: '\\epsilon',
  varepsilon: '\\varepsilon',
  zeta: '\\zeta',
  eta: '\\eta',
  theta: '\\theta',
  lambda: '\\lambda',
  mu: '\\mu',
  nu: '\\nu',
  xi: '\\xi',
  pi: '\\pi',
  rho: '\\rho',
  sigma: '\\sigma',
  tau: '\\tau',
  phi: '\\phi',
  chi: '\\chi',
  psi: '\\psi',
  omega: '\\omega',
  Gamma: '\\Gamma',
  Delta: '\\Delta',
  Theta: '\\Theta',
  Lambda: '\\Lambda',
  Xi: '\\Xi',
  Pi: '\\Pi',
  Sigma: '\\Sigma',
  Phi: '\\Phi',
  Psi: '\\Psi',
  Omega: '\\Omega',
  'in': '\\in',
  to: '\\to',
  R: '\\mathbb{R}',
  N: '\\mathbb{N}',
  Z: '\\mathbb{Z}',
  Q: '\\mathbb{Q}',
  C: '\\mathbb{C}',
  times: '\\times',
  cdot: '\\cdot',
  leq: '\\leq',
  geq: '\\geq',
  neq: '\\neq',
  infty: '\\infty',
  forall: '\\forall',
  exists: '\\exists',
  subset: '\\subset',
  subseteq: '\\subseteq',
  cup: '\\cup',
  cap: '\\cap',
  emptyset: '\\emptyset',
  nabla: '\\nabla',
  partial: '\\partial',
  pm: '\\pm',
  mp: '\\mp',
  sqrt: '\\sqrt', // TODO: make this a compound node with inner slot
  ldots: '\\ldots',
  cdots: '\\cdots',
  vdots: '\\vdots',
  ddots: '\\ddots',
  text: '\\text', // intercepted in acceptCommand to enter text mode
};

// ============================================================================
// Main input handler
// ============================================================================

export type InputAction =
  | { type: 'char'; char: string }
  | { type: 'backspace' }
  | { type: 'left' }
  | { type: 'right' }
  | { type: 'tab' };

export function handleInput(state: MathEditorState, action: InputAction): MathEditorState {
  // If in text buffer mode, route to text handler
  if (state.textBuffer !== null) {
    if (action.type === 'char') return handleTextChar(state, action.char);
    if (action.type === 'backspace') return handleTextBackspace(state);
    // Other actions: commit text first, then process
    const committed = commitTextBuffer(state);
    return handleInput(committed, action);
  }

  // If in command buffer mode, route to command handler
  if (state.commandBuffer !== null && action.type === 'char') {
    return handleCommandChar(state, action.char);
  }

  switch (action.type) {
    case 'char':
      return handleChar(state, action.char);
    case 'backspace':
      return handleBackspace(state);
    case 'left':
    case 'right':
    case 'tab':
      // Navigation handled by navigation.ts — but exposed here for convenience
      return state;
  }
}

// ============================================================================
// Character input
// ============================================================================

function handleChar(state: MathEditorState, char: string): MathEditorState {
  switch (char) {
    case '\\':
      return { ...state, commandBuffer: '' };

    case '_':
      return handleSubscript(state);

    case '^':
      return handleSuperscript(state);

    case '(':
      return handleOpenDelimiter(state, '(', ')');

    case '[':
      return handleOpenDelimiter(state, '[', ']');

    case ')':
    case ']':
      return handleCloseDelimiter(state);

    case ' ':
      // Enter text mode
      return { ...state, textBuffer: '' };

    default: {
      const inserted = insertSymbol(state, char);
      return tryMergeKeyword(inserted);
    }
  }
}

// ============================================================================
// Symbol insertion
// ============================================================================

function insertSymbol(state: MathEditorState, value: string): MathEditorState {
  const row = resolveRow(state.root, state.cursor.path);
  const offset = state.cursor.offset;

  // If cursor is right before a Hole, replace it
  if (offset < row.children.length && row.children[offset].tag === 'Hole') {
    const newRow = replaceAtIndex(row, offset, mkSymbol(value));
    const newRoot = replaceRowAtPath(state.root, state.cursor.path, newRow);
    return { ...state, root: newRoot, cursor: { path: state.cursor.path, offset: offset + 1 } };
  }

  // If cursor is at end of row and the last child is a Hole, replace it
  // (defensive — navigation should not place cursor after Holes, but handle it gracefully)
  if (offset === row.children.length && offset > 0 && row.children[offset - 1].tag === 'Hole') {
    const newRow = replaceAtIndex(row, offset - 1, mkSymbol(value));
    const newRoot = replaceRowAtPath(state.root, state.cursor.path, newRow);
    return { ...state, root: newRoot, cursor: { path: state.cursor.path, offset: offset } };
  }

  // Otherwise insert at cursor position
  const newRow = insertAtOffset(row, offset, mkSymbol(value));
  const newRoot = replaceRowAtPath(state.root, state.cursor.path, newRow);
  return { ...state, root: newRoot, cursor: { path: state.cursor.path, offset: offset + 1 } };
}

/**
 * Grammar keywords that should be auto-merged from consecutive letter symbols.
 * When the user types 'I','f' and "if" is in this set, the two Symbol nodes
 * are replaced with a single Text('If') node.
 */
const AUTO_MERGE_KEYWORDS = new Set(['if', 'let', 'assume', 'and', 'then', 'forall']);

/**
 * After inserting a symbol, check if the last N symbols at the cursor spell
 * a recognized keyword. If so, merge them into a Text node.
 * Only merges when preceded by a non-letter (word boundary).
 */
function tryMergeKeyword(state: MathEditorState): MathEditorState {
  const row = resolveRow(state.root, state.cursor.path);
  const offset = state.cursor.offset;

  // Scan backwards from cursor collecting consecutive single-char letter Symbols
  let word = '';
  let startIdx = offset - 1;
  while (startIdx >= 0) {
    const node = row.children[startIdx];
    if (node.tag !== 'Symbol' || node.value.length !== 1 || !/^[a-zA-Z]$/.test(node.value)) break;
    word = node.value + word;
    if (AUTO_MERGE_KEYWORDS.has(word.toLowerCase())) {
      // Only merge if preceded by a non-letter or at the start of the row
      const preceded = startIdx > 0 ? row.children[startIdx - 1] : null;
      const precededByLetter = preceded !== null &&
        preceded.tag === 'Symbol' && preceded.value.length === 1 && /^[a-zA-Z]$/.test(preceded.value);
      if (!precededByLetter) {
        // Replace symbols [startIdx..offset-1] with Text(word)
        const textNode = mkText(word);
        const newChildren = [...row.children];
        newChildren.splice(startIdx, offset - startIdx, textNode);
        const newRow: MathRow = { ...row, children: newChildren };
        const newRoot = replaceRowAtPath(state.root, state.cursor.path, newRow);
        return {
          ...state,
          root: newRoot,
          cursor: { ...state.cursor, offset: startIdx + 1 },
        };
      }
    }
    startIdx--;
  }

  return state;
}

// ============================================================================
// Subscript / Superscript
// ============================================================================

function handleSubscript(state: MathEditorState): MathEditorState {
  const row = resolveRow(state.root, state.cursor.path);
  const offset = state.cursor.offset;

  if (offset === 0) {
    // Nothing to the left — insert Sub with Hole base
    const sub = mkSub(mkRow([mkHole()]), mkRow([mkHole()]));
    const newRow = insertAtOffset(row, offset, sub);
    const newRoot = replaceRowAtPath(state.root, state.cursor.path, newRow);
    return {
      ...state,
      root: newRoot,
      cursor: { path: [...state.cursor.path, { nodeId: sub.id, slot: 'sub' }], offset: 0 },
    };
  }

  const leftNode = row.children[offset - 1];

  // If left node is already a Sup, promote to SubSup
  if (leftNode.tag === 'Sup') {
    const subSup = mkSubSup(leftNode.base, mkRow([mkHole()]), leftNode.sup);
    const newRow = replaceAtIndex(row, offset - 1, subSup);
    const newRoot = replaceRowAtPath(state.root, state.cursor.path, newRow);
    return {
      ...state,
      root: newRoot,
      cursor: { path: [...state.cursor.path, { nodeId: subSup.id, slot: 'sub' }], offset: 0 },
    };
  }

  // If left node is already a Sub or SubSup, enter the sub slot
  if (leftNode.tag === 'Sub') {
    return {
      ...state,
      cursor: { path: [...state.cursor.path, { nodeId: leftNode.id, slot: 'sub' }], offset: 0 },
    };
  }
  if (leftNode.tag === 'SubSup') {
    return {
      ...state,
      cursor: { path: [...state.cursor.path, { nodeId: leftNode.id, slot: 'sub' }], offset: 0 },
    };
  }

  // Wrap left node as base of new Sub
  const sub = mkSub(mkRow([leftNode]), mkRow([mkHole()]));
  const newRow = replaceAtIndex(row, offset - 1, sub);
  const newRoot = replaceRowAtPath(state.root, state.cursor.path, newRow);
  return {
    ...state,
    root: newRoot,
    cursor: { path: [...state.cursor.path, { nodeId: sub.id, slot: 'sub' }], offset: 0 },
  };
}

function handleSuperscript(state: MathEditorState): MathEditorState {
  const row = resolveRow(state.root, state.cursor.path);
  const offset = state.cursor.offset;

  if (offset === 0) {
    // Nothing to the left — insert Sup with Hole base
    const sup = mkSup(mkRow([mkHole()]), mkRow([mkHole()]));
    const newRow = insertAtOffset(row, offset, sup);
    const newRoot = replaceRowAtPath(state.root, state.cursor.path, newRow);
    return {
      ...state,
      root: newRoot,
      cursor: { path: [...state.cursor.path, { nodeId: sup.id, slot: 'sup' }], offset: 0 },
    };
  }

  const leftNode = row.children[offset - 1];

  // If left node is already a Sub, promote to SubSup
  if (leftNode.tag === 'Sub') {
    const subSup = mkSubSup(leftNode.base, leftNode.sub, mkRow([mkHole()]));
    const newRow = replaceAtIndex(row, offset - 1, subSup);
    const newRoot = replaceRowAtPath(state.root, state.cursor.path, newRow);
    return {
      ...state,
      root: newRoot,
      cursor: { path: [...state.cursor.path, { nodeId: subSup.id, slot: 'sup' }], offset: 0 },
    };
  }

  // If left node is already a Sup or SubSup, enter the sup slot
  if (leftNode.tag === 'Sup') {
    return {
      ...state,
      cursor: { path: [...state.cursor.path, { nodeId: leftNode.id, slot: 'sup' }], offset: 0 },
    };
  }
  if (leftNode.tag === 'SubSup') {
    return {
      ...state,
      cursor: { path: [...state.cursor.path, { nodeId: leftNode.id, slot: 'sup' }], offset: 0 },
    };
  }

  // Wrap left node as base of new Sup
  const sup = mkSup(mkRow([leftNode]), mkRow([mkHole()]));
  const newRow = replaceAtIndex(row, offset - 1, sup);
  const newRoot = replaceRowAtPath(state.root, state.cursor.path, newRow);
  return {
    ...state,
    root: newRoot,
    cursor: { path: [...state.cursor.path, { nodeId: sup.id, slot: 'sup' }], offset: 0 },
  };
}

// ============================================================================
// Delimiter handling
// ============================================================================

function handleOpenDelimiter(state: MathEditorState, open: string, close: string): MathEditorState {
  const row = resolveRow(state.root, state.cursor.path);
  const offset = state.cursor.offset;

  const delim = mkDelimiter(open, close, mkRow([mkHole()]));
  const newRow = insertAtOffset(row, offset, delim);
  const newRoot = replaceRowAtPath(state.root, state.cursor.path, newRow);

  return {
    ...state,
    root: newRoot,
    cursor: {
      path: [...state.cursor.path, { nodeId: delim.id, slot: 'inner' }],
      offset: 0,
    },
  };
}

function handleCloseDelimiter(state: MathEditorState): MathEditorState {
  // Walk up the path to find the nearest enclosing Delimiter
  for (let i = state.cursor.path.length - 1; i >= 0; i--) {
    const seg = state.cursor.path[i];
    // Resolve the parent row to find the node
    const parentPath = state.cursor.path.slice(0, i);
    const parentRow = resolveRow(state.root, parentPath);
    const node = parentRow.children.find(c => c.id === seg.nodeId);
    if (node && node.tag === 'Delimiter') {
      // Exit to after the delimiter
      const nodeIndex = findChildIndex(parentRow, node.id);
      return {
        ...state,
        cursor: { path: parentPath, offset: nodeIndex + 1 },
      };
    }
  }
  // No enclosing delimiter — do nothing
  return state;
}

// ============================================================================
// Backspace
// ============================================================================

function handleBackspace(state: MathEditorState): MathEditorState {
  const row = resolveRow(state.root, state.cursor.path);
  const offset = state.cursor.offset;

  if (state.commandBuffer !== null) {
    // In command mode — delete last char or exit command mode
    if (state.commandBuffer.length === 0) {
      return { ...state, commandBuffer: null };
    }
    return { ...state, commandBuffer: state.commandBuffer.slice(0, -1) };
  }

  if (offset > 0) {
    const leftNode = row.children[offset - 1];

    if (leftNode.tag === 'Symbol' || leftNode.tag === 'Hole' || leftNode.tag === 'Text') {
      // Delete the leaf
      const newRow = removeAtIndex(row, offset - 1);
      const newRoot = replaceRowAtPath(state.root, state.cursor.path, newRow);
      return { ...state, root: newRoot, cursor: { path: state.cursor.path, offset: offset - 1 } };
    }

    // For compound nodes, dissolve: replace node with its base/inner content
    if (leftNode.tag === 'Sub') {
      return dissolveCompound(state, row, offset - 1, leftNode.base);
    }
    if (leftNode.tag === 'Sup') {
      return dissolveCompound(state, row, offset - 1, leftNode.base);
    }
    if (leftNode.tag === 'SubSup') {
      return dissolveCompound(state, row, offset - 1, leftNode.base);
    }
    if (leftNode.tag === 'Frac') {
      // Dissolve frac — spill numerator content at cursor position
      return dissolveCompound(state, row, offset - 1, leftNode.numer);
    }
    if (leftNode.tag === 'Delimiter') {
      return dissolveCompound(state, row, offset - 1, leftNode.inner);
    }
    if (leftNode.tag === 'Accent') {
      return dissolveCompound(state, row, offset - 1, leftNode.body);
    }
    if (leftNode.tag === 'BigOp') {
      // Dissolve: spill body content
      return dissolveCompound(state, row, offset - 1, leftNode.body);
    }
  }

  // At start of a slot — exit the compound node (move cursor to before it)
  if (offset === 0 && state.cursor.path.length > 0) {
    const parentPath = state.cursor.path.slice(0, -1);
    const lastSeg = state.cursor.path[state.cursor.path.length - 1];
    const parentRow = resolveRow(state.root, parentPath);
    const nodeIndex = findChildIndex(parentRow, lastSeg.nodeId);
    return { ...state, cursor: { path: parentPath, offset: nodeIndex } };
  }

  return state;
}

/** Dissolve a compound node: replace it with the children of one of its slots. */
function dissolveCompound(
  state: MathEditorState,
  row: MathRow,
  index: number,
  contentRow: MathRow
): MathEditorState {
  // Filter out Hole placeholders when spilling content
  const content = contentRow.children.filter(c => c.tag !== 'Hole');
  const newChildren = [...row.children];
  newChildren.splice(index, 1, ...content);
  const newRow: MathRow = { ...row, children: newChildren };
  const newRoot = replaceRowAtPath(state.root, state.cursor.path, newRow);
  return {
    ...state,
    root: newRoot,
    cursor: { path: state.cursor.path, offset: index + content.length },
  };
}

// ============================================================================
// Command buffer
// ============================================================================

/** Returns all command/symbol names that start with the given prefix. */
export function getCommandCandidates(prefix: string): string[] {
  if (prefix === '') return [];
  const all = [...Object.keys(COMMAND_TABLE), ...Object.keys(SYMBOL_TABLE)];
  return all.filter(key => key.startsWith(prefix)).sort();
}

/** Returns the currently selected (best-match) candidate for a buffer. */
export function getSelectedCandidate(buffer: string): string | null {
  const candidates = getCommandCandidates(buffer);
  if (candidates.length === 0) return null;
  // Exact match gets priority
  if (candidates.includes(buffer)) return buffer;
  return candidates[0];
}

function handleCommandChar(state: MathEditorState, char: string): MathEditorState {
  if (char === ' ' || char === 'Enter' || char === 'Tab') {
    // Accept current best match
    return acceptCommand(state);
  }

  if (char === '\\') {
    // Double backslash — cancel command mode
    return { ...state, commandBuffer: null };
  }

  // Accumulate into buffer
  const newBuffer = state.commandBuffer! + char;

  // Check if any commands/symbols start with the new buffer
  const candidates = getCommandCandidates(newBuffer);

  if (candidates.length === 0) {
    // No matches for the new buffer.
    // Try to accept what was in the old buffer and re-process this char.
    const oldBuffer = state.commandBuffer!;
    if (COMMAND_TABLE[oldBuffer] || SYMBOL_TABLE[oldBuffer]) {
      const executed = acceptCommand(state);
      return handleChar(executed, char);
    }
    // No valid command at all — cancel command mode
    return { ...state, commandBuffer: null };
  }

  if (candidates.length === 1 && candidates[0] === newBuffer) {
    // Exactly one match and it's a complete match — auto-fire
    return acceptCommand({ ...state, commandBuffer: newBuffer });
  }

  // Multiple candidates or partial match — keep accumulating
  return { ...state, commandBuffer: newBuffer };
}

/** Accept the best matching command for the current buffer. */
function acceptCommand(state: MathEditorState): MathEditorState {
  const buffer = state.commandBuffer!;
  const selected = getSelectedCandidate(buffer);

  if (!selected) {
    // No match — cancel
    return { ...state, commandBuffer: null };
  }

  // Special: \text enters text mode
  if (selected === 'text') {
    return { ...state, commandBuffer: null, textBuffer: '' };
  }

  // Try command table first (compound nodes)
  const entry = COMMAND_TABLE[selected];
  if (entry) {
    const row = resolveRow(state.root, state.cursor.path);
    const offset = state.cursor.offset;
    const node = entry.create();
    const after = entry.afterNodes?.() ?? [];
    const newChildren = [...row.children];
    newChildren.splice(offset, 0, node, ...after);
    const newRow: MathRow = { ...row, children: newChildren };
    const newRoot = replaceRowAtPath(state.root, state.cursor.path, newRow);

    return {
      ...state,
      root: newRoot,
      cursor: {
        path: [...state.cursor.path, { nodeId: node.id, slot: entry.cursorSlot }],
        offset: 0,
      },
      commandBuffer: null,
    };
  }

  // Try symbol table
  const symbolValue = SYMBOL_TABLE[selected];
  if (symbolValue) {
    const newState = { ...state, commandBuffer: null };
    return insertSymbol(newState, symbolValue);
  }

  // Unknown command — cancel
  return { ...state, commandBuffer: null };
}

// ============================================================================
// Text buffer
// ============================================================================

function handleTextChar(state: MathEditorState, char: string): MathEditorState {
  if (char === ' ') {
    // Space terminates text mode
    return commitTextBuffer(state);
  }

  if (char === '\\') {
    // Backslash terminates text, then enters command mode
    const committed = commitTextBuffer(state);
    return { ...committed, commandBuffer: '' };
  }

  // Letters accumulate
  if (/^[a-zA-Z]$/.test(char)) {
    return { ...state, textBuffer: state.textBuffer! + char };
  }

  // Non-letter chars: terminate text mode, insert the text, then process the char normally
  const committed = commitTextBuffer(state);
  return handleChar(committed, char);
}

function handleTextBackspace(state: MathEditorState): MathEditorState {
  if (state.textBuffer!.length === 0) {
    // Empty buffer: cancel text mode
    return { ...state, textBuffer: null };
  }
  // Remove last character
  return { ...state, textBuffer: state.textBuffer!.slice(0, -1) };
}

function commitTextBuffer(state: MathEditorState): MathEditorState {
  const text = state.textBuffer!;
  const cleared: MathEditorState = { ...state, textBuffer: null };
  if (text.length === 0) return cleared;

  // Insert a TextNode at cursor
  const row = resolveRow(cleared.root, cleared.cursor.path);
  const offset = cleared.cursor.offset;
  const node = mkText(text);

  // Replace Hole if cursor is on one
  if (offset < row.children.length && row.children[offset].tag === 'Hole') {
    const newRow = replaceAtIndex(row, offset, node);
    const newRoot = replaceRowAtPath(cleared.root, cleared.cursor.path, newRow);
    return { ...cleared, root: newRoot, cursor: { path: cleared.cursor.path, offset: offset + 1 } };
  }

  // Otherwise insert at cursor
  const newRow = insertAtOffset(row, offset, node);
  const newRoot = replaceRowAtPath(cleared.root, cleared.cursor.path, newRow);
  return { ...cleared, root: newRoot, cursor: { path: cleared.cursor.path, offset: offset + 1 } };
}
