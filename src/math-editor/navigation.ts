/**
 * Cursor navigation through the math AST.
 *
 * Every compound node has an ordered list of "slots" (named child MathRows).
 * The cursor navigates by entering/exiting these slots.
 */

import { MathNode, MathRow, RowPath, RowPathSegment, CursorState, MathEditorState } from './types';

// ============================================================================
// Slot info
// ============================================================================

export interface SlotInfo {
  readonly name: string;
}

/** Returns the ordered navigable slots for a node. */
export function getSlots(node: MathNode): readonly SlotInfo[] {
  switch (node.tag) {
    case 'Frac':
      return [{ name: 'numer' }, { name: 'denom' }];
    case 'Sub':
      return [{ name: 'base' }, { name: 'sub' }];
    case 'Sup':
      return [{ name: 'base' }, { name: 'sup' }];
    case 'SubSup':
      return [{ name: 'base' }, { name: 'sub' }, { name: 'sup' }];
    case 'BigOp': {
      const slots: SlotInfo[] = [];
      if (node.below !== null) slots.push({ name: 'below' });
      if (node.above !== null) slots.push({ name: 'above' });
      slots.push({ name: 'body' });
      return slots;
    }
    case 'Accent':
      return [{ name: 'body' }];
    case 'Delimiter':
      return [{ name: 'inner' }];
    case 'Symbol':
    case 'Hole':
    case 'Text':
      return [];
  }
}

/** Gets the MathRow for a named slot on a node. */
export function getSlotRow(node: MathNode, slotName: string): MathRow | null {
  switch (node.tag) {
    case 'Frac':
      if (slotName === 'numer') return node.numer;
      if (slotName === 'denom') return node.denom;
      return null;
    case 'Sub':
      if (slotName === 'base') return node.base;
      if (slotName === 'sub') return node.sub;
      return null;
    case 'Sup':
      if (slotName === 'base') return node.base;
      if (slotName === 'sup') return node.sup;
      return null;
    case 'SubSup':
      if (slotName === 'base') return node.base;
      if (slotName === 'sub') return node.sub;
      if (slotName === 'sup') return node.sup;
      return null;
    case 'BigOp':
      if (slotName === 'below') return node.below;
      if (slotName === 'above') return node.above;
      if (slotName === 'body') return node.body;
      return null;
    case 'Accent':
      if (slotName === 'body') return node.body;
      return null;
    case 'Delimiter':
      if (slotName === 'inner') return node.inner;
      return null;
    default:
      return null;
  }
}

// ============================================================================
// Path resolution
// ============================================================================

/** Resolve a RowPath to the actual MathRow in the tree. */
export function resolveRow(root: MathRow, path: RowPath): MathRow {
  let current = root;
  for (const seg of path) {
    const node = current.children.find(c => c.id === seg.nodeId);
    if (!node) throw new Error(`Node ${seg.nodeId} not found in row`);
    const slotRow = getSlotRow(node, seg.slot);
    if (!slotRow) throw new Error(`Slot '${seg.slot}' not found on ${node.tag}`);
    current = slotRow;
  }
  return current;
}

/** Find the index of a node (by id) within a MathRow's children. Returns -1 if not found. */
export function findChildIndex(row: MathRow, nodeId: number): number {
  return row.children.findIndex(c => c.id === nodeId);
}

// ============================================================================
// moveRight
// ============================================================================

export function moveRight(state: MathEditorState): MathEditorState {
  const row = resolveRow(state.root, state.cursor.path);
  const offset = state.cursor.offset;

  // Case 1: Not at end of row — look at the node to the right
  if (offset < row.children.length) {
    const rightNode = row.children[offset];
    const slots = getSlots(rightNode);

    if (slots.length > 0) {
      // Enter first slot at offset 0
      const firstSlot = slots[0];
      const newPath: RowPath = [...state.cursor.path, { nodeId: rightNode.id, slot: firstSlot.name }];
      return { ...state, cursor: { path: newPath, offset: 0 } };
    } else {
      // Leaf — skip over it
      return { ...state, cursor: { path: state.cursor.path, offset: offset + 1 } };
    }
  }

  // Case 2: At end of row — pop up to parent
  if (state.cursor.path.length === 0) {
    return state; // At root end, do nothing
  }

  const parentPath = state.cursor.path.slice(0, -1);
  const lastSeg = state.cursor.path[state.cursor.path.length - 1];

  const parentRow = resolveRow(state.root, parentPath);
  const parentNode = parentRow.children.find(c => c.id === lastSeg.nodeId);
  if (!parentNode) return state;

  const slots = getSlots(parentNode);
  const currentSlotIndex = slots.findIndex(s => s.name === lastSeg.slot);

  if (currentSlotIndex < slots.length - 1) {
    // Move to next sibling slot at offset 0
    const nextSlot = slots[currentSlotIndex + 1];
    const newPath: RowPath = [...parentPath, { nodeId: parentNode.id, slot: nextSlot.name }];
    return { ...state, cursor: { path: newPath, offset: 0 } };
  } else {
    // Exiting compound node — cursor after it in parent row
    const parentNodeIndex = findChildIndex(parentRow, lastSeg.nodeId);
    const newState = { ...state, cursor: { path: parentPath, offset: parentNodeIndex + 1 } };
    // If we landed at end of parent row and still inside a compound, keep bubbling
    if (parentNodeIndex + 1 >= parentRow.children.length && parentPath.length > 0) {
      return moveRight(newState);
    }
    return newState;
  }
}

// ============================================================================
// moveLeft
// ============================================================================

export function moveLeft(state: MathEditorState): MathEditorState {
  const row = resolveRow(state.root, state.cursor.path);
  const offset = state.cursor.offset;

  // Case 1: Not at start — look at node to the left
  if (offset > 0) {
    const leftNode = row.children[offset - 1];
    const slots = getSlots(leftNode);

    if (slots.length > 0) {
      // Enter last slot, cursor at end (but before trailing Holes)
      const lastSlot = slots[slots.length - 1];
      const slotRow = getSlotRow(leftNode, lastSlot.name)!;
      const newPath: RowPath = [...state.cursor.path, { nodeId: leftNode.id, slot: lastSlot.name }];
      return { ...state, cursor: { path: newPath, offset: clampOffsetBeforeHoles(slotRow.children.length, slotRow) } };
    } else {
      // Leaf — skip over it
      return { ...state, cursor: { path: state.cursor.path, offset: offset - 1 } };
    }
  }

  // Case 2: At start of row — pop up to parent
  if (state.cursor.path.length === 0) {
    return state; // At root start, do nothing
  }

  const parentPath = state.cursor.path.slice(0, -1);
  const lastSeg = state.cursor.path[state.cursor.path.length - 1];

  const parentRow = resolveRow(state.root, parentPath);
  const parentNode = parentRow.children.find(c => c.id === lastSeg.nodeId);
  if (!parentNode) return state;

  const slots = getSlots(parentNode);
  const currentSlotIndex = slots.findIndex(s => s.name === lastSeg.slot);

  if (currentSlotIndex > 0) {
    // Move to previous sibling slot, cursor at end (but before trailing Holes)
    const prevSlot = slots[currentSlotIndex - 1];
    const prevRow = getSlotRow(parentNode, prevSlot.name)!;
    const newPath: RowPath = [...parentPath, { nodeId: parentNode.id, slot: prevSlot.name }];
    return { ...state, cursor: { path: newPath, offset: clampOffsetBeforeHoles(prevRow.children.length, prevRow) } };
  } else {
    // Exiting compound node to the left — cursor before it in parent row
    const parentNodeIndex = findChildIndex(parentRow, lastSeg.nodeId);
    return { ...state, cursor: { path: parentPath, offset: parentNodeIndex } };
  }
}

// ============================================================================
// moveUp / moveDown — vertical navigation between stacked slots
// ============================================================================

/**
 * Vertical layout map: for each node type + current slot, what slot is above/below.
 * null means "no vertical neighbor in that direction".
 */
interface VerticalNeighbors {
  above: string | null;
  below: string | null;
}

function getVerticalNeighbors(node: MathNode, currentSlot: string): VerticalNeighbors {
  switch (node.tag) {
    case 'Frac':
      if (currentSlot === 'numer') return { above: null, below: 'denom' };
      if (currentSlot === 'denom') return { above: 'numer', below: null };
      return { above: null, below: null };
    case 'Sub':
      if (currentSlot === 'base') return { above: null, below: 'sub' };
      if (currentSlot === 'sub') return { above: 'base', below: null };
      return { above: null, below: null };
    case 'Sup':
      if (currentSlot === 'base') return { above: 'sup', below: null };
      if (currentSlot === 'sup') return { above: null, below: 'base' };
      return { above: null, below: null };
    case 'SubSup':
      if (currentSlot === 'base') return { above: 'sup', below: 'sub' };
      if (currentSlot === 'sub') return { above: 'base', below: null };
      if (currentSlot === 'sup') return { above: null, below: 'base' };
      return { above: null, below: null };
    case 'BigOp':
      if (currentSlot === 'below') return { above: node.above !== null ? 'above' : null, below: null };
      if (currentSlot === 'above') return { above: null, below: node.below !== null ? 'below' : null };
      if (currentSlot === 'body') return { above: null, below: null };
      return { above: null, below: null };
    default:
      return { above: null, below: null };
  }
}

/**
 * For entering a compound node from a parent row: which slot to enter
 * when pressing up/down while adjacent to the node.
 */
function getEntrySlotVertical(node: MathNode, direction: 'up' | 'down'): string | null {
  switch (node.tag) {
    case 'Frac':
      return direction === 'up' ? 'numer' : 'denom';
    case 'Sub':
      return direction === 'down' ? 'sub' : null;
    case 'Sup':
      return direction === 'up' ? 'sup' : null;
    case 'SubSup':
      return direction === 'up' ? 'sup' : 'sub';
    case 'BigOp':
      if (direction === 'up' && node.above !== null) return 'above';
      if (direction === 'down' && node.below !== null) return 'below';
      return null;
    default:
      return null;
  }
}

export function moveUp(state: MathEditorState): MathEditorState {
  return moveVertical(state, 'up');
}

export function moveDown(state: MathEditorState): MathEditorState {
  return moveVertical(state, 'down');
}

function moveVertical(state: MathEditorState, direction: 'up' | 'down'): MathEditorState {
  // Case 1: Walk up the path hierarchy looking for a vertical neighbor.
  // e.g. cursor inside Delimiter.inner inside Frac.numer — Delimiter has no
  // vertical neighbor, so bubble up to Frac which has numer↔denom.
  let currentPath = state.cursor.path;

  while (currentPath.length > 0) {
    const lastSeg = currentPath[currentPath.length - 1];
    const parentPath = currentPath.slice(0, -1);
    const parentRow = resolveRow(state.root, parentPath);
    const parentNode = parentRow.children.find(c => c.id === lastSeg.nodeId);

    if (parentNode) {
      const neighbors = getVerticalNeighbors(parentNode, lastSeg.slot);
      const targetSlot = direction === 'up' ? neighbors.above : neighbors.below;

      if (targetSlot) {
        const targetRow = getSlotRow(parentNode, targetSlot);
        if (targetRow) {
          // Move to the same offset (clamped, but before trailing Holes)
          const newOffset = clampOffsetBeforeHoles(state.cursor.offset, targetRow);
          return {
            ...state,
            cursor: {
              path: [...parentPath, { nodeId: parentNode.id, slot: targetSlot }],
              offset: newOffset,
            },
          };
        }
      }
    }

    // No vertical neighbor at this level — try parent
    currentPath = parentPath;
  }

  // Case 2: Cursor in a row (root or parent) — look at adjacent compound nodes
  const row = resolveRow(state.root, state.cursor.path);
  const offset = state.cursor.offset;

  // Check the node at cursor position (to the right)
  if (offset < row.children.length) {
    const rightNode = row.children[offset];
    const entrySlot = getEntrySlotVertical(rightNode, direction);
    if (entrySlot) {
      const targetRow = getSlotRow(rightNode, entrySlot);
      if (targetRow) {
        return {
          ...state,
          cursor: {
            path: [...state.cursor.path, { nodeId: rightNode.id, slot: entrySlot }],
            offset: 0,
          },
        };
      }
    }
  }

  // Check the node to the left of cursor
  if (offset > 0) {
    const leftNode = row.children[offset - 1];
    const entrySlot = getEntrySlotVertical(leftNode, direction);
    if (entrySlot) {
      const targetRow = getSlotRow(leftNode, entrySlot);
      if (targetRow) {
        return {
          ...state,
          cursor: {
            path: [...state.cursor.path, { nodeId: leftNode.id, slot: entrySlot }],
            offset: clampOffsetBeforeHoles(targetRow.children.length, targetRow),
          },
        };
      }
    }
  }

  return state;
}

// ============================================================================
// Utilities
// ============================================================================

/**
 * When entering a row, avoid placing cursor after trailing Holes.
 * Holes are empty placeholders — the cursor should be positioned before them
 * so typing replaces them naturally.
 */
export function clampOffsetBeforeHoles(offset: number, row: MathRow): number {
  let effectiveEnd = row.children.length;
  while (effectiveEnd > 0 && row.children[effectiveEnd - 1].tag === 'Hole') {
    effectiveEnd--;
  }
  return Math.min(offset, effectiveEnd);
}

export function rowPathEquals(a: RowPath, b: RowPath): boolean {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i++) {
    if (a[i].nodeId !== b[i].nodeId || a[i].slot !== b[i].slot) return false;
  }
  return true;
}

/** Exit the current compound node, placing cursor after it in the parent row. */
export function exitCompound(state: MathEditorState): MathEditorState {
  if (state.cursor.path.length === 0) return state; // Already at root

  const parentPath = state.cursor.path.slice(0, -1);
  const lastSeg = state.cursor.path[state.cursor.path.length - 1];
  const parentRow = resolveRow(state.root, parentPath);
  const parentNodeIndex = findChildIndex(parentRow, lastSeg.nodeId);

  return { ...state, cursor: { path: parentPath, offset: parentNodeIndex + 1 } };
}
