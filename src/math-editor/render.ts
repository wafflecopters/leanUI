/**
 * LaTeX rendering for the structured math editor.
 *
 * Walks the MathNode tree and produces a LaTeX string with:
 * - \htmlId{n-ID}{...} wrappers for click interactivity
 * - A cursor marker at the current position
 * - Hole placeholders rendered as grey squares
 */

import { MathNode, MathRow, MathEditorState, CursorState, RowPath } from './types';
import { rowPathEquals } from './navigation';

// ============================================================================
// Cursor rendering
// ============================================================================

// Cursor: a thin vertical bar aligned with surrounding text.
// \rule[-depth]{width}{height} — the negative depth extends below the baseline so the bar
// doesn't float above the text.  0.15em below + 1.05em tall ≈ matches a capital letter.
const CURSOR_LATEX = '\\htmlId{cursor}{\\textcolor{#4488ff}{\\rule[-0.15em]{1.5px}{1.05em}}}';
const HOLE_LATEX = '\\textcolor{#666}{\\square}';

// ============================================================================
// Main render function
// ============================================================================

export function renderToLatex(state: MathEditorState): string {
  return renderRow(state.root, state.cursor, []);
}

function renderRow(row: MathRow, cursor: CursorState, currentPath: RowPath): string {
  const isCursorRow = rowPathEquals(cursor.path, currentPath);
  const parts: string[] = [];

  for (let i = 0; i < row.children.length; i++) {
    // Insert cursor before this child if cursor is at this offset
    if (isCursorRow && cursor.offset === i) {
      parts.push(CURSOR_LATEX);
    }
    parts.push(renderNode(row.children[i], cursor, currentPath));
  }

  // Cursor at end of row
  if (isCursorRow && cursor.offset === row.children.length) {
    parts.push(CURSOR_LATEX);
  }

  const result = parts.join('');
  // Safety: never produce completely empty content inside \frac{}{} or similar.
  // An empty string inside a KaTeX command arg can cause parse failures.
  if (result === '') return '\\vphantom{0}';
  return result;
}

function renderNode(node: MathNode, cursor: CursorState, currentPath: RowPath): string {
  const inner = renderNodeInner(node, cursor, currentPath);
  return `\\htmlId{n-${node.id}}{${inner}}`;
}

function renderNodeInner(node: MathNode, cursor: CursorState, currentPath: RowPath): string {
  switch (node.tag) {
    case 'Symbol':
      return renderSymbol(node.value);

    case 'Hole':
      return HOLE_LATEX;

    case 'Frac': {
      const numer = renderRow(node.numer, cursor, [...currentPath, { nodeId: node.id, slot: 'numer' }]);
      const denom = renderRow(node.denom, cursor, [...currentPath, { nodeId: node.id, slot: 'denom' }]);
      return `\\frac{${numer}}{${denom}}`;
    }

    case 'Sub': {
      const base = renderRow(node.base, cursor, [...currentPath, { nodeId: node.id, slot: 'base' }]);
      const sub = renderRow(node.sub, cursor, [...currentPath, { nodeId: node.id, slot: 'sub' }]);
      return `{${base}}_{${sub}}`;
    }

    case 'Sup': {
      const base = renderRow(node.base, cursor, [...currentPath, { nodeId: node.id, slot: 'base' }]);
      const sup = renderRow(node.sup, cursor, [...currentPath, { nodeId: node.id, slot: 'sup' }]);
      return `{${base}}^{${sup}}`;
    }

    case 'SubSup': {
      const base = renderRow(node.base, cursor, [...currentPath, { nodeId: node.id, slot: 'base' }]);
      const sub = renderRow(node.sub, cursor, [...currentPath, { nodeId: node.id, slot: 'sub' }]);
      const sup = renderRow(node.sup, cursor, [...currentPath, { nodeId: node.id, slot: 'sup' }]);
      return `{${base}}_{${sub}}^{${sup}}`;
    }

    case 'BigOp': {
      let result = `\\${node.operator}`;
      if (node.below !== null) {
        const below = renderRow(node.below, cursor, [...currentPath, { nodeId: node.id, slot: 'below' }]);
        result += `_{${below}}`;
      }
      if (node.above !== null) {
        const above = renderRow(node.above, cursor, [...currentPath, { nodeId: node.id, slot: 'above' }]);
        result += `^{${above}}`;
      }
      return result;
    }

    case 'Accent': {
      const body = renderRow(node.body, cursor, [...currentPath, { nodeId: node.id, slot: 'body' }]);
      switch (node.accent) {
        case 'vec': return `\\vec{${body}}`;
        case 'hat': return `\\hat{${body}}`;
        case 'bar': return `\\bar{${body}}`;
        case 'tilde': return `\\tilde{${body}}`;
        case 'dot': return `\\dot{${body}}`;
        case 'overline': return `\\overline{${body}}`;
      }
    }

    case 'Delimiter': {
      const inner = renderRow(node.inner, cursor, [...currentPath, { nodeId: node.id, slot: 'inner' }]);
      return `\\left${node.open}${inner}\\right${node.close}`;
    }

    case 'Text':
      return `\\;\\text{${node.content}}\\;`;
  }
}

/** Render a symbol value — most are passed through as-is. */
function renderSymbol(value: string): string {
  // Single chars just pass through: 'x', '+', '2', etc.
  // LaTeX commands like '\alpha', '\in' also pass through
  // Operators that need spacing
  if (value === '+' || value === '-' || value === '=') {
    return ` ${value} `;
  }
  if (value === '\\in' || value === '\\to' || value === '\\leq' || value === '\\geq' ||
      value === '\\neq' || value === '\\subset' || value === '\\subseteq' ||
      value === '\\implies' || value === '\\iff') {
    return ` ${value} `;
  }
  return value;
}

// ============================================================================
// Render without cursor (for static display)
// ============================================================================

export function renderStaticLatex(root: MathRow): string {
  return renderRowStatic(root);
}

function renderRowStatic(row: MathRow): string {
  const result = row.children.map(c => renderNodeStatic(c)).join('');
  if (result === '') return '\\vphantom{0}';
  return result;
}

function renderNodeStatic(node: MathNode): string {
  switch (node.tag) {
    case 'Symbol':
      return renderSymbol(node.value);
    case 'Hole':
      return HOLE_LATEX;
    case 'Frac':
      return `\\frac{${renderRowStatic(node.numer)}}{${renderRowStatic(node.denom)}}`;
    case 'Sub':
      return `{${renderRowStatic(node.base)}}_{${renderRowStatic(node.sub)}}`;
    case 'Sup':
      return `{${renderRowStatic(node.base)}}^{${renderRowStatic(node.sup)}}`;
    case 'SubSup':
      return `{${renderRowStatic(node.base)}}_{${renderRowStatic(node.sub)}}^{${renderRowStatic(node.sup)}}`;
    case 'BigOp': {
      let r = `\\${node.operator}`;
      if (node.below !== null) r += `_{${renderRowStatic(node.below)}}`;
      if (node.above !== null) r += `^{${renderRowStatic(node.above)}}`;
      return r;
    }
    case 'Accent': {
      const body = renderRowStatic(node.body);
      switch (node.accent) {
        case 'vec': return `\\vec{${body}}`;
        case 'hat': return `\\hat{${body}}`;
        case 'bar': return `\\bar{${body}}`;
        case 'tilde': return `\\tilde{${body}}`;
        case 'dot': return `\\dot{${body}}`;
        case 'overline': return `\\overline{${body}}`;
      }
    }
    case 'Delimiter':
      return `\\left${node.open}${renderRowStatic(node.inner)}\\right${node.close}`;
    case 'Text':
      return `\\;\\text{${node.content}}\\;`;
  }
}
