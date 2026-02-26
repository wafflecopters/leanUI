/**
 * Type inference for math editor expressions.
 *
 * Parses a flat MathRow into binding groups (separated by \text{and})
 * and produces a type signature string using the syntax registry for
 * expression conversion.
 *
 * Example:
 *   a, b ∈ ℝ  and  f, g : ℝ → ℝ
 *   → {R : Real} -> (a b : Carrier R) -> (f g : Carrier R -> Carrier R) -> ?
 *
 *   Let a, b ∈ ℝ, then a + b = b + a
 *   → {R : Real} -> (a b : Carrier R) -> Equal (radd a b) (rsub a b)
 */

import { MathRow, MathNode } from './types';
import { SyntaxRegistry, createDefaultRegistry, convertToSource } from './syntax-registry';

// ============================================================================
// Public API
// ============================================================================

/** Leading text tokens that are stripped (case-insensitive). */
const LEADING_TOKENS = new Set(['if', 'let', 'assume']);

/** Lazily-initialized default registry. */
let _defaultRegistry: SyntaxRegistry | null = null;
function getDefaultRegistry(): SyntaxRegistry {
  if (!_defaultRegistry) _defaultRegistry = createDefaultRegistry();
  return _defaultRegistry;
}

export function inferTypeSignature(root: MathRow, registry?: SyntaxRegistry): string | null {
  const reg = registry ?? getDefaultRegistry();

  // 1. Strip leading If/Let/Assume text nodes
  const children = stripLeadingTokens(root.children);

  // 2. Split by body separator (then / . Then / , then)
  const { bindings: bindingNodes, body: bodyNodes } = splitByBodySeparator(children);

  // 3. Split bindings by "and"
  const segments = splitByAnd(bindingNodes);
  const bindings: Binding[] = [];
  let needsR = false;

  for (const seg of segments) {
    const parsed = parseSegment(seg, reg);
    if (parsed === null) return null; // incomplete input
    bindings.push(parsed);
    if (parsed.usesR) needsR = true;
  }

  if (bindings.length === 0) return null;

  // 4. Convert body if present
  let bodyExpr = '?';
  if (bodyNodes !== null && bodyNodes.length > 0) {
    const bodyResult = convertToSource(reg, bodyNodes);
    bodyExpr = bodyResult.source;
    if (bodyResult.needsR) needsR = true;
  }

  // 5. Assemble
  const parts: string[] = [];
  if (needsR) parts.push('{R : Real}');
  for (const b of bindings) {
    parts.push(`(${b.names.join(' ')} : ${b.typeExpr})`);
  }
  parts.push(bodyExpr);
  return parts.join(' -> ');
}

// ============================================================================
// Internal types
// ============================================================================

interface Binding {
  names: string[];
  typeExpr: string;
  usesR: boolean;
}

// ============================================================================
// Leading token stripping
// ============================================================================

function stripLeadingTokens(children: readonly MathNode[]): MathNode[] {
  let start = 0;
  while (start < children.length) {
    const c = children[start];
    if (c.tag === 'Text' && LEADING_TOKENS.has(c.content.toLowerCase())) {
      start++;
    } else {
      break;
    }
  }
  return start === 0 ? [...children] : children.slice(start);
}

// ============================================================================
// Body separator — split bindings from conclusion
// ============================================================================

interface BodySplit {
  bindings: MathNode[];
  body: MathNode[] | null;
}

/**
 * Scan for a body separator: `then`, `, then`, `. Then`, `. then`.
 * Returns bindings (before separator) and body (after separator).
 */
function splitByBodySeparator(children: MathNode[]): BodySplit {
  for (let i = 0; i < children.length; i++) {
    const c = children[i];

    // Pattern: Text('then') alone
    if (c.tag === 'Text' && c.content.toLowerCase() === 'then') {
      return { bindings: children.slice(0, i), body: children.slice(i + 1) };
    }

    // Pattern: Symbol(',') or Symbol('.') followed by Text('then')
    if ((c.tag === 'Symbol' && (c.value === ',' || c.value === '.')) &&
        i + 1 < children.length) {
      const next = children[i + 1];
      if (next.tag === 'Text' && next.content.toLowerCase() === 'then') {
        return { bindings: children.slice(0, i), body: children.slice(i + 2) };
      }
    }
  }

  return { bindings: children, body: null };
}

// ============================================================================
// Segment splitting — split top-level children by Text('and')
// ============================================================================

function splitByAnd(children: readonly MathNode[]): MathNode[][] {
  const segments: MathNode[][] = [];
  let current: MathNode[] = [];

  for (const child of children) {
    if (child.tag === 'Text' && child.content.toLowerCase() === 'and') {
      if (current.length > 0) segments.push(current);
      current = [];
    } else {
      current.push(child);
    }
  }
  if (current.length > 0) segments.push(current);
  return segments;
}

// ============================================================================
// Segment parsing — find relation symbol, extract names + type
// ============================================================================

function parseSegment(nodes: MathNode[], registry: SyntaxRegistry): Binding | null {
  // Find the relation symbol: \in or :
  const relIndex = nodes.findIndex(n =>
    n.tag === 'Symbol' && (n.value === '\\in' || n.value === ':')
  );
  if (relIndex < 0) return null;

  const nameNodes = nodes.slice(0, relIndex);
  const typeNodes = nodes.slice(relIndex + 1);

  if (typeNodes.length === 0) return null; // incomplete: "a ∈" with nothing after

  const names = extractNames(nameNodes);
  if (names.length === 0) return null;

  const typeResult = convertToSource(registry, typeNodes);
  return {
    names,
    typeExpr: typeResult.source,
    usesR: typeResult.needsR,
  };
}

// ============================================================================
// Name extraction — pull variable names from before the relation
// ============================================================================

function extractNames(nodes: MathNode[]): string[] {
  const names: string[] = [];
  for (const n of nodes) {
    if (n.tag === 'Symbol') {
      // Skip commas and whitespace-like symbols
      if (n.value === ',' || n.value === ' ') continue;
      // Single-char identifiers and multi-char (Greek, etc.)
      names.push(n.value);
    }
    // Sub nodes: extract base as a subscripted name
    if (n.tag === 'Sub') {
      const baseName = rowToSimpleString(n.base);
      const subName = rowToSimpleString(n.sub);
      if (baseName && subName) {
        names.push(`${baseName}${subName}`);
      }
    }
  }
  return names;
}

/** Convert a simple row (only symbols) to a plain string, or null if complex. */
function rowToSimpleString(row: MathRow): string | null {
  if (row.children.length === 0) return null;
  const parts: string[] = [];
  for (const c of row.children) {
    if (c.tag === 'Symbol') {
      parts.push(c.value);
    } else {
      return null;
    }
  }
  return parts.join('');
}
