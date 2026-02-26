/**
 * Type inference for math editor expressions.
 *
 * Parses a flat MathRow into binding groups (separated by \text{and})
 * and produces a type signature string.
 *
 * Example:
 *   a, b ∈ ℝ  and  f, g : ℝ → ℝ
 *   → {R : Real} -> (a b : Carrier R) -> (f g : Carrier R -> Carrier R) -> ?
 */

import { MathRow, MathNode } from './types';

// ============================================================================
// Public API
// ============================================================================

export function inferTypeSignature(root: MathRow): string | null {
  const segments = splitByAnd(root.children);
  const bindings: Binding[] = [];
  let needsR = false;

  for (const seg of segments) {
    const parsed = parseSegment(seg);
    if (parsed === null) return null; // incomplete input
    bindings.push(parsed);
    if (parsed.usesR) needsR = true;
  }

  if (bindings.length === 0) return null;

  const parts: string[] = [];
  if (needsR) parts.push('{R : Real}');
  for (const b of bindings) {
    parts.push(`(${b.names.join(' ')} : ${b.typeExpr})`);
  }
  parts.push('?');
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

function parseSegment(nodes: MathNode[]): Binding | null {
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

  const typeResult = convertTypeExpr(typeNodes);
  return {
    names,
    typeExpr: typeResult.expr,
    usesR: typeResult.usesR,
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

// ============================================================================
// Type expression conversion
// ============================================================================

interface TypeResult {
  expr: string;
  usesR: boolean;
}

/** Known type mappings from LaTeX symbols to type theory types. */
const TYPE_MAP: Record<string, { type: string; usesR: boolean }> = {
  '\\mathbb{R}': { type: 'Carrier R', usesR: true },
  '\\mathbb{N}': { type: 'Nat', usesR: false },
  '\\mathbb{Z}': { type: 'Int', usesR: false },
};

function convertTypeExpr(nodes: MathNode[]): TypeResult {
  const parts: string[] = [];
  let usesR = false;

  for (let i = 0; i < nodes.length; i++) {
    const n = nodes[i];
    switch (n.tag) {
      case 'Symbol': {
        const mapped = TYPE_MAP[n.value];
        if (mapped) {
          parts.push(mapped.type);
          if (mapped.usesR) usesR = true;
        } else if (n.value === '\\to') {
          parts.push('->');
        } else if (n.value === '\\times') {
          parts.push('×');
        } else {
          parts.push(n.value);
        }
        break;
      }
      case 'Delimiter': {
        const inner = convertTypeExpr(n.inner.children as MathNode[]);
        if (inner.usesR) usesR = true;
        parts.push(`(${inner.expr})`);
        break;
      }
      case 'Sub': {
        // Subscripted type like T_n
        const base = convertTypeExpr(n.base.children as MathNode[]);
        const sub = rowToSimpleString(n.sub);
        if (base.usesR) usesR = true;
        parts.push(sub ? `${base.expr}${sub}` : base.expr);
        break;
      }
      case 'Frac': {
        // Unlikely in type position, but handle gracefully
        const numer = convertTypeExpr(n.numer.children as MathNode[]);
        const denom = convertTypeExpr(n.denom.children as MathNode[]);
        if (numer.usesR) usesR = true;
        if (denom.usesR) usesR = true;
        parts.push(`(${numer.expr} / ${denom.expr})`);
        break;
      }
      default:
        // Hole, BigOp, Accent, etc. — skip or render as ?
        if (n.tag === 'Hole') {
          parts.push('?');
        }
        break;
    }
  }

  // Join: spaces around ->, otherwise concatenate
  const expr = joinTypeParts(parts);
  return { expr, usesR };
}

/** Join type parts with proper spacing around arrows. */
function joinTypeParts(parts: string[]): string {
  if (parts.length === 0) return '?';

  const result: string[] = [];
  for (let i = 0; i < parts.length; i++) {
    const p = parts[i];
    if (p === '->') {
      result.push(' -> ');
    } else if (i > 0 && result.length > 0 && !result[result.length - 1].endsWith(' ')) {
      // Don't add space if previous ended with space (arrow)
      // Concatenate type fragments: "Carrier" + " " + "R" → "Carrier R"
      // But "Carrier R" is already one token from TYPE_MAP
      result.push(' ');
      result.push(p);
    } else {
      result.push(p);
    }
  }
  return result.join('');
}
