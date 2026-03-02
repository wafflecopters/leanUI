/**
 * Type Signature Grammar
 * ======================
 *
 * This file defines the complete grammar for converting visual math (MathNode
 * trees from the structured editor) into TT type signature strings. All
 * structural rules live here; expression-level patterns (like `a + b → radd a b`)
 * live in syntax-registry.ts.
 *
 * Grammar:
 *
 *   Signature  ::= Preamble? Bindings Separator? Body?
 *   Preamble   ::= ('If' | 'Let' | 'Assume')+          -- case-insensitive, stripped
 *   Bindings   ::= Binding ('and' Binding)*
 *   Binding    ::= Quantifier? Names Relation TypeExpr   -- named: "∀ a, b ∈ ℝ"
 *                | Quantifier? TypeExpr                   -- anonymous: "a = b"
 *   Quantifier ::= '∀' | 'forall' | 'for all'           -- stripped at binder start
 *
 *   Keywords ('If', 'and', 'then', 'forall') can be entered as:
 *     - A Text node (via text mode: space + letters + space)
 *     - Consecutive single-char Symbol nodes (typed directly as characters)
 *   Names      ::= Name (',' Name)*
 *   Name       ::= symbol | symbol_subscript              -- e.g., x or x₀
 *   Relation   ::= '∈' | ':'
 *   Separator  ::= 'then' | ',' 'then' | '.' 'then'     -- case-insensitive
 *   Body       ::= Expr                                   -- conclusion
 *   Expr       ::= <see syntax-registry.ts>               -- pattern-matched to TT
 *
 * Examples:
 *   ∀ n ∈ ℕ, n ≥ 0
 *   → (n : Nat) -> rge n (rzero R)
 *
 *   Let a, b ∈ ℝ and f : ℝ → ℝ, then f(a + b) = f(a) + f(b)
 *   → {R : Real} -> (a b : Carrier R) -> (f : Carrier R -> Carrier R) -> Equal ...
 *
 *   ∀ a ∈ ℝ and ∀ b ∈ ℝ, then a + b = b + a
 *   → {R : Real} -> (a : Carrier R) -> (b : Carrier R) -> Equal ...
 */

import { MathRow, MathNode } from './types';
import { SyntaxRegistry, createDefaultRegistry, convertToSource, lookupSymbol } from './syntax-registry';

// ============================================================================
// Grammar Rules — all structural tokens/keywords defined here
// ============================================================================

/** Preamble: leading text tokens stripped from the start (case-insensitive). */
const PREAMBLE_TOKENS = new Set(['if', 'let', 'assume']);

/** Quantifier: stripped at the start of each binder segment (case-insensitive). */
const QUANTIFIER_SYMBOLS = new Set(['\\forall']);
const QUANTIFIER_TEXTS = new Set(['forall']);

/** Segment separator: splits bindings into individual binder groups. */
const SEGMENT_SEPARATOR = 'and';

/** Relation symbols: separate names from their type in a binding. */
const RELATION_SYMBOLS = new Set(['\\in', ':']);

/**
 * Try to match consecutive single-character Symbol nodes at `startIdx`
 * against a set of known words (case-insensitive).
 * Returns the number of Symbol nodes consumed, or 0 if no match.
 */
function tryMatchSymbolWord(children: readonly MathNode[], startIdx: number, words: Set<string>): number {
  let word = '';
  for (let i = startIdx; i < children.length; i++) {
    const c = children[i];
    if (c.tag !== 'Symbol' || c.value.length !== 1) break;
    word += c.value;
    if (words.has(word.toLowerCase())) {
      return word.length;
    }
  }
  return 0;
}

/**
 * Check whether a node is a Text node matching a word (case-insensitive),
 * OR a sequence of single-char Symbol nodes spelling the word.
 * Returns number of nodes consumed (1 for Text, N for Symbols), or 0 for no match.
 */
function matchesWord(children: readonly MathNode[], idx: number, word: string): number {
  if (idx >= children.length) return 0;
  const c = children[idx];
  // Text node match
  if (c.tag === 'Text' && c.content.toLowerCase() === word) return 1;
  // Symbol sequence match
  return tryMatchSymbolWord(children, idx, new Set([word]));
}

/**
 * Strip a leading quantifier (∀ / forall / for all) from a segment.
 * Returns the remaining nodes after the quantifier.
 */
function stripQuantifier(nodes: MathNode[]): MathNode[] {
  if (nodes.length === 0) return nodes;
  const first = nodes[0];

  // Symbol('\\forall')
  if (first.tag === 'Symbol' && QUANTIFIER_SYMBOLS.has(first.value)) {
    return nodes.slice(1);
  }

  // Text('forall') or Symbol sequence 'f','o','r','a','l','l' — case-insensitive
  const forallLen = matchesWord(nodes, 0, 'forall');
  if (forallLen > 0) return nodes.slice(forallLen);

  // Text('for') followed by Text('all') — case-insensitive
  if (first.tag === 'Text' && first.content.toLowerCase() === 'for' && nodes.length >= 2) {
    const second = nodes[1];
    if (second.tag === 'Text' && second.content.toLowerCase() === 'all') {
      return nodes.slice(2);
    }
  }

  return nodes;
}

// ============================================================================
// Public API
// ============================================================================

/** Lazily-initialized default registry. */
let _defaultRegistry: SyntaxRegistry | null = null;
function getDefaultRegistry(): SyntaxRegistry {
  if (!_defaultRegistry) _defaultRegistry = createDefaultRegistry();
  return _defaultRegistry;
}

export function inferTypeSignature(root: MathRow, registry?: SyntaxRegistry): string | null {
  const parts = inferTypeSignatureParts(root, registry);
  return parts ? parts.join(' -> ') : null;
}

/**
 * Returns the type signature as an array of Pi-spine segments,
 * e.g. ['{R : Real}', '(a : Carrier R)', '?'].
 * Each segment is one binder or the body. The caller can join with ' -> '
 * or render each segment separately for wrapping.
 */
export function inferTypeSignatureParts(root: MathRow, registry?: SyntaxRegistry): string[] | null {
  const reg = registry ?? getDefaultRegistry();

  // 1. Strip leading If/Let/Assume text nodes
  const children = stripLeadingTokens(root.children);

  // 2. Split by body separator (then / . Then / , then)
  const { bindings: bindingNodes, body: bodyNodes } = splitByBodySeparator(children);

  // 3. Split bindings by "and"
  const segments = splitByAnd(bindingNodes);
  const bindings: Binding[] = [];
  let needsR = false;

  // Parse each segment as a binding. Strip leading quantifier (∀/forall/for all)
  // from each segment. Segments without ∈/: become anonymous hypothesis bindings.
  for (const rawSeg of segments) {
    const seg = stripQuantifier(rawSeg);
    const parsed = parseSegment(seg, reg);
    if (parsed !== null) {
      bindings.push(parsed);
      if (parsed.usesR) needsR = true;
    } else if (seg.length > 0 && !hasRelationSymbol(seg)) {
      // No relation symbol → anonymous hypothesis (e.g. "lim f(x) = L")
      const typeResult = convertToSource(reg, seg);
      bindings.push({ names: ['_'], typeExpr: typeResult.source, usesR: typeResult.needsR });
      if (typeResult.needsR) needsR = true;
    }
    // Has relation symbol but incomplete (e.g. "a ∈") → skip, user is mid-typing
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
  return parts;
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
    if (c.tag === 'Text' && PREAMBLE_TOKENS.has(c.content.toLowerCase())) {
      start++;
      continue;
    }
    // Also try matching consecutive Symbol nodes spelling a preamble word
    const consumed = tryMatchSymbolWord(children, start, PREAMBLE_TOKENS);
    if (consumed > 0) {
      start += consumed;
      continue;
    }
    break;
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
 * Also recognizes consecutive Symbol nodes spelling "then".
 * Returns bindings (before separator) and body (after separator).
 */
function splitByBodySeparator(children: MathNode[]): BodySplit {
  for (let i = 0; i < children.length; i++) {
    const c = children[i];

    // Pattern: Text('then') alone
    if (c.tag === 'Text' && c.content.toLowerCase() === 'then') {
      return { bindings: children.slice(0, i), body: children.slice(i + 1) };
    }

    // Pattern: Symbol sequence spelling "then"
    const thenLen = matchesWord(children, i, 'then');
    if (thenLen > 1) { // >1 to require Symbol sequence, not a single node
      return { bindings: children.slice(0, i), body: children.slice(i + thenLen) };
    }

    // Pattern: Symbol(',') or Symbol('.') followed by Text('then') or Symbol-sequence 'then'
    if (c.tag === 'Symbol' && (c.value === ',' || c.value === '.')) {
      const afterLen = matchesWord(children, i + 1, 'then');
      if (afterLen > 0) {
        return { bindings: children.slice(0, i), body: children.slice(i + 1 + afterLen) };
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
  const andSet = new Set([SEGMENT_SEPARATOR]);

  let i = 0;
  while (i < children.length) {
    const child = children[i];
    if (child.tag === 'Text' && child.content.toLowerCase() === SEGMENT_SEPARATOR) {
      if (current.length > 0) segments.push(current);
      current = [];
      i++;
    } else {
      // Check for Symbol sequence spelling "and"
      const consumed = tryMatchSymbolWord(children, i, andSet);
      if (consumed > 0) {
        if (current.length > 0) segments.push(current);
        current = [];
        i += consumed;
      } else {
        current.push(child);
        i++;
      }
    }
  }
  if (current.length > 0) segments.push(current);
  return segments;
}

// ============================================================================
// Segment parsing — find relation symbol, extract names + type
// ============================================================================

/** Check if a node list contains a relation symbol (∈ or :) at the top level. */
function hasRelationSymbol(nodes: readonly MathNode[]): boolean {
  return nodes.some(n => n.tag === 'Symbol' && RELATION_SYMBOLS.has(n.value));
}

function parseSegment(nodes: MathNode[], registry: SyntaxRegistry): Binding | null {
  // Find the relation symbol: \in or :
  const relIndex = nodes.findIndex(n =>
    n.tag === 'Symbol' && RELATION_SYMBOLS.has(n.value)
  );
  if (relIndex < 0) return null;

  const nameNodes = nodes.slice(0, relIndex);
  const typeNodes = nodes.slice(relIndex + 1);

  if (typeNodes.length === 0) return null; // incomplete: "a ∈" with nothing after

  const names = extractNames(nameNodes);
  if (names.length === 0) return null;

  // Record types need carrier projection insertion which isn't implemented yet
  checkNotRecordType(typeNodes, registry);

  const typeResult = convertToSource(registry, typeNodes);
  return {
    names,
    typeExpr: typeResult.source,
    usesR: typeResult.needsR,
  };
}

/** Throws if typeNodes resolve to a record type — carrier projection insertion not yet implemented. */
function checkNotRecordType(typeNodes: readonly MathNode[], registry: SyntaxRegistry): void {
  if (typeNodes.length === 1 && typeNodes[0].tag === 'Symbol') {
    const mapped = lookupSymbol(registry, typeNodes[0].value);
    if (mapped?.isRecord) {
      throw new Error(`carrier projection insertion not implemented yet (type '${typeNodes[0].value}' is a record)`);
    }
  }
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
    // Text nodes created by space-triggered text mode (e.g., "n" typed as space-n-space)
    if (n.tag === 'Text') {
      const trimmed = n.content.trim();
      if (trimmed.length > 0) names.push(trimmed);
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
