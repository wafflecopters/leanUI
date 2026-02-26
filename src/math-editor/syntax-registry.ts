/**
 * Syntax Registry — pattern matching on MathNode trees to produce TT source.
 *
 * Each SyntaxEntry defines a visual pattern (matching MathNode trees) and a
 * TT source template (with $name substitution points). The registry converts
 * math editor output to compilable TT source.
 *
 * Patterns compose recursively: `lim_{x→a} f(x) + g(x)` matches the `+`
 * pattern first, then each side recursively matches further patterns.
 */

import { MathNode, MathRow } from './types';

// ============================================================================
// Pattern elements
// ============================================================================

export type PatternElement =
  | { tag: 'literal'; symbol: string }
  | { tag: 'capture'; name: string }
  | { tag: 'bigop'; operator: string; below: PatternElement[] | null; above: PatternElement[] | null }
  | { tag: 'frac'; numer: PatternElement[]; denom: PatternElement[] }
  | { tag: 'delimiter'; open: string; close: string; inner: PatternElement[] }
  | { tag: 'accent'; accent: string; body: PatternElement[] }
  | { tag: 'sub'; base: PatternElement[]; sub: PatternElement[] }
  | { tag: 'sup'; base: PatternElement[]; sup: PatternElement[] };

// Convenience constructors
export const pat = {
  literal: (symbol: string): PatternElement => ({ tag: 'literal', symbol }),
  capture: (name: string): PatternElement => ({ tag: 'capture', name }),
  bigop: (operator: string, below: PatternElement[] | null, above: PatternElement[] | null = null): PatternElement =>
    ({ tag: 'bigop', operator, below, above }),
  frac: (numer: PatternElement[], denom: PatternElement[]): PatternElement =>
    ({ tag: 'frac', numer, denom }),
  delimiter: (open: string, close: string, inner: PatternElement[]): PatternElement =>
    ({ tag: 'delimiter', open, close, inner }),
  accent: (accent: string, body: PatternElement[]): PatternElement =>
    ({ tag: 'accent', accent, body }),
  sub: (base: PatternElement[], sub: PatternElement[]): PatternElement =>
    ({ tag: 'sub', base, sub }),
  sup: (base: PatternElement[], sup: PatternElement[]): PatternElement =>
    ({ tag: 'sup', base, sup }),
};

// ============================================================================
// Syntax entry and registry
// ============================================================================

export interface SyntaxEntry {
  name: string;
  pattern: PatternElement[];
  template: string;
  needsR?: boolean;
  priority: number;
}

export interface SyntaxRegistry {
  entries: SyntaxEntry[];
  symbolMap: Map<string, { source: string; needsR: boolean }>;
  parent?: SyntaxRegistry;
}

// ============================================================================
// Pattern matching
// ============================================================================

export type Bindings = Map<string, MathNode[]>;

/**
 * Match a pattern against a sequence of MathNodes.
 * Returns captured bindings on success, null on failure.
 */
export function matchRow(pattern: PatternElement[], nodes: readonly MathNode[]): Bindings | null {
  const bindings: Bindings = new Map();
  const nodeArr = [...nodes];
  let nodeIdx = 0;

  for (let patIdx = 0; patIdx < pattern.length; patIdx++) {
    const pe = pattern[patIdx];

    switch (pe.tag) {
      case 'literal': {
        if (nodeIdx >= nodeArr.length) return null;
        const node = nodeArr[nodeIdx];
        if (node.tag !== 'Symbol' || node.value !== pe.symbol) return null;
        nodeIdx++;
        break;
      }

      case 'capture': {
        const anchor = findNextAnchor(pattern, patIdx + 1);

        if (anchor === null) {
          // No anchor — capture everything remaining
          bindings.set(pe.name, nodeArr.slice(nodeIdx));
          nodeIdx = nodeArr.length;
        } else {
          // Scan forward for where the anchor matches
          const anchorPos = findAnchorInNodes(anchor, nodeArr, nodeIdx);
          if (anchorPos === null) return null;
          bindings.set(pe.name, nodeArr.slice(nodeIdx, anchorPos));
          nodeIdx = anchorPos;
        }
        break;
      }

      case 'bigop': {
        if (nodeIdx >= nodeArr.length) return null;
        const node = nodeArr[nodeIdx];
        if (node.tag !== 'BigOp' || node.operator !== pe.operator) return null;

        if (pe.below !== null) {
          if (node.below === null) return null;
          const sub = matchRow(pe.below, node.below.children);
          if (sub === null) return null;
          mergeBindings(bindings, sub);
        }
        if (pe.above !== null) {
          if (node.above === null) return null;
          const sub = matchRow(pe.above, node.above.children);
          if (sub === null) return null;
          mergeBindings(bindings, sub);
        }
        nodeIdx++;
        break;
      }

      case 'frac': {
        if (nodeIdx >= nodeArr.length) return null;
        const node = nodeArr[nodeIdx];
        if (node.tag !== 'Frac') return null;

        const numSub = matchRow(pe.numer, node.numer.children);
        if (numSub === null) return null;
        mergeBindings(bindings, numSub);

        const denSub = matchRow(pe.denom, node.denom.children);
        if (denSub === null) return null;
        mergeBindings(bindings, denSub);

        nodeIdx++;
        break;
      }

      case 'delimiter': {
        if (nodeIdx >= nodeArr.length) return null;
        const node = nodeArr[nodeIdx];
        if (node.tag !== 'Delimiter' || node.open !== pe.open || node.close !== pe.close) return null;

        const sub = matchRow(pe.inner, node.inner.children);
        if (sub === null) return null;
        mergeBindings(bindings, sub);

        nodeIdx++;
        break;
      }

      case 'accent': {
        if (nodeIdx >= nodeArr.length) return null;
        const node = nodeArr[nodeIdx];
        if (node.tag !== 'Accent' || node.accent !== pe.accent) return null;

        const sub = matchRow(pe.body, node.body.children);
        if (sub === null) return null;
        mergeBindings(bindings, sub);

        nodeIdx++;
        break;
      }

      case 'sub': {
        if (nodeIdx >= nodeArr.length) return null;
        const node = nodeArr[nodeIdx];
        if (node.tag !== 'Sub') return null;

        const baseSub = matchRow(pe.base, node.base.children);
        if (baseSub === null) return null;
        mergeBindings(bindings, baseSub);

        const subSub = matchRow(pe.sub, node.sub.children);
        if (subSub === null) return null;
        mergeBindings(bindings, subSub);

        nodeIdx++;
        break;
      }

      case 'sup': {
        if (nodeIdx >= nodeArr.length) return null;
        const node = nodeArr[nodeIdx];
        if (node.tag !== 'Sup') return null;

        const baseSub = matchRow(pe.base, node.base.children);
        if (baseSub === null) return null;
        mergeBindings(bindings, baseSub);

        const supSub = matchRow(pe.sup, node.sup.children);
        if (supSub === null) return null;
        mergeBindings(bindings, supSub);

        nodeIdx++;
        break;
      }
    }
  }

  // All pattern elements consumed — all input must be consumed too
  if (nodeIdx < nodeArr.length) return null;
  return bindings;
}

/** Find the next non-capture pattern element after startIdx. */
function findNextAnchor(pattern: PatternElement[], startIdx: number): PatternElement | null {
  for (let i = startIdx; i < pattern.length; i++) {
    if (pattern[i].tag !== 'capture') return pattern[i];
  }
  return null;
}

/** Scan nodes starting at startIdx for where an anchor matches. */
function findAnchorInNodes(anchor: PatternElement, nodes: readonly MathNode[], startIdx: number): number | null {
  for (let i = startIdx; i < nodes.length; i++) {
    if (anchorMatchesAt(anchor, nodes[i])) return i;
  }
  return null;
}

/** Check if an anchor pattern matches a single node (shallow check for scanning). */
function anchorMatchesAt(anchor: PatternElement, node: MathNode): boolean {
  switch (anchor.tag) {
    case 'literal': return node.tag === 'Symbol' && node.value === anchor.symbol;
    case 'bigop': return node.tag === 'BigOp' && node.operator === anchor.operator;
    case 'frac': return node.tag === 'Frac';
    case 'delimiter': return node.tag === 'Delimiter' && node.open === anchor.open;
    case 'accent': return node.tag === 'Accent' && node.accent === anchor.accent;
    case 'sub': return node.tag === 'Sub';
    case 'sup': return node.tag === 'Sup';
    default: return false;
  }
}

function mergeBindings(target: Bindings, source: Bindings): void {
  for (const [k, v] of source) {
    target.set(k, v);
  }
}

// ============================================================================
// Source conversion
// ============================================================================

export interface ConvertResult {
  source: string;
  needsR: boolean;
}

/**
 * Convert a sequence of MathNodes to TT source using the syntax registry.
 * Tries patterns in priority order, falls back to per-node conversion.
 */
export function convertToSource(registry: SyntaxRegistry, nodes: readonly MathNode[]): ConvertResult {
  if (nodes.length === 0) return { source: '?', needsR: false };

  // Try row-level patterns in priority order
  const sorted = getSortedEntries(registry);
  for (const entry of sorted) {
    const bindings = matchRow(entry.pattern, nodes);
    if (bindings !== null) {
      // Recursively convert each captured binding
      let needsR = entry.needsR ?? false;
      const convertedBindings = new Map<string, string>();

      for (const [name, capturedNodes] of bindings) {
        const result = convertToSource(registry, capturedNodes);
        convertedBindings.set(name, result.source);
        if (result.needsR) needsR = true;
      }

      const source = substituteTemplate(entry.template, convertedBindings);
      return { source, needsR };
    }
  }

  // No pattern matched — fall back to per-node conversion
  return convertNodesFallback(registry, nodes);
}

/**
 * Get all entries from registry chain, ordered for correct matching.
 *
 * Structural patterns (first element is NOT a capture) are tried first, in
 * descending priority — more specific structural matches take precedence.
 *
 * Infix patterns (first element IS a capture, e.g., $a + $b) are tried after,
 * in ASCENDING priority — lower-precedence operators (like =) should bind at
 * the top level before higher-precedence ones (like +). This gives correct
 * operator precedence: `a + b = c + d` splits on `=` first.
 */
function getSortedEntries(registry: SyntaxRegistry): SyntaxEntry[] {
  const entries: SyntaxEntry[] = [];
  let current: SyntaxRegistry | undefined = registry;
  while (current) {
    entries.push(...current.entries);
    current = current.parent;
  }

  const structural = entries.filter(e => e.pattern.length > 0 && e.pattern[0].tag !== 'capture');
  const infix = entries.filter(e => e.pattern.length > 0 && e.pattern[0].tag === 'capture');

  structural.sort((a, b) => b.priority - a.priority);
  infix.sort((a, b) => a.priority - b.priority);

  return [...structural, ...infix];
}

/** Look up a symbol in the registry chain's symbolMaps. */
function lookupSymbol(registry: SyntaxRegistry, value: string): { source: string; needsR: boolean } | undefined {
  let current: SyntaxRegistry | undefined = registry;
  while (current) {
    const mapped = current.symbolMap.get(value);
    if (mapped) return mapped;
    current = current.parent;
  }
  return undefined;
}

/** Fallback: convert nodes individually when no row pattern matches. */
function convertNodesFallback(registry: SyntaxRegistry, nodes: readonly MathNode[]): ConvertResult {
  const parts: string[] = [];
  let needsR = false;

  for (const node of nodes) {
    const result = convertSingleNode(registry, node);
    if (result.source) parts.push(result.source);
    if (result.needsR) needsR = true;
  }

  return {
    source: parts.length === 0 ? '?' : parts.join(' '),
    needsR,
  };
}

/** Convert a single MathNode to TT source. */
function convertSingleNode(registry: SyntaxRegistry, node: MathNode): ConvertResult {
  switch (node.tag) {
    case 'Symbol': {
      const mapped = lookupSymbol(registry, node.value);
      if (mapped) return { source: mapped.source, needsR: mapped.needsR };
      return { source: node.value, needsR: false };
    }

    case 'Delimiter': {
      const inner = convertToSource(registry, node.inner.children);
      return { source: `(${inner.source})`, needsR: inner.needsR };
    }

    case 'Frac': {
      // Try frac-specific patterns first
      const sorted = getSortedEntries(registry);
      for (const entry of sorted) {
        if (entry.pattern.length === 1 && entry.pattern[0].tag === 'frac') {
          const bindings = matchRow(entry.pattern, [node]);
          if (bindings !== null) {
            let nr = entry.needsR ?? false;
            const converted = new Map<string, string>();
            for (const [name, captured] of bindings) {
              const r = convertToSource(registry, captured);
              converted.set(name, r.source);
              if (r.needsR) nr = true;
            }
            return { source: substituteTemplate(entry.template, converted), needsR: nr };
          }
        }
      }
      // Fallback
      const numer = convertToSource(registry, node.numer.children);
      const denom = convertToSource(registry, node.denom.children);
      return {
        source: `(${numer.source} / ${denom.source})`,
        needsR: numer.needsR || denom.needsR,
      };
    }

    case 'BigOp': {
      // Try bigop-specific patterns
      const sorted = getSortedEntries(registry);
      for (const entry of sorted) {
        if (entry.pattern.length >= 1 && entry.pattern[0].tag === 'bigop') {
          const bindings = matchRow(entry.pattern.slice(0, 1), [node]);
          if (bindings !== null) {
            let nr = entry.needsR ?? false;
            const converted = new Map<string, string>();
            for (const [name, captured] of bindings) {
              const r = convertToSource(registry, captured);
              converted.set(name, r.source);
              if (r.needsR) nr = true;
            }
            return { source: substituteTemplate(entry.template, converted), needsR: nr };
          }
        }
      }
      return { source: '?', needsR: false };
    }

    case 'Accent': {
      // Try accent-specific patterns
      const sorted = getSortedEntries(registry);
      for (const entry of sorted) {
        if (entry.pattern.length === 1 && entry.pattern[0].tag === 'accent') {
          const bindings = matchRow(entry.pattern, [node]);
          if (bindings !== null) {
            let nr = entry.needsR ?? false;
            const converted = new Map<string, string>();
            for (const [name, captured] of bindings) {
              const r = convertToSource(registry, captured);
              converted.set(name, r.source);
              if (r.needsR) nr = true;
            }
            return { source: substituteTemplate(entry.template, converted), needsR: nr };
          }
        }
      }
      // Fallback
      const body = convertToSource(registry, node.body.children);
      return { source: body.source, needsR: body.needsR };
    }

    case 'Sub': {
      const base = convertToSource(registry, node.base.children);
      const sub = convertToSource(registry, node.sub.children);
      // Subscript concatenation for names (e.g., x₁ → x1)
      return {
        source: `${base.source}${sub.source}`,
        needsR: base.needsR || sub.needsR,
      };
    }

    case 'Sup': {
      const base = convertToSource(registry, node.base.children);
      const sup = convertToSource(registry, node.sup.children);
      return {
        source: `${base.source}^${sup.source}`,
        needsR: base.needsR || sup.needsR,
      };
    }

    case 'SubSup': {
      const base = convertToSource(registry, node.base.children);
      const sub = convertToSource(registry, node.sub.children);
      const sup = convertToSource(registry, node.sup.children);
      return {
        source: `${base.source}${sub.source}^${sup.source}`,
        needsR: base.needsR || sub.needsR || sup.needsR,
      };
    }

    case 'Hole':
      return { source: '?', needsR: false };

    case 'Text':
      // Text nodes are structural (e.g., "and", "then") — skip in source
      return { source: '', needsR: false };

    default:
      return { source: '?', needsR: false };
  }
}

// ============================================================================
// Template substitution
// ============================================================================

/**
 * Substitute $name and $$name references in a template string.
 *
 * - `$name`  — substitute as-is (value position: after ->, =>, at start)
 * - `$$name` — substitute with auto-paren (argument position: after function name)
 *
 * Auto-paren wraps multi-word values in parentheses to prevent
 * `radd f x g y` when we need `radd (f x) (g y)`.
 */
export function substituteTemplate(template: string, bindings: Map<string, string>): string {
  return template.replace(/\$\$(\w+)|\$(\w+)/g, (match, autoParenName, plainName) => {
    const name = autoParenName ?? plainName;
    const value = bindings.get(name);
    if (value === undefined) return match; // unbound — leave as-is

    // $$name: auto-parenthesize multi-word values
    if (autoParenName !== undefined && value.includes(' ') && !value.startsWith('(') && !value.startsWith('\\')) {
      return `(${value})`;
    }
    return value;
  });
}

// ============================================================================
// Pattern display (for UI)
// ============================================================================

/** Convert a pattern to display LaTeX (for the syntax reference panel). */
export function patternToDisplayLatex(pattern: PatternElement[]): string {
  return pattern.map(pe => patternElementToLatex(pe)).join(' ');
}

function patternElementToLatex(pe: PatternElement): string {
  switch (pe.tag) {
    case 'literal': {
      // Render LaTeX symbols directly, add spacing for operators
      const SPACED = new Set(['+', '-', '=', '\\leq', '\\geq', '<', '>', '\\to', '\\in', '\\cdot', '\\times']);
      if (SPACED.has(pe.symbol)) return pe.symbol;
      return pe.symbol;
    }
    case 'capture':
      return `\\textcolor{#58a6ff}{${pe.name}}`;
    case 'bigop': {
      const op = `\\${pe.operator}`;
      const below = pe.below ? `_{${pe.below.map(p => patternElementToLatex(p)).join(' ')}}` : '';
      const above = pe.above ? `^{${pe.above.map(p => patternElementToLatex(p)).join(' ')}}` : '';
      return `${op}${below}${above}`;
    }
    case 'frac': {
      const n = pe.numer.map(p => patternElementToLatex(p)).join(' ');
      const d = pe.denom.map(p => patternElementToLatex(p)).join(' ');
      return `\\frac{${n}}{${d}}`;
    }
    case 'delimiter': {
      const inner = pe.inner.map(p => patternElementToLatex(p)).join(' ');
      const open = pe.open === '\\|' ? '\\|' : pe.open;
      const close = pe.close === '\\|' ? '\\|' : pe.close;
      return `\\left${open} ${inner} \\right${close}`;
    }
    case 'accent': {
      const body = pe.body.map(p => patternElementToLatex(p)).join(' ');
      if (pe.accent === 'overline') return `\\overline{${body}}`;
      return `\\${pe.accent}{${body}}`;
    }
    case 'sub': {
      const base = pe.base.map(p => patternElementToLatex(p)).join('');
      const sub = pe.sub.map(p => patternElementToLatex(p)).join(' ');
      return `${base}_{${sub}}`;
    }
    case 'sup': {
      const base = pe.base.map(p => patternElementToLatex(p)).join('');
      const sup = pe.sup.map(p => patternElementToLatex(p)).join(' ');
      return `${base}^{${sup}}`;
    }
  }
}

// ============================================================================
// Default registry — real analysis
// ============================================================================

export function createDefaultRegistry(): SyntaxRegistry {
  const symbolMap = new Map<string, { source: string; needsR: boolean }>([
    ['\\mathbb{R}', { source: 'Carrier R', needsR: true }],
    ['\\mathbb{N}', { source: 'Nat', needsR: false }],
    ['\\mathbb{Z}', { source: 'Int', needsR: false }],
  ]);

  const entries: SyntaxEntry[] = [
    // --- Structural patterns (priority 50) ---

    // lim_{x → a} body = L  →  Limit (\x => body) a L
    // Must be higher priority than bare = pattern
    {
      name: 'limit-equals',
      pattern: [
        pat.bigop('lim', [pat.capture('x'), pat.literal('\\to'), pat.capture('a')]),
        pat.capture('body'),
        pat.literal('='),
        pat.capture('L'),
      ],
      template: 'Limit (\\$x => $body) $$a $$L',
      needsR: true,
      priority: 50,
    },

    // lim_{x → a} body  →  Limit (\x => body) a
    {
      name: 'limit',
      pattern: [
        pat.bigop('lim', [pat.capture('x'), pat.literal('\\to'), pat.capture('a')]),
        pat.capture('body'),
      ],
      template: 'Limit (\\$x => $body) $$a',
      needsR: true,
      priority: 45,
    },

    // \frac{a}{b}  →  rmul a (rinv b)
    {
      name: 'fraction',
      pattern: [pat.frac([pat.capture('a')], [pat.capture('b')])],
      template: 'rmul $$a (rinv $$b)',
      needsR: true,
      priority: 50,
    },

    // |a|  →  rabs a
    {
      name: 'absolute-value',
      pattern: [pat.delimiter('|', '|', [pat.capture('a')])],
      template: 'rabs $$a',
      needsR: true,
      priority: 50,
    },

    // \overline{A}  →  closure A
    {
      name: 'closure',
      pattern: [pat.accent('overline', [pat.capture('A')])],
      template: 'closure $$A',
      priority: 50,
    },

    // --- Infix patterns (priority 10) ---
    // Use $$name for argument positions (auto-paren multi-word values)

    {
      name: 'addition',
      pattern: [pat.capture('a'), pat.literal('+'), pat.capture('b')],
      template: 'radd $$a $$b',
      needsR: true,
      priority: 10,
    },
    {
      name: 'subtraction',
      pattern: [pat.capture('a'), pat.literal('-'), pat.capture('b')],
      template: 'rsub $$a $$b',
      needsR: true,
      priority: 10,
    },
    {
      name: 'multiplication',
      pattern: [pat.capture('a'), pat.literal('\\cdot'), pat.capture('b')],
      template: 'rmul $$a $$b',
      needsR: true,
      priority: 10,
    },
    {
      name: 'less-equal',
      pattern: [pat.capture('a'), pat.literal('\\leq'), pat.capture('b')],
      template: 'rle $$a $$b',
      needsR: true,
      priority: 10,
    },
    {
      name: 'less-than',
      pattern: [pat.capture('a'), pat.literal('<'), pat.capture('b')],
      template: 'rlt $$a $$b',
      needsR: true,
      priority: 10,
    },
    {
      name: 'greater-equal',
      pattern: [pat.capture('a'), pat.literal('\\geq'), pat.capture('b')],
      template: 'rge $$a $$b',
      needsR: true,
      priority: 10,
    },
    {
      name: 'element-of',
      pattern: [pat.capture('a'), pat.literal('\\in'), pat.capture('S')],
      template: 'elem $$a $$S',
      priority: 10,
    },
    {
      name: 'subset',
      pattern: [pat.capture('A'), pat.literal('\\subseteq'), pat.capture('B')],
      template: 'subset $$A $$B',
      priority: 10,
    },

    // --- Low priority (5) ---
    // Use $name (no auto-paren) for value positions around -> and =

    {
      name: 'equality',
      pattern: [pat.capture('a'), pat.literal('='), pat.capture('b')],
      template: 'Equal $$a $$b',
      priority: 5,
    },
    {
      name: 'arrow',
      pattern: [pat.capture('a'), pat.literal('\\to'), pat.capture('b')],
      template: '$a -> $b',
      priority: 5,
    },
  ];

  return { entries, symbolMap };
}
