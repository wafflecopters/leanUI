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
  | { tag: 'bigop'; operator: string; below: PatternElement[] | null; above: PatternElement[] | null; body: PatternElement[] | null }
  | { tag: 'frac'; numer: PatternElement[]; denom: PatternElement[] }
  | { tag: 'delimiter'; open: string; close: string; inner: PatternElement[] }
  | { tag: 'accent'; accent: string; body: PatternElement[] }
  | { tag: 'sub'; base: PatternElement[]; sub: PatternElement[] }
  | { tag: 'sup'; base: PatternElement[]; sup: PatternElement[] };

// Convenience constructors
export const pat = {
  literal: (symbol: string): PatternElement => ({ tag: 'literal', symbol }),
  capture: (name: string): PatternElement => ({ tag: 'capture', name }),
  bigop: (operator: string, below: PatternElement[] | null, above: PatternElement[] | null = null, body: PatternElement[] | null = null): PatternElement =>
    ({ tag: 'bigop', operator, below, above, body }),
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
  symbolMap: Map<string, { source: string; needsR: boolean; isRecord?: boolean }>;
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
        if (pe.body !== null) {
          const sub = matchRow(pe.body, node.body.children);
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
export function lookupSymbol(registry: SyntaxRegistry, value: string): { source: string; needsR: boolean; isRecord?: boolean } | undefined {
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
            const src = substituteTemplate(entry.template, converted);
            // Wrap in parens — BigOp produces multi-arg applications that need grouping
            return { source: `(${src})`, needsR: nr };
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
      // Try sub-specific patterns first
      const sortedSub = getSortedEntries(registry);
      for (const entry of sortedSub) {
        if (entry.pattern.length === 1 && entry.pattern[0].tag === 'sub') {
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
      // Fallback: subscript concatenation for names (e.g., x₁ → x1)
      const base = convertToSource(registry, node.base.children);
      const sub = convertToSource(registry, node.sub.children);
      return {
        source: `${base.source}${sub.source}`,
        needsR: base.needsR || sub.needsR,
      };
    }

    case 'Sup': {
      // Try sup-specific patterns first
      const sortedSup = getSortedEntries(registry);
      for (const entry of sortedSup) {
        if (entry.pattern.length === 1 && entry.pattern[0].tag === 'sup') {
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
      const baseSup = convertToSource(registry, node.base.children);
      const sup = convertToSource(registry, node.sup.children);
      return {
        source: `${baseSup.source}^${sup.source}`,
        needsR: baseSup.needsR || sup.needsR,
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
      const body = pe.body ? ` ${pe.body.map(p => patternElementToLatex(p)).join(' ')}` : '';
      return `${op}${below}${above}${body}`;
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
        pat.bigop('lim', [pat.capture('x'), pat.literal('\\to'), pat.capture('a')], null, [pat.capture('body')]),
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
        pat.bigop('lim', [pat.capture('x'), pat.literal('\\to'), pat.capture('a')], null, [pat.capture('body')]),
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

// ============================================================================
// @syntax annotation parser — converts pattern strings to SyntaxEntry objects
// ============================================================================

/** Known LaTeX command abbreviations for common symbols. */
const LATEX_ABBREVIATIONS: Record<string, string> = {
  '\\N': '\\mathbb{N}',
  '\\R': '\\mathbb{R}',
  '\\Z': '\\mathbb{Z}',
};

/** BigOp operators: LaTeX command → internal operator name. */
const BIGOP_OPERATORS: Record<string, string> = {
  '\\sum': 'sum',
  '\\prod': 'prod',
  '\\int': 'int',
  '\\lim': 'lim',
};

export interface ParsedSyntaxAnnotation {
  /** Symbol mapping (no captures): e.g., \mathbb{N} → Nat */
  symbolMapping?: { symbol: string; source: string };
  /** Pattern entry (has captures): e.g., $0 + $1 → plus $$0 $$1 */
  entry?: SyntaxEntry;
}

/**
 * Parse a @syntax annotation string and generate the corresponding
 * symbol mapping or pattern entry.
 *
 * Pattern syntax:
 *   $N        — capture for explicit arg N (0-indexed)
 *   $Name     — capture for implicit arg Name (uppercase first letter)
 *   \command  — LaTeX command (\N, \R, \Z are expanded to \mathbb{...})
 *   _{...}    — subscript (creates Sub pattern; or BigOp below slot)
 *   ^{...}    — superscript (creates Sup pattern; or BigOp above slot)
 *   \prime    — as postfix, creates Sup with prime
 *   other     — literal symbol
 *
 * If the pattern contains no captures, it becomes a symbol mapping.
 * Otherwise it becomes a SyntaxEntry with auto-generated template.
 */
export function parseSyntaxAnnotation(
  patternStr: string,
  declName: string,
  priority?: number,
): ParsedSyntaxAnnotation {
  // Split on @becomes for explicit template override
  const becomesIdx = patternStr.indexOf(' @becomes ');
  const rawPattern = becomesIdx >= 0 ? patternStr.slice(0, becomesIdx) : patternStr;
  const explicitTemplate = becomesIdx >= 0 ? patternStr.slice(becomesIdx + ' @becomes '.length).trim() : null;

  const elements = parsePatternString(rawPattern);

  const hasCaptures = containsCaptures(elements);

  if (!hasCaptures) {
    // Symbol mapping: the entire pattern is literal(s)
    const symbol = elementsToSymbol(elements);
    return { symbolMapping: { symbol, source: declName } };
  }

  // Use explicit template or auto-generate from captures
  const template = explicitTemplate ?? generateTemplate(declName, elements);
  const effectivePriority = priority ?? computeDefaultPriority(elements);

  return {
    entry: {
      name: declName,
      pattern: elements,
      template,
      priority: effectivePriority,
    },
  };
}

/**
 * Parse a pattern string into PatternElement[].
 * Handles LaTeX commands, captures ($N/$Name), subscripts, superscripts, BigOps.
 */
export function parsePatternString(input: string): PatternElement[] {
  let i = 0;

  function skipSpaces(): void {
    while (i < input.length && input[i] === ' ') i++;
  }

  function parseCapture(): PatternElement {
    i++; // skip $
    let name = '';
    while (i < input.length && /[a-zA-Z0-9_]/.test(input[i])) {
      name += input[i]; i++;
    }
    if (name === '') name = '?'; // malformed capture
    return pat.capture(name);
  }

  function parseLaTeXCommand(): string {
    let cmd = '\\';
    i++; // skip \
    while (i < input.length && /[a-zA-Z]/.test(input[i])) {
      cmd += input[i]; i++;
    }
    // Handle \mathbb{X} — consume the {X} part
    if (cmd === '\\mathbb' && i < input.length && input[i] === '{') {
      i++; // skip {
      let arg = '';
      while (i < input.length && input[i] !== '}') {
        arg += input[i]; i++;
      }
      if (i < input.length && input[i] === '}') i++; // skip }
      cmd = `\\mathbb{${arg}}`;
    }
    // Apply abbreviations
    if (cmd in LATEX_ABBREVIATIONS) cmd = LATEX_ABBREVIATIONS[cmd];
    return cmd;
  }

  function parseBraced(): PatternElement[] {
    i++; // skip {
    const elems: PatternElement[] = [];
    while (i < input.length && input[i] !== '}') {
      skipSpaces();
      if (i >= input.length || input[i] === '}') break;
      const elem = parseElement();
      if (elem) elems.push(elem);
    }
    if (i < input.length && input[i] === '}') i++; // skip }
    return elems;
  }

  function parseSingleOrBraced(): PatternElement[] {
    skipSpaces();
    if (i < input.length && input[i] === '{') {
      return parseBraced();
    }
    // Single element
    const elem = parseElement();
    return elem ? [elem] : [];
  }

  function parseElement(): PatternElement | null {
    skipSpaces();
    if (i >= input.length) return null;

    const ch = input[i];

    // Capture: $name
    if (ch === '$') {
      const capture = parseCapture();
      return applyPostfix(capture);
    }

    // LaTeX command: \command
    if (ch === '\\') {
      const cmd = parseLaTeXCommand();

      // Check if this is a BigOp operator
      if (cmd in BIGOP_OPERATORS) {
        return parseBigOp(BIGOP_OPERATORS[cmd]);
      }

      const literal = pat.literal(cmd);
      return applyPostfix(literal);
    }

    // Skip braces used for grouping (not meaningful at top level)
    if (ch === '{' || ch === '}') {
      i++;
      return null; // will be skipped
    }

    // Regular character: literal
    i++;
    const literal = pat.literal(ch);
    return applyPostfix(literal);
  }

  function applyPostfix(base: PatternElement): PatternElement {
    // Check for \prime postfix → creates Sup with prime
    if (i < input.length && input[i] === '\\') {
      const savedI = i;
      const cmd = parseLaTeXCommand();
      if (cmd === '\\prime') {
        return pat.sup([base], [pat.literal('\\prime')]);
      }
      // Not a postfix command — restore position
      i = savedI;
    }

    // Check for subscript
    if (i < input.length && input[i] === '_') {
      i++; // skip _
      const sub = parseSingleOrBraced();
      // Check for additional superscript after subscript
      skipSpaces();
      if (i < input.length && input[i] === '^') {
        i++; // skip ^
        // For now, ignore the sup part of a SubSup on non-BigOp
        // (would need SubSup pattern element)
        parseSingleOrBraced();
      }
      return pat.sub([base], sub);
    }

    // Check for superscript
    if (i < input.length && input[i] === '^') {
      i++; // skip ^
      const sup = parseSingleOrBraced();
      return pat.sup([base], sup);
    }

    return base;
  }

  function parseBigOp(operator: string): PatternElement {
    let below: PatternElement[] | null = null;
    let above: PatternElement[] | null = null;
    let body: PatternElement[] | null = null;

    skipSpaces();
    if (i < input.length && input[i] === '_') {
      i++; // skip _
      below = parseSingleOrBraced();
    }

    skipSpaces();
    if (i < input.length && input[i] === '^') {
      i++; // skip ^
      above = parseSingleOrBraced();
    }

    // Parse one body element (the expression being operated on)
    skipSpaces();
    if (i < input.length) {
      const el = parseElement();
      if (el) body = [el];
    }

    return pat.bigop(operator, below, above, body);
  }

  // Parse all elements
  const result: PatternElement[] = [];
  while (i < input.length) {
    skipSpaces();
    if (i >= input.length) break;
    const elem = parseElement();
    if (elem) result.push(elem);
  }

  return result;
}

// ============================================================================
// Helpers for parseSyntaxAnnotation
// ============================================================================

/** Check if a pattern element tree contains any captures. */
function containsCaptures(elements: PatternElement[]): boolean {
  for (const e of elements) {
    switch (e.tag) {
      case 'capture': return true;
      case 'sub': if (containsCaptures(e.base) || containsCaptures(e.sub)) return true; break;
      case 'sup': if (containsCaptures(e.base) || containsCaptures(e.sup)) return true; break;
      case 'bigop':
        if ((e.below !== null && containsCaptures(e.below)) ||
            (e.above !== null && containsCaptures(e.above)) ||
            (e.body !== null && containsCaptures(e.body))) return true;
        break;
      case 'frac': if (containsCaptures(e.numer) || containsCaptures(e.denom)) return true; break;
      case 'delimiter': if (containsCaptures(e.inner)) return true; break;
      case 'accent': if (containsCaptures(e.body)) return true; break;
    }
  }
  return false;
}

/** Collect all capture names from a pattern, in the order they appear. */
function collectCaptures(elements: PatternElement[]): string[] {
  const captures: string[] = [];
  function walk(elems: PatternElement[]) {
    for (const e of elems) {
      switch (e.tag) {
        case 'capture': captures.push(e.name); break;
        case 'sub': walk(e.base); walk(e.sub); break;
        case 'sup': walk(e.base); walk(e.sup); break;
        case 'bigop':
          if (e.below) walk(e.below);
          if (e.above) walk(e.above);
          if (e.body) walk(e.body);
          break;
        case 'frac': walk(e.numer); walk(e.denom); break;
        case 'delimiter': walk(e.inner); break;
        case 'accent': walk(e.body); break;
      }
    }
  }
  walk(elements);
  return captures;
}

/**
 * Generate a TT source template from declaration name and pattern captures.
 *
 * - Numbered captures ($0, $1, $2) → explicit args: `$$0 $$1 $$2`
 * - Named captures ($A, $B) → implicit args: `{$$A} {$$B}`
 * - Implicits emitted first (in appearance order), then explicits (in numeric order)
 */
function generateTemplate(declName: string, elements: PatternElement[]): string {
  const captures = collectCaptures(elements);

  // Separate named (implicit) and numbered (explicit) captures
  const implicitCaptures = captures.filter(c => /^[A-Z]/.test(c));
  const explicitCaptures = captures
    .filter(c => /^\d/.test(c))
    .sort((a, b) => parseInt(a) - parseInt(b));

  const parts = [declName];

  for (const c of implicitCaptures) {
    parts.push(`{$$${c}}`);
  }

  for (const c of explicitCaptures) {
    parts.push(`$$${c}`);
  }

  return parts.join(' ');
}

/** Convert literal-only elements to a single symbol string. */
function elementsToSymbol(elements: PatternElement[]): string {
  if (elements.length === 1 && elements[0].tag === 'literal') {
    return elements[0].symbol;
  }
  return elements.map(e => e.tag === 'literal' ? e.symbol : '?').join('');
}

/**
 * Compute a default priority for a pattern.
 * - Infix (starts with capture): 10, or 5 for = and → operators
 * - Structural (starts with non-capture): 50
 */
function computeDefaultPriority(elements: PatternElement[]): number {
  if (elements[0]?.tag === 'capture') {
    // Check for wide-binding operators
    for (const e of elements) {
      if (e.tag === 'literal' && (e.symbol === '=' || e.symbol === '\\to')) {
        return 5;
      }
    }
    return 10;
  }
  return 50;
}

// ============================================================================
// Registry builder — construct a SyntaxRegistry from @syntax annotations
// ============================================================================

export interface SyntaxAnnotation {
  declName: string;
  pattern: string;
  isRecord?: boolean;
}

/**
 * Build a SyntaxRegistry from a list of @syntax annotations.
 *
 * Annotations are processed in order. For infix patterns, earlier definitions
 * bind wider (lower priority value → tried first in ascending sort).
 * For structural patterns, later definitions bind tighter (higher priority
 * value → tried first in descending sort).
 */
export function buildRegistryFromAnnotations(annotations: SyntaxAnnotation[]): SyntaxRegistry {
  const symbolMap = new Map<string, { source: string; needsR: boolean; isRecord?: boolean }>();
  const entries: SyntaxEntry[] = [];

  let infixCounter = 5;   // Incrementing: earlier → lower → binds wider
  let structuralCounter = 50; // Incrementing: later → higher → tried first

  for (const ann of annotations) {
    const result = parseSyntaxAnnotation(ann.pattern, ann.declName);

    if (result.symbolMapping) {
      symbolMap.set(result.symbolMapping.symbol, { source: result.symbolMapping.source, needsR: false, isRecord: ann.isRecord });
    }

    if (result.entry) {
      if (result.entry.pattern[0]?.tag === 'capture') {
        // Infix pattern: use incrementing counter
        result.entry.priority = infixCounter++;
      } else {
        // Structural pattern: use incrementing counter
        result.entry.priority = structuralCounter++;
      }
      entries.push(result.entry);
    }
  }

  return { entries, symbolMap, parent: createDefaultRegistry() };
}
