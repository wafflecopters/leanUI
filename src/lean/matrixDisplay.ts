/**
 * Matrix display DERIVED FROM AN INDEXED FAMILY.
 *
 * A grid with ellipses is not a list of cells: `\vdots` is an assertion about
 * an indexed family ("rows 2..n all follow this rule"), and writing it as a
 * literal cell is how a WYSIWYG display and the underlying semantics quietly
 * diverge. So the model here is the family — a row range, a column range, and
 * an entry rule that is a total function of (i, j) — and the DISPLAY is
 * computed from it: which indices to sample, where the ellipsis bands fall,
 * and what each sampled cell says.
 *
 * Consequences that fall out rather than being special-cased:
 *   - A concrete small matrix (3×3) renders as a full grid with no ellipses;
 *     the same spec with a symbolic bound renders with them.
 *   - When a step SHRINKS the matrix (n × n → (n−1) × (n−1)), the corner
 *     entries change with the bound, because they were never written down.
 *   - Piecewise rules (row 1 says one thing, rows 2..n another) are just a
 *     branch inside the entry function, and the sampler is required to show
 *     at least one row from each band for the display to be honest.
 *
 * Ellipsis geometry: each ellipsis occupies its OWN row/column of the grid,
 * so `\cdots` is centered in its own column rather than in the gap between two
 * cells of wildly different widths, and `\ddots` lands at the intersection of
 * the two bands — geometrically, not by cell index.
 *
 * Display-only. Nothing here is a term; nothing round-trips into Lean.
 */

/** An index expression: a number, or a symbol with an integer offset (`n−1`). */
export interface Idx {
  readonly sym?: string;
  readonly offset: number;
}

export const num = (n: number): Idx => ({ offset: n });
export const sym = (s: string, offset = 0): Idx => ({ sym: s, offset });
export const shift = (i: Idx, d: number): Idx => ({ ...i, offset: i.offset + d });

/** The concrete value of an index, or null when it is symbolic. */
export const idxValue = (i: Idx): number | null => (i.sym ? null : i.offset);

export function showIdx(i: Idx): string {
  if (!i.sym) return String(i.offset);
  if (i.offset === 0) return i.sym;
  return `${i.sym}${i.offset > 0 ? '+' : '-'}${Math.abs(i.offset)}`;
}

/** `base^e`, written the way a person writes it: `1`, `x`, `x^{2}`, `x^{n-1}`. */
export function pow(base: string, e: Idx): string {
  const v = idxValue(e);
  if (v === 0) return '1';
  if (v === 1) return base;
  return `${base}^{${showIdx(e)}}`;
}

/** `a·(b)` with the identity factor dropped — `1·(x−y)` is just `x−y`. */
export function mul(a: string, b: string): string {
  if (a === '1') return b;
  if (b === '1') return a;
  return `${a}(${b})`;
}

/** One axis of the grid: indices `from … count`, showing `head` of them up front. */
export interface Dim {
  /** The last index — `n`, `n−1`, or a literal `3`. */
  readonly count: Idx;
  /** The first index (default 1). */
  readonly from?: number;
  /** How many leading indices to show before the ellipsis band (default 2). */
  readonly head?: number;
}

export interface MatrixSpec {
  readonly rows: Dim;
  readonly cols: Dim;
  /** The entry at (i, j) as LaTeX. A total function on the rectangle. */
  readonly entry: (i: Idx, j: Idx) => string;
  /** Bracket style (default parentheses). */
  readonly delim?: 'p' | 'b' | 'v';
}

/** A sampled position on one axis: a real index, or the ellipsis band. */
export type Slot = { readonly tag: 'index'; readonly idx: Idx } | { readonly tag: 'gap' };

/**
 * Which indices to actually show. A symbolic bound always gets a band; a
 * concrete bound small enough to print in full gets no band at all, which is
 * why the same spec serves a 3×3 example and the general case.
 */
export function sampleAxis(d: Dim): Slot[] {
  const from = d.from ?? 1;
  const head = d.head ?? 2;
  const v = idxValue(d.count);
  const upTo = (last: number): Slot[] => {
    const out: Slot[] = [];
    for (let i = from; i <= last; i++) out.push({ tag: 'index', idx: num(i) });
    return out;
  };
  if (v !== null) {
    // A concrete bound: print the whole grid when it fits, else band it.
    if (v - from + 1 <= head + 1) return upTo(v);
    return [...upTo(from + head - 1), { tag: 'gap' }, { tag: 'index', idx: num(v) }];
  }
  return [...upTo(from + head - 1), { tag: 'gap' }, { tag: 'index', idx: d.count }];
}

/** The cell at a sampled (row, col) position — an entry or an ellipsis. */
export function cellLatex(spec: MatrixSpec, r: Slot, c: Slot): string {
  if (r.tag === 'gap' && c.tag === 'gap') return '\\ddots';
  if (r.tag === 'gap') return '\\vdots';
  if (c.tag === 'gap') return '\\cdots';
  return spec.entry(r.idx, c.idx);
}

/** The grid as LaTeX — a pmatrix/bmatrix/vmatrix environment. */
export function matrixLatex(spec: MatrixSpec): string {
  const rows = sampleAxis(spec.rows);
  const cols = sampleAxis(spec.cols);
  const env = `${spec.delim ?? 'p'}matrix`;
  const body = rows
    .map((r) => cols.map((c) => cellLatex(spec, r, c)).join(' & '))
    .join(' \\\\ ');
  return `\\begin{${env}} ${body} \\end{${env}}`;
}

/**
 * Does the sampling actually SHOW every band the entry rule distinguishes?
 *
 * A piecewise rule ("row 1 is special") is only honestly displayed when the
 * grid shows row 1 AND a generic row — otherwise the reader infers the wrong
 * family from the picture. Callers building a piecewise spec should assert
 * this; it is the display-level version of "the ellipsis is doing inductive
 * work". Returns the indices that were sampled, so a caller can check that a
 * distinguished index is among them.
 */
export function sampledIndices(d: Dim): Idx[] {
  return sampleAxis(d).flatMap((s) => (s.tag === 'index' ? [s.idx] : []));
}

/** Whether a concrete index is among the sampled ones (piecewise honesty). */
export function samples(d: Dim, index: number): boolean {
  return sampledIndices(d).some((i) => idxValue(i) === index);
}
