/**
 * The Vandermonde proof IS the acceptance test for the display model: three
 * steps whose grids change, and the change is the argument. Step 0 is a total
 * function of (i, j); Step 1 is piecewise (row 1 says one thing, rows 2..n
 * another); Step 2 SHRINKS, so the corner entry moves from x^{n-1} to x^{n-2}
 * without anyone editing a cell.
 */
import { describe, expect, test } from 'vitest';
import {
  cellLatex,
  matrixLatex,
  mul,
  num,
  pow,
  sampleAxis,
  samples,
  shift,
  showIdx,
  sym,
  type MatrixSpec,
} from './matrixDisplay';

const x = (i: ReturnType<typeof num>) => `x_{${showIdx(i)}}`;

/** Step 0: V, the Vandermonde matrix itself — a_{ij} = x_i^{j-1}. */
const STEP0: MatrixSpec = {
  rows: { count: sym('n'), head: 2 },
  cols: { count: sym('n'), head: 3 },
  entry: (i, j) => pow(x(i), shift(j, -1)),
};

/** Step 1: after C_j ← C_j − x_1 C_{j-1}. Row 1 clears; row i becomes
 *  x_i^{j-2}(x_i − x_1). PIECEWISE — the display must show both bands. */
const STEP1: MatrixSpec = {
  rows: { count: sym('n'), head: 2 },
  cols: { count: sym('n'), head: 3 },
  entry: (i, j) => {
    const firstCol = idxIs(j, 1);
    if (idxIs(i, 1)) return firstCol ? '1' : '0';
    if (firstCol) return '1';
    return mul(pow(x(i), shift(j, -2)), `${x(i)} - x_{1}`);
  },
};

/** Step 2: the minor that survives — (n−1) × (n−1), rows 2..n. */
const STEP2: MatrixSpec = {
  rows: { from: 2, count: sym('n'), head: 1 },
  cols: { count: sym('n', -1), head: 2 },
  entry: (i, j) => pow(x(i), shift(j, -1)),
};

function idxIs(i: { sym?: string; offset: number }, v: number): boolean {
  return !i.sym && i.offset === v;
}

describe('sampling an axis', () => {
  test('a symbolic bound gets an ellipsis band ending at the bound', () => {
    expect(sampleAxis({ count: sym('n'), head: 2 })).toEqual([
      { tag: 'index', idx: num(1) },
      { tag: 'index', idx: num(2) },
      { tag: 'gap' },
      { tag: 'index', idx: sym('n') },
    ]);
  });

  test('a concrete bound that FITS prints in full — no ellipses at all', () => {
    // The same model serves the 3x3 worked example and the general case.
    expect(sampleAxis({ count: num(3), head: 3 })).toEqual([
      { tag: 'index', idx: num(1) },
      { tag: 'index', idx: num(2) },
      { tag: 'index', idx: num(3) },
    ]);
    expect(matrixLatex({ ...STEP0, rows: { count: num(2) }, cols: { count: num(2) } }))
      .not.toContain('\\cdots');
  });

  test('a concrete bound too big to print still bands', () => {
    expect(sampleAxis({ count: num(9), head: 2 })).toEqual([
      { tag: 'index', idx: num(1) },
      { tag: 'index', idx: num(2) },
      { tag: 'gap' },
      { tag: 'index', idx: num(9) },
    ]);
  });

  test('a shifted start: rows 2..n', () => {
    expect(sampleAxis({ from: 2, count: sym('n'), head: 1 })).toEqual([
      { tag: 'index', idx: num(2) },
      { tag: 'gap' },
      { tag: 'index', idx: sym('n') },
    ]);
  });
});

describe('ellipsis geometry', () => {
  test('bands intersect at ddots; each ellipsis owns its own cell', () => {
    const gap = { tag: 'gap' } as const;
    const one = { tag: 'index', idx: num(1) } as const;
    expect(cellLatex(STEP0, gap, gap)).toBe('\\ddots');
    expect(cellLatex(STEP0, gap, one)).toBe('\\vdots');
    expect(cellLatex(STEP0, one, gap)).toBe('\\cdots');
  });
});

describe('Vandermonde step 0 — the matrix', () => {
  test('renders exactly the grid a paper prints', () => {
    expect(matrixLatex(STEP0)).toBe(
      '\\begin{pmatrix} ' +
        '1 & x_{1} & x_{1}^{2} & \\cdots & x_{1}^{n-1} \\\\ ' +
        '1 & x_{2} & x_{2}^{2} & \\cdots & x_{2}^{n-1} \\\\ ' +
        '\\vdots & \\vdots & \\vdots & \\ddots & \\vdots \\\\ ' +
        '1 & x_{n} & x_{n}^{2} & \\cdots & x_{n}^{n-1}' +
        ' \\end{pmatrix}',
    );
  });

  test('the leading entries are SIMPLIFIED, not written as x^0 and x^1', () => {
    // Derived from the formula, printed the way a person writes it.
    expect(pow('x_{1}', num(0))).toBe('1');
    expect(pow('x_{1}', num(1))).toBe('x_{1}');
    expect(pow('x_{1}', sym('n', -1))).toBe('x_{1}^{n-1}');
  });
});

describe('Vandermonde step 1 — the column operation (piecewise rows)', () => {
  test('row 1 clears to 1, 0, …, 0 while rows 2..n carry the factor', () => {
    expect(matrixLatex(STEP1)).toBe(
      '\\begin{pmatrix} ' +
        '1 & 0 & 0 & \\cdots & 0 \\\\ ' +
        '1 & x_{2} - x_{1} & x_{2}(x_{2} - x_{1}) & \\cdots & x_{2}^{n-2}(x_{2} - x_{1}) \\\\ ' +
        '\\vdots & \\vdots & \\vdots & \\ddots & \\vdots \\\\ ' +
        '1 & x_{n} - x_{1} & x_{n}(x_{n} - x_{1}) & \\cdots & x_{n}^{n-2}(x_{n} - x_{1})' +
        ' \\end{pmatrix}',
    );
  });

  test('the display is HONEST about a piecewise rule: both bands are shown', () => {
    // Row 1 is distinguished, so row 1 must be among the sampled rows AND a
    // generic row must be too — otherwise the picture asserts the wrong family.
    expect(samples(STEP1.rows, 1)).toBe(true);
    expect(samples(STEP1.rows, 2)).toBe(true);
    // A head of 1 would show ONLY the special row before the band: dishonest.
    expect(samples({ count: sym('n'), head: 1 }, 2)).toBe(false);
  });

  test('the common factor is dropped where it is 1 — no 1(x_2 - x_1)', () => {
    expect(mul('1', 'x_{2} - x_{1}')).toBe('x_{2} - x_{1}');
    expect(mul('x_{2}', 'x_{2} - x_{1}')).toBe('x_{2}(x_{2} - x_{1})');
  });
});

describe('Vandermonde step 2 — the matrix SHRINKS', () => {
  test('rows 2..n, columns 1..n-1, and the corner follows the bound', () => {
    expect(matrixLatex(STEP2)).toBe(
      '\\begin{pmatrix} ' +
        '1 & x_{2} & \\cdots & x_{2}^{n-2} \\\\ ' +
        '\\vdots & \\vdots & \\ddots & \\vdots \\\\ ' +
        '1 & x_{n} & \\cdots & x_{n}^{n-2}' +
        ' \\end{pmatrix}',
    );
  });

  test('the top-right entry changed with the bound, not by hand', () => {
    // Step 0's corner is x_1^{n-1}; step 2's is x_2^{n-2}. Both are the SAME
    // rule x_i^{j-1} read at the sampled corner — the index bounds moved.
    expect(matrixLatex(STEP0)).toContain('x_{1}^{n-1}');
    expect(matrixLatex(STEP2)).toContain('x_{2}^{n-2}');
    expect(matrixLatex(STEP2)).not.toContain('n-1');
  });
});

describe('bracket styles', () => {
  test('determinant bars are the same grid in vmatrix', () => {
    const v = matrixLatex({ ...STEP2, delim: 'v' });
    expect(v.startsWith('\\begin{vmatrix}')).toBe(true);
    expect(v.endsWith('\\end{vmatrix}')).toBe(true);
  });
});
