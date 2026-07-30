import { describe, test, expect, beforeEach } from 'vitest';
import { resetIds, mkRow, mkSymbol, mkHole, mkFrac, mkSub, mkSup, mkSubSup, mkBigOp, mkAccent, mkDelimiter, mkText, MathEditorState } from './types';
import { renderToLatex, renderStaticLatex } from './render';

beforeEach(() => resetIds());

function mkState(root: ReturnType<typeof mkRow>, cursor: MathEditorState['cursor']): MathEditorState {
  return { root, cursor, commandBuffer: null, textBuffer: null };
}

const CURSOR = '\\htmlId{cursor}{\\textcolor{#4488ff}{\\rule[-0.15em]{1.5px}{1.05em}}}';
const HOLE = '\\textcolor{#666}{\\square}';

// ============================================================================
// Static rendering (no cursor)
// ============================================================================

describe('renderStaticLatex', () => {
  test('renders empty row with vphantom', () => {
    expect(renderStaticLatex(mkRow([]))).toBe('\\vphantom{0}');
  });

  test('renders symbols', () => {
    const row = mkRow([mkSymbol('x'), mkSymbol('+'), mkSymbol('y')]);
    expect(renderStaticLatex(row)).toBe('x + y');
  });

  test('renders hole', () => {
    const row = mkRow([mkHole()]);
    expect(renderStaticLatex(row)).toBe(HOLE);
  });

  test('spelled-out Greek names render as Greek symbols', () => {
    expect(renderStaticLatex(mkRow([mkSymbol('epsilon')])).trim()).toBe('\\varepsilon');
    expect(renderStaticLatex(mkRow([mkSymbol('delta')])).trim()).toBe('\\delta');
    expect(renderStaticLatex(mkRow([mkSymbol('pi')])).trim()).toBe('\\pi');
    expect(renderStaticLatex(mkRow([mkSymbol('Delta')])).trim()).toBe('\\Delta');
  });

  test('Greek name with a subscript suffix (deltaF, epsilon0)', () => {
    expect(renderStaticLatex(mkRow([mkSymbol('deltaF')])).trim()).toBe('\\delta_{F}');
    expect(renderStaticLatex(mkRow([mkSymbol('epsilon0')])).trim()).toBe('\\varepsilon_{0}');
  });

  test('non-Greek multi-letter names stay upright (no false Greek match)', () => {
    expect(renderStaticLatex(mkRow([mkSymbol('etale')])).trim()).toBe('\\operatorname{etale}');
    expect(renderStaticLatex(mkRow([mkSymbol('le')])).trim()).toBe('\\operatorname{le}');
  });

  test('renders fraction', () => {
    const row = mkRow([mkFrac(mkRow([mkSymbol('a')]), mkRow([mkSymbol('b')]))]);
    expect(renderStaticLatex(row)).toBe('\\frac{a}{b}');
  });

  test('renders subscript', () => {
    const row = mkRow([mkSub(mkRow([mkSymbol('x')]), mkRow([mkSymbol('2')]))]);
    expect(renderStaticLatex(row)).toBe('{x}_{2}');
  });

  test('limit-style operators put the subscript BELOW via \\limits', () => {
    // `\lim_{x → a}` needs the subscript on the bare operator, not a braced
    // group — else KaTeX trails it. We emit `\lim\limits_{…}`.
    const sub = mkRow([mkSymbol('x'), mkSymbol('\\to'), mkSymbol('a')]);
    expect(renderStaticLatex(mkRow([mkSub(mkRow([mkSymbol('\\lim')]), sub)])))
      .toBe('\\lim\\limits_{x \\to a}');
    // A normal (non-limits) base still braces the subscript.
    expect(renderStaticLatex(mkRow([mkSub(mkRow([mkSymbol('x')]), mkRow([mkSymbol('0')]))])))
      .toBe('{x}_{0}');
  });

  test('renders superscript', () => {
    const row = mkRow([mkSup(mkRow([mkSymbol('x')]), mkRow([mkSymbol('2')]))]);
    expect(renderStaticLatex(row)).toBe('{x}^{2}');
  });

  test('renders SubSup', () => {
    const row = mkRow([mkSubSup(mkRow([mkSymbol('x')]), mkRow([mkSymbol('i')]), mkRow([mkSymbol('2')]))]);
    expect(renderStaticLatex(row)).toBe('{x}_{i}^{2}');
  });

  test('renders BigOp sum', () => {
    const row = mkRow([mkBigOp('sum', mkRow([mkSymbol('i'), mkSymbol('='), mkSymbol('0')]), mkRow([mkSymbol('n')]), mkRow([mkSymbol('k')]))]);
    expect(renderStaticLatex(row)).toBe('\\sum_{i = 0}^{n}k');
  });

  test('renders BigOp lim (below only)', () => {
    const row = mkRow([mkBigOp('lim', mkRow([mkSymbol('n'), mkSymbol('\\to'), mkSymbol('\\infty')]), null, mkRow([mkSymbol('f')]))]);
    expect(renderStaticLatex(row)).toBe('\\lim_{n \\to \\infty }f');
  });

  test('renders accent vec', () => {
    const row = mkRow([mkAccent('vec', mkRow([mkSymbol('v')]))]);
    expect(renderStaticLatex(row)).toBe('\\vec{v}');
  });

  test('renders delimiter', () => {
    const row = mkRow([mkDelimiter('(', ')', mkRow([mkSymbol('x'), mkSymbol('+'), mkSymbol('y')]))]);
    expect(renderStaticLatex(row)).toBe('\\left(x + y\\right)');
  });

  test('renders nested: frac with sub inside', () => {
    const sub = mkSub(mkRow([mkSymbol('x')]), mkRow([mkSymbol('i')]));
    const frac = mkFrac(mkRow([sub]), mkRow([mkSymbol('n')]));
    const row = mkRow([frac]);
    expect(renderStaticLatex(row)).toBe('\\frac{{x}_{i}}{n}');
  });
});

// ============================================================================
// Cursor rendering
// ============================================================================

describe('renderToLatex (with cursor)', () => {
  test('cursor at start of empty row', () => {
    const root = mkRow([]);
    const s = mkState(root, { path: [], offset: 0 });
    expect(renderToLatex(s)).toBe(CURSOR);
  });

  test('cursor before first symbol', () => {
    const root = mkRow([mkSymbol('x')]);
    const s = mkState(root, { path: [], offset: 0 });
    const result = renderToLatex(s);
    expect(result).toContain(CURSOR);
    expect(result.indexOf(CURSOR)).toBeLessThan(result.indexOf('x'));
  });

  test('cursor after symbol', () => {
    const root = mkRow([mkSymbol('x')]);
    const s = mkState(root, { path: [], offset: 1 });
    const result = renderToLatex(s);
    expect(result).toContain(CURSOR);
    expect(result.indexOf('x')).toBeLessThan(result.indexOf(CURSOR));
  });

  test('cursor between symbols', () => {
    const root = mkRow([mkSymbol('a'), mkSymbol('b')]);
    const s = mkState(root, { path: [], offset: 1 });
    const result = renderToLatex(s);
    // Should be: htmlId(a) CURSOR htmlId(b)
    const cursorPos = result.indexOf(CURSOR);
    expect(cursorPos).toBeGreaterThan(0);
  });

  test('cursor inside fraction numerator', () => {
    const frac = mkFrac(mkRow([mkSymbol('a')]), mkRow([mkSymbol('b')]));
    const root = mkRow([frac]);
    const s = mkState(root, { path: [{ nodeId: frac.id, slot: 'numer' }], offset: 0 });
    const result = renderToLatex(s);
    // Cursor should appear inside the \\frac{ ... numerator ... }
    expect(result).toContain(CURSOR);
    // The cursor should be inside the frac's numer
    expect(result).toMatch(/\\frac\{.*\\htmlId\{cursor\}/);
  });

  test('cursor inside denominator', () => {
    const frac = mkFrac(mkRow([mkSymbol('a')]), mkRow([mkSymbol('b')]));
    const root = mkRow([frac]);
    const s = mkState(root, { path: [{ nodeId: frac.id, slot: 'denom' }], offset: 1 });
    const result = renderToLatex(s);
    expect(result).toContain(CURSOR);
    // Cursor after 'b' in denom
    expect(result).toMatch(/\\frac\{.*\}\{.*b.*\\htmlId\{cursor\}/);
  });

  test('cursor inside sub slot', () => {
    const sub = mkSub(mkRow([mkSymbol('x')]), mkRow([mkSymbol('2')]));
    const root = mkRow([sub]);
    const s = mkState(root, { path: [{ nodeId: sub.id, slot: 'sub' }], offset: 0 });
    const result = renderToLatex(s);
    expect(result).toContain(CURSOR);
    // Cursor in the subscript part
    expect(result).toMatch(/_\{.*\\htmlId\{cursor\}/);
  });

  test('htmlId wrapping present for each node', () => {
    const root = mkRow([mkSymbol('x'), mkSymbol('y')]);
    const s = mkState(root, { path: [], offset: 0 });
    const result = renderToLatex(s);
    // Each node should be wrapped in \htmlId{n-ID}{...}
    expect(result).toMatch(/\\htmlId\{n-\d+\}/);
  });
});

// ============================================================================
// Operator spacing
// ============================================================================

describe('operator spacing', () => {
  test('plus gets spaces', () => {
    const row = mkRow([mkSymbol('a'), mkSymbol('+'), mkSymbol('b')]);
    expect(renderStaticLatex(row)).toBe('a + b');
  });

  test('equals gets spaces', () => {
    const row = mkRow([mkSymbol('x'), mkSymbol('='), mkSymbol('1')]);
    expect(renderStaticLatex(row)).toBe('x = 1');
  });

  test('\\in gets spaces', () => {
    const row = mkRow([mkSymbol('x'), mkSymbol('\\in'), mkSymbol('\\mathbb{R}')]);
    expect(renderStaticLatex(row)).toBe('x \\in \\mathbb{R} ');
  });

  test('regular symbols have no extra space', () => {
    const row = mkRow([mkSymbol('x'), mkSymbol('y')]);
    expect(renderStaticLatex(row)).toBe('xy');
  });

  test('renders TextNode with thin spaces', () => {
    const row = mkRow([mkSymbol('a'), mkText('and'), mkSymbol('b')]);
    expect(renderStaticLatex(row)).toBe('a\\;\\text{and}\\;b');
  });

  test('renders single-letter + digits as subscript', () => {
    expect(renderStaticLatex(mkRow([mkSymbol('x0')]))).toBe('{x}_{0}');
    expect(renderStaticLatex(mkRow([mkSymbol('n1')]))).toBe('{n}_{1}');
    expect(renderStaticLatex(mkRow([mkSymbol('a12')]))).toBe('{a}_{12}');
  });

  test('does not subscript multi-letter names or primes', () => {
    expect(renderStaticLatex(mkRow([mkSymbol('sum')]))).toBe('\\operatorname{sum}');
    expect(renderStaticLatex(mkRow([mkSymbol("n'")]))).toBe("n'");
    expect(renderStaticLatex(mkRow([mkSymbol('x')]))).toBe('x');
  });
});
