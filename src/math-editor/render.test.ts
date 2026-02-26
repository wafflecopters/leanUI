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

  test('renders fraction', () => {
    const row = mkRow([mkFrac(mkRow([mkSymbol('a')]), mkRow([mkSymbol('b')]))]);
    expect(renderStaticLatex(row)).toBe('\\frac{a}{b}');
  });

  test('renders subscript', () => {
    const row = mkRow([mkSub(mkRow([mkSymbol('x')]), mkRow([mkSymbol('2')]))]);
    expect(renderStaticLatex(row)).toBe('{x}_{2}');
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
    const row = mkRow([mkBigOp('sum', mkRow([mkSymbol('i'), mkSymbol('='), mkSymbol('0')]), mkRow([mkSymbol('n')]))]);
    expect(renderStaticLatex(row)).toBe('\\sum_{i = 0}^{n}');
  });

  test('renders BigOp lim (below only)', () => {
    const row = mkRow([mkBigOp('lim', mkRow([mkSymbol('n'), mkSymbol('\\to'), mkSymbol('\\infty')]), null)]);
    expect(renderStaticLatex(row)).toBe('\\lim_{n \\to \\infty}');
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
    expect(renderStaticLatex(row)).toBe('x \\in \\mathbb{R}');
  });

  test('regular symbols have no extra space', () => {
    const row = mkRow([mkSymbol('x'), mkSymbol('y')]);
    expect(renderStaticLatex(row)).toBe('xy');
  });

  test('renders TextNode with thin spaces', () => {
    const row = mkRow([mkSymbol('a'), mkText('and'), mkSymbol('b')]);
    expect(renderStaticLatex(row)).toBe('a\\;\\text{and}\\;b');
  });
});
