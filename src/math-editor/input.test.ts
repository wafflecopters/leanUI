import { describe, test, expect, beforeEach } from 'vitest';
import { resetIds, mkRow, mkSymbol, mkHole, mkFrac, mkSub, mkSup, mkSubSup, mkBigOp, mkDelimiter, mkText, MathEditorState, MathNode } from './types';
import { handleInput, InputAction } from './input';
import { resolveRow, moveUp, moveDown, moveLeft } from './navigation';
import { renderToLatex } from './render';

beforeEach(() => resetIds());

function mkState(root: ReturnType<typeof mkRow>, cursor: MathEditorState['cursor']): MathEditorState {
  return { root, cursor, commandBuffer: null, textBuffer: null };
}

function char(c: string): InputAction { return { type: 'char', char: c }; }
function backspace(): InputAction { return { type: 'backspace' }; }

/** Helper: get the row at the cursor path */
function cursorRow(state: MathEditorState) {
  return resolveRow(state.root, state.cursor.path);
}

/** Helper: collect symbol values from a row's children */
function symbols(row: ReturnType<typeof mkRow>): string[] {
  return row.children.map(c => c.tag === 'Symbol' ? c.value : `<${c.tag}>`);
}

// ============================================================================
// Character insertion
// ============================================================================

describe('character insertion', () => {
  test('inserts a symbol into empty row', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });
    s = handleInput(s, char('x'));
    expect(cursorRow(s).children).toHaveLength(1);
    expect(cursorRow(s).children[0].tag).toBe('Symbol');
    expect((cursorRow(s).children[0] as any).value).toBe('x');
    expect(s.cursor.offset).toBe(1);
  });

  test('inserts symbols in sequence', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });
    s = handleInput(s, char('a'));
    s = handleInput(s, char('+'));
    s = handleInput(s, char('b'));
    expect(symbols(cursorRow(s))).toEqual(['a', '+', 'b']);
    expect(s.cursor.offset).toBe(3);
  });

  test('inserts at cursor position (middle of row)', () => {
    const root = mkRow([mkSymbol('a'), mkSymbol('c')]);
    let s = mkState(root, { path: [], offset: 1 });
    s = handleInput(s, char('b'));
    expect(symbols(cursorRow(s))).toEqual(['a', 'b', 'c']);
    expect(s.cursor.offset).toBe(2);
  });

  test('replaces a Hole with a symbol', () => {
    const root = mkRow([mkHole()]);
    let s = mkState(root, { path: [], offset: 0 });
    s = handleInput(s, char('x'));
    expect(cursorRow(s).children).toHaveLength(1);
    expect(cursorRow(s).children[0].tag).toBe('Symbol');
    expect(s.cursor.offset).toBe(1);
  });
});

// ============================================================================
// Subscript
// ============================================================================

describe('subscript (_)', () => {
  test('x_ creates Sub(base=[x], sub=[hole])', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });
    s = handleInput(s, char('x'));
    s = handleInput(s, char('_'));

    // Root should now have one Sub node
    expect(s.root.children).toHaveLength(1);
    const sub = s.root.children[0];
    expect(sub.tag).toBe('Sub');
    if (sub.tag === 'Sub') {
      expect(sub.base.children).toHaveLength(1);
      expect(sub.base.children[0].tag).toBe('Symbol');
      expect(sub.sub.children).toHaveLength(1);
      expect(sub.sub.children[0].tag).toBe('Hole');
    }

    // Cursor should be inside sub slot
    expect(s.cursor.path).toHaveLength(1);
    expect(s.cursor.path[0].slot).toBe('sub');
    expect(s.cursor.offset).toBe(0);
  });

  test('x_2 creates Sub(base=[x], sub=[2])', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });
    s = handleInput(s, char('x'));
    s = handleInput(s, char('_'));
    s = handleInput(s, char('2'));

    const sub = s.root.children[0];
    expect(sub.tag).toBe('Sub');
    if (sub.tag === 'Sub') {
      expect((sub.base.children[0] as any).value).toBe('x');
      // The '2' replaced the Hole
      expect(sub.sub.children).toHaveLength(1);
      expect((sub.sub.children[0] as any).value).toBe('2');
    }
  });

  test('_ at start creates Sub with Hole base', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });
    s = handleInput(s, char('_'));

    expect(s.root.children).toHaveLength(1);
    const sub = s.root.children[0];
    expect(sub.tag).toBe('Sub');
    if (sub.tag === 'Sub') {
      expect(sub.base.children[0].tag).toBe('Hole');
      expect(sub.sub.children[0].tag).toBe('Hole');
    }
  });

  test('x^2_ promotes to SubSup', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });
    s = handleInput(s, char('x'));
    s = handleInput(s, char('^'));
    s = handleInput(s, char('2'));

    // Now we have Sup(base=[x], sup=[2]) — exit sup first
    // Navigate to parent
    // After typing '2', cursor is at sub=[2] offset=1
    // We need to exit to root to type '_'
    // Let's manually place cursor after the Sup
    s = { ...s, cursor: { path: [], offset: 1 } };
    s = handleInput(s, char('_'));

    const node = s.root.children[0];
    expect(node.tag).toBe('SubSup');
    if (node.tag === 'SubSup') {
      expect((node.base.children[0] as any).value).toBe('x');
      expect((node.sup.children[0] as any).value).toBe('2');
      expect(node.sub.children[0].tag).toBe('Hole');
    }
    expect(s.cursor.path[0].slot).toBe('sub');
  });

  test('_ on existing Sub enters sub slot', () => {
    const sub = mkSub(mkRow([mkSymbol('x')]), mkRow([mkSymbol('i')]));
    const root = mkRow([sub]);
    let s = mkState(root, { path: [], offset: 1 });
    s = handleInput(s, char('_'));
    expect(s.cursor.path).toHaveLength(1);
    expect(s.cursor.path[0].slot).toBe('sub');
  });
});

// ============================================================================
// Superscript
// ============================================================================

describe('superscript (^)', () => {
  test('x^ creates Sup(base=[x], sup=[hole])', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });
    s = handleInput(s, char('x'));
    s = handleInput(s, char('^'));

    expect(s.root.children).toHaveLength(1);
    const sup = s.root.children[0];
    expect(sup.tag).toBe('Sup');
    if (sup.tag === 'Sup') {
      expect((sup.base.children[0] as any).value).toBe('x');
      expect(sup.sup.children[0].tag).toBe('Hole');
    }
    expect(s.cursor.path[0].slot).toBe('sup');
  });

  test('x_2^ promotes to SubSup', () => {
    const sub = mkSub(mkRow([mkSymbol('x')]), mkRow([mkSymbol('2')]));
    const root = mkRow([sub]);
    let s = mkState(root, { path: [], offset: 1 });
    s = handleInput(s, char('^'));

    const node = s.root.children[0];
    expect(node.tag).toBe('SubSup');
    if (node.tag === 'SubSup') {
      expect((node.base.children[0] as any).value).toBe('x');
      expect((node.sub.children[0] as any).value).toBe('2');
      expect(node.sup.children[0].tag).toBe('Hole');
    }
    expect(s.cursor.path[0].slot).toBe('sup');
  });

  test('^ on existing Sup enters sup slot', () => {
    const sup = mkSup(mkRow([mkSymbol('x')]), mkRow([mkSymbol('2')]));
    const root = mkRow([sup]);
    let s = mkState(root, { path: [], offset: 1 });
    s = handleInput(s, char('^'));
    expect(s.cursor.path[0].slot).toBe('sup');
  });
});

// ============================================================================
// Delimiters
// ============================================================================

describe('delimiters', () => {
  test('( creates Delimiter with Hole inner', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });
    s = handleInput(s, char('('));

    expect(s.root.children).toHaveLength(1);
    const delim = s.root.children[0];
    expect(delim.tag).toBe('Delimiter');
    if (delim.tag === 'Delimiter') {
      expect(delim.open).toBe('(');
      expect(delim.close).toBe(')');
      expect(delim.inner.children).toHaveLength(1);
      expect(delim.inner.children[0].tag).toBe('Hole');
    }
    expect(s.cursor.path[0].slot).toBe('inner');
  });

  test('(x+y) full sequence', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });
    s = handleInput(s, char('('));
    s = handleInput(s, char('x'));
    s = handleInput(s, char('+'));
    s = handleInput(s, char('y'));
    s = handleInput(s, char(')'));

    // After ), cursor should be in root, after the delimiter
    expect(s.cursor.path).toEqual([]);
    expect(s.cursor.offset).toBe(1);

    const delim = s.root.children[0];
    expect(delim.tag).toBe('Delimiter');
    if (delim.tag === 'Delimiter') {
      expect(symbols(delim.inner)).toEqual(['x', '+', 'y']);
    }
  });

  test(') with no enclosing delimiter does nothing', () => {
    const root = mkRow([mkSymbol('x')]);
    const s = mkState(root, { path: [], offset: 1 });
    const s2 = handleInput(s, char(')'));
    expect(s2).toBe(s);
  });

  test('[ creates bracket delimiter', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });
    s = handleInput(s, char('['));

    const delim = s.root.children[0];
    expect(delim.tag).toBe('Delimiter');
    if (delim.tag === 'Delimiter') {
      expect(delim.open).toBe('[');
      expect(delim.close).toBe(']');
    }
  });
});

// ============================================================================
// Backspace
// ============================================================================

describe('backspace', () => {
  test('deletes a symbol', () => {
    const root = mkRow([mkSymbol('a'), mkSymbol('b')]);
    let s = mkState(root, { path: [], offset: 2 });
    s = handleInput(s, backspace());
    expect(symbols(cursorRow(s))).toEqual(['a']);
    expect(s.cursor.offset).toBe(1);
  });

  test('at start of root does nothing', () => {
    const root = mkRow([mkSymbol('x')]);
    const s = mkState(root, { path: [], offset: 0 });
    const s2 = handleInput(s, backspace());
    expect(s2).toBe(s);
  });

  test('dissolves a Sub, keeps base content', () => {
    const sub = mkSub(mkRow([mkSymbol('x')]), mkRow([mkSymbol('2')]));
    const root = mkRow([sub]);
    let s = mkState(root, { path: [], offset: 1 });
    s = handleInput(s, backspace());

    // Sub dissolved, base content spilled — just 'x' remains
    expect(cursorRow(s).children).toHaveLength(1);
    expect((cursorRow(s).children[0] as any).value).toBe('x');
    expect(s.cursor.offset).toBe(1);
  });

  test('dissolves a Frac, keeps numerator content', () => {
    const frac = mkFrac(mkRow([mkSymbol('a'), mkSymbol('b')]), mkRow([mkSymbol('c')]));
    const root = mkRow([frac]);
    let s = mkState(root, { path: [], offset: 1 });
    s = handleInput(s, backspace());

    expect(symbols(cursorRow(s))).toEqual(['a', 'b']);
    expect(s.cursor.offset).toBe(2);
  });

  test('dissolves a Delimiter, spills inner content', () => {
    const delim = mkDelimiter('(', ')', mkRow([mkSymbol('x'), mkSymbol('+'), mkSymbol('y')]));
    const root = mkRow([delim]);
    let s = mkState(root, { path: [], offset: 1 });
    s = handleInput(s, backspace());

    expect(symbols(cursorRow(s))).toEqual(['x', '+', 'y']);
    expect(s.cursor.offset).toBe(3);
  });

  test('at start of slot, exits compound node', () => {
    const frac = mkFrac(mkRow([mkSymbol('a')]), mkRow([mkSymbol('b')]));
    const root = mkRow([mkSymbol('z'), frac]);
    let s = mkState(root, { path: [{ nodeId: frac.id, slot: 'numer' }], offset: 0 });
    s = handleInput(s, backspace());

    // Should exit to root, before frac
    expect(s.cursor.path).toEqual([]);
    expect(s.cursor.offset).toBe(1);
  });

  test('dissolving removes Holes from spilled content', () => {
    const frac = mkFrac(mkRow([mkHole()]), mkRow([mkSymbol('c')]));
    const root = mkRow([frac]);
    let s = mkState(root, { path: [], offset: 1 });
    s = handleInput(s, backspace());

    // Hole in numerator should be removed
    expect(cursorRow(s).children).toHaveLength(0);
    expect(s.cursor.offset).toBe(0);
  });

  test('backspace in command buffer removes last char', () => {
    const root = mkRow([]);
    let s: MathEditorState = { root, cursor: { path: [], offset: 0 }, commandBuffer: 'fra', textBuffer: null };
    s = handleInput(s, backspace());
    expect(s.commandBuffer).toBe('fr');
  });

  test('backspace on empty command buffer exits command mode', () => {
    const root = mkRow([]);
    let s: MathEditorState = { root, cursor: { path: [], offset: 0 }, commandBuffer: '', textBuffer: null };
    s = handleInput(s, backspace());
    expect(s.commandBuffer).toBe(null);
  });
});

// ============================================================================
// Command mode
// ============================================================================

describe('command mode (\\)', () => {
  test('\\ enters command buffer mode', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });
    s = handleInput(s, char('\\'));
    expect(s.commandBuffer).toBe('');
  });

  test('\\frac creates a fraction', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });
    s = handleInput(s, char('\\'));
    s = handleInput(s, char('f'));
    s = handleInput(s, char('r'));
    s = handleInput(s, char('a'));
    s = handleInput(s, char('c'));

    expect(s.commandBuffer).toBe(null);
    expect(s.root.children).toHaveLength(1);
    const frac = s.root.children[0];
    expect(frac.tag).toBe('Frac');
    if (frac.tag === 'Frac') {
      expect(frac.numer.children[0].tag).toBe('Hole');
      expect(frac.denom.children[0].tag).toBe('Hole');
    }
    // Cursor in numerator
    expect(s.cursor.path[0].slot).toBe('numer');
  });

  test('\\sum creates a BigOp', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });
    s = handleInput(s, char('\\'));
    s = handleInput(s, char('s'));
    s = handleInput(s, char('u'));
    s = handleInput(s, char('m'));

    expect(s.commandBuffer).toBe(null);
    expect(s.root.children).toHaveLength(1);
    const op = s.root.children[0];
    expect(op.tag).toBe('BigOp');
    if (op.tag === 'BigOp') {
      expect(op.operator).toBe('sum');
      expect(op.below).not.toBeNull();
      expect(op.above).not.toBeNull();
    }
    expect(s.cursor.path[0].slot).toBe('below');
  });

  test('\\lim creates BigOp with below only', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });
    s = handleInput(s, char('\\'));
    s = handleInput(s, char('l'));
    s = handleInput(s, char('i'));
    s = handleInput(s, char('m'));

    const op = s.root.children[0];
    expect(op.tag).toBe('BigOp');
    if (op.tag === 'BigOp') {
      expect(op.operator).toBe('lim');
      expect(op.below).not.toBeNull();
      expect(op.above).toBeNull();
    }
  });

  test('\\vec creates an accent', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });
    s = handleInput(s, char('\\'));
    s = handleInput(s, char('v'));
    s = handleInput(s, char('e'));
    s = handleInput(s, char('c'));

    const node = s.root.children[0];
    expect(node.tag).toBe('Accent');
    if (node.tag === 'Accent') {
      expect(node.accent).toBe('vec');
      expect(node.body.children[0].tag).toBe('Hole');
    }
    expect(s.cursor.path[0].slot).toBe('body');
  });

  test('\\alpha inserts a greek symbol', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });
    s = handleInput(s, char('\\'));
    s = handleInput(s, char('a'));
    s = handleInput(s, char('l'));
    s = handleInput(s, char('p'));
    s = handleInput(s, char('h'));
    s = handleInput(s, char('a'));

    expect(s.commandBuffer).toBe(null);
    expect(cursorRow(s).children).toHaveLength(1);
    expect((cursorRow(s).children[0] as any).value).toBe('\\alpha');
  });

  test('\\in does NOT auto-fire because \\int and \\infty exist', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });
    s = handleInput(s, char('\\'));
    s = handleInput(s, char('i'));
    s = handleInput(s, char('n'));

    // 'in' is a prefix of 'int', 'infty' — should NOT auto-fire
    expect(s.commandBuffer).toBe('in');

    // Space/Enter/Tab accepts the best match (exact match 'in')
    s = handleInput(s, char(' '));
    expect(s.commandBuffer).toBe(null);
    expect((cursorRow(s).children[0] as any).value).toBe('\\in');
  });

  test('\\int auto-fires because no longer command starts with "int"', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });
    s = handleInput(s, char('\\'));
    s = handleInput(s, char('i'));
    s = handleInput(s, char('n'));
    s = handleInput(s, char('t'));

    // 'int' is the only match (infty starts with 'inf', not 'int')
    expect(s.commandBuffer).toBe(null);
    expect(s.root.children[0].tag).toBe('BigOp');
    if (s.root.children[0].tag === 'BigOp') {
      expect(s.root.children[0].operator).toBe('int');
    }
  });

  test('\\in + Space inserts \\in, then can type \\int separately', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });
    // Type \in — held because 'infty', 'int' also start with 'in'
    s = handleInput(s, char('\\'));
    s = handleInput(s, char('i'));
    s = handleInput(s, char('n'));
    expect(s.commandBuffer).toBe('in');

    // Space accepts 'in' (exact match takes priority)
    s = handleInput(s, char(' '));
    expect(s.commandBuffer).toBe(null);
    expect(cursorRow(s).children).toHaveLength(1);
    expect((cursorRow(s).children[0] as any).value).toBe('\\in');
  });

  test('\\R inserts blackboard R', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });
    s = handleInput(s, char('\\'));
    s = handleInput(s, char('R'));

    expect(s.commandBuffer).toBe(null);
    expect((cursorRow(s).children[0] as any).value).toBe('\\mathbb{R}');
  });

  test('\\\\ cancels command mode', () => {
    const root = mkRow([]);
    let s: MathEditorState = { root, cursor: { path: [], offset: 0 }, commandBuffer: 'fr', textBuffer: null };
    s = handleInput(s, char('\\'));
    expect(s.commandBuffer).toBe(null);
  });
});

// ============================================================================
// Complex sequences
// ============================================================================

describe('complex input sequences', () => {
  test('a + \\frac{b}{c} sequence', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });

    // Type 'a'
    s = handleInput(s, char('a'));
    s = handleInput(s, char('+'));

    // Type \frac
    s = handleInput(s, char('\\'));
    s = handleInput(s, char('f'));
    s = handleInput(s, char('r'));
    s = handleInput(s, char('a'));
    s = handleInput(s, char('c'));

    // Now cursor is in numerator at offset 0
    expect(s.cursor.path).toHaveLength(1);
    expect(s.cursor.path[0].slot).toBe('numer');

    // Type 'b' in numerator
    s = handleInput(s, char('b'));

    // Verify structure so far
    expect(s.root.children).toHaveLength(3); // a, +, frac
    const frac = s.root.children[2];
    expect(frac.tag).toBe('Frac');
    if (frac.tag === 'Frac') {
      expect((frac.numer.children[0] as any).value).toBe('b');
    }
  });

  test('x_{i_j} nested subscript', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });

    s = handleInput(s, char('x'));
    s = handleInput(s, char('_'));
    // Now in x's sub slot
    s = handleInput(s, char('i'));
    s = handleInput(s, char('_'));
    // Now in i's sub slot (nested)

    expect(s.cursor.path).toHaveLength(2);
    expect(s.cursor.path[0].slot).toBe('sub');
    expect(s.cursor.path[1].slot).toBe('sub');

    s = handleInput(s, char('j'));

    // Verify nested structure
    const outerSub = s.root.children[0];
    expect(outerSub.tag).toBe('Sub');
    if (outerSub.tag === 'Sub') {
      const innerSub = outerSub.sub.children[0];
      expect(innerSub.tag).toBe('Sub');
      if (innerSub.tag === 'Sub') {
        expect((innerSub.base.children[0] as any).value).toBe('i');
        expect((innerSub.sub.children[0] as any).value).toBe('j');
      }
    }
  });

  test('type \\frac then immediate backspace exits and renders valid LaTeX', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });

    // Type some content first
    s = handleInput(s, char('a'));
    s = handleInput(s, char('+'));

    // Type \frac
    s = handleInput(s, char('\\'));
    s = handleInput(s, char('f'));
    s = handleInput(s, char('r'));
    s = handleInput(s, char('a'));
    s = handleInput(s, char('c'));

    // Cursor is inside numer at offset 0
    expect(s.cursor.path).toHaveLength(1);
    expect(s.cursor.path[0].slot).toBe('numer');
    expect(s.cursor.offset).toBe(0);

    // Backspace at start of numer — should exit to before frac
    s = handleInput(s, backspace());
    expect(s.cursor.path).toEqual([]);
    expect(s.cursor.offset).toBe(2); // before the frac

    // Verify rendered LaTeX has valid structure
    const latex = renderToLatex(s);
    expect(latex).toContain('\\frac');
    // The \frac should have balanced braces — check no empty double-braces
    expect(latex).not.toContain('{{}}');

    // Two more backspaces: first deletes '+', then deletes 'a'
    s = handleInput(s, backspace());
    expect(s.root.children).toHaveLength(2); // 'a' and frac
    s = handleInput(s, backspace());
    expect(s.root.children).toHaveLength(1); // just frac
  });

  test('(a+b)^2 delimiter then superscript', () => {
    const root = mkRow([]);
    let s = mkState(root, { path: [], offset: 0 });

    s = handleInput(s, char('('));
    s = handleInput(s, char('a'));
    s = handleInput(s, char('+'));
    s = handleInput(s, char('b'));
    s = handleInput(s, char(')'));
    // After ), cursor is at root offset 1 (after delimiter)
    s = handleInput(s, char('^'));
    // Should wrap the delimiter as base of Sup

    expect(s.root.children).toHaveLength(1);
    const sup = s.root.children[0];
    expect(sup.tag).toBe('Sup');
    if (sup.tag === 'Sup') {
      expect(sup.base.children[0].tag).toBe('Delimiter');
    }
    expect(s.cursor.path[0].slot).toBe('sup');

    s = handleInput(s, char('2'));
    if (s.root.children[0].tag === 'Sup') {
      expect((s.root.children[0] as any).sup.children[0].value).toBe('2');
    }
  });
});

// ============================================================================
// Hole interaction — typing replaces Holes, navigation lands before Holes
// ============================================================================

describe('Hole interaction', () => {
  test('\\int then up then type replaces upper Hole (not appends)', () => {
    let s = mkState(mkRow([]), { path: [], offset: 0 });

    // Type \int — creates BigOp with below=[Hole], above=[Hole]
    s = handleInput(s, char('\\'));
    s = handleInput(s, char('i'));
    s = handleInput(s, char('n'));
    s = handleInput(s, char('t'));
    // Now in below slot at offset 0

    // Type "0" in the lower bound (replaces Hole)
    s = handleInput(s, char('0'));
    expect(resolveRow(s.root, s.cursor.path).children[0].tag).toBe('Symbol');

    // Press up to go to upper bound
    s = moveUp(s);
    expect(s.cursor.path[0].slot).toBe('above');
    // Cursor should be at offset 0, BEFORE the Hole
    expect(s.cursor.offset).toBe(0);

    // Type 'x' — should replace the Hole
    s = handleInput(s, char('x'));
    const aboveRow = resolveRow(s.root, s.cursor.path);
    // Should have exactly 1 child: Symbol('x'), NOT [Hole, Symbol('x')]
    expect(aboveRow.children).toHaveLength(1);
    expect(aboveRow.children[0].tag).toBe('Symbol');
    expect((aboveRow.children[0] as any).value).toBe('x');
  });

  test('\\frac then type replaces numer Hole, right then type replaces denom Hole', () => {
    let s = mkState(mkRow([]), { path: [], offset: 0 });

    // Type \frac
    s = handleInput(s, char('\\'));
    s = handleInput(s, char('f'));
    s = handleInput(s, char('r'));
    s = handleInput(s, char('a'));
    s = handleInput(s, char('c'));
    // Now in numer slot at offset 0, with Hole

    // Type 'a' — replaces Hole
    s = handleInput(s, char('a'));
    const numerRow = resolveRow(s.root, s.cursor.path);
    expect(numerRow.children).toHaveLength(1);
    expect((numerRow.children[0] as any).value).toBe('a');

    // moveDown to denom
    s = moveDown(s);
    expect(s.cursor.path[0].slot).toBe('denom');
    expect(s.cursor.offset).toBe(0);

    // Type 'b' — replaces Hole
    s = handleInput(s, char('b'));
    const denomRow = resolveRow(s.root, s.cursor.path);
    expect(denomRow.children).toHaveLength(1);
    expect((denomRow.children[0] as any).value).toBe('b');
  });

  test('moveLeft into Hole-only slot then type replaces Hole', () => {
    // Frac with numer=[Hole], denom has content
    const frac = mkFrac(mkRow([mkHole()]), mkRow([mkSymbol('b')]));
    const root = mkRow([frac]);
    // Start at denom offset 0
    let s = mkState(root, { path: [{ nodeId: frac.id, slot: 'denom' }], offset: 0 });

    // moveLeft → enters numer
    s = moveLeft(s);
    expect(s.cursor.path[0].slot).toBe('numer');
    expect(s.cursor.offset).toBe(0);

    // Type 'a' — replaces Hole
    s = handleInput(s, char('a'));
    const numerRow = resolveRow(s.root, s.cursor.path);
    expect(numerRow.children).toHaveLength(1);
    expect(numerRow.children[0].tag).toBe('Symbol');
  });

  test('typing at end of row where last child is Hole replaces it (defensive)', () => {
    // Manually construct a state where cursor is after a Hole (shouldn't happen normally)
    const row = mkRow([mkHole()]);
    let s = mkState(row, { path: [], offset: 1 }); // offset 1 = after Hole

    // Type 'x' — should replace the Hole, not create [Hole, x]
    s = handleInput(s, char('x'));
    expect(s.root.children).toHaveLength(1);
    expect(s.root.children[0].tag).toBe('Symbol');
    expect((s.root.children[0] as any).value).toBe('x');
  });

  test('\\sum then up then type multiple chars in upper bound', () => {
    let s = mkState(mkRow([]), { path: [], offset: 0 });

    // Type \sum
    s = handleInput(s, char('\\'));
    s = handleInput(s, char('s'));
    s = handleInput(s, char('u'));
    s = handleInput(s, char('m'));
    // Now in below slot

    // Type i=0
    s = handleInput(s, char('i'));
    s = handleInput(s, char('='));
    s = handleInput(s, char('0'));

    // Press up to go to upper bound
    s = moveUp(s);
    expect(s.cursor.path[0].slot).toBe('above');
    expect(s.cursor.offset).toBe(0);

    // Type 'n' — replaces Hole
    s = handleInput(s, char('n'));
    const aboveRow = resolveRow(s.root, s.cursor.path);
    expect(aboveRow.children).toHaveLength(1);
    expect((aboveRow.children[0] as any).value).toBe('n');
  });
});

// ============================================================================
// Text mode (space → text → space)
// ============================================================================

describe('text mode', () => {
  test('space enters text mode', () => {
    let s = mkState(mkRow([]), { path: [], offset: 0 });
    s = handleInput(s, char(' '));
    expect(s.textBuffer).toBe('');
    expect(s.root.children).toHaveLength(0);
  });

  test('letters accumulate in text buffer', () => {
    let s = mkState(mkRow([]), { path: [], offset: 0 });
    s = handleInput(s, char(' '));
    s = handleInput(s, char('a'));
    s = handleInput(s, char('n'));
    s = handleInput(s, char('d'));
    expect(s.textBuffer).toBe('and');
  });

  test('second space terminates and inserts TextNode', () => {
    let s = mkState(mkRow([]), { path: [], offset: 0 });
    s = handleInput(s, char(' '));
    s = handleInput(s, char('a'));
    s = handleInput(s, char('n'));
    s = handleInput(s, char('d'));
    s = handleInput(s, char(' '));
    expect(s.textBuffer).toBe(null);
    expect(s.root.children).toHaveLength(1);
    expect(s.root.children[0].tag).toBe('Text');
    expect((s.root.children[0] as any).content).toBe('and');
    expect(s.cursor.offset).toBe(1);
  });

  test('empty text buffer canceled by space (no node)', () => {
    let s = mkState(mkRow([]), { path: [], offset: 0 });
    s = handleInput(s, char(' '));
    s = handleInput(s, char(' '));
    expect(s.textBuffer).toBe(null);
    expect(s.root.children).toHaveLength(0);
  });

  test('backspace removes last char in text buffer', () => {
    let s: MathEditorState = { ...mkState(mkRow([]), { path: [], offset: 0 }), textBuffer: 'and' };
    s = handleInput(s, backspace());
    expect(s.textBuffer).toBe('an');
  });

  test('backspace on empty text buffer cancels text mode', () => {
    let s: MathEditorState = { ...mkState(mkRow([]), { path: [], offset: 0 }), textBuffer: '' };
    s = handleInput(s, backspace());
    expect(s.textBuffer).toBe(null);
  });

  test('non-letter char terminates text and processes char', () => {
    let s = mkState(mkRow([]), { path: [], offset: 0 });
    s = handleInput(s, char(' '));
    s = handleInput(s, char('h'));
    s = handleInput(s, char('i'));
    s = handleInput(s, char('+'));
    expect(s.textBuffer).toBe(null);
    expect(s.root.children).toHaveLength(2); // TextNode('hi'), Symbol('+')
    expect(s.root.children[0].tag).toBe('Text');
    expect((s.root.children[0] as any).content).toBe('hi');
    expect(s.root.children[1].tag).toBe('Symbol');
    expect((s.root.children[1] as any).value).toBe('+');
  });

  test('backslash terminates text and enters command mode', () => {
    let s = mkState(mkRow([]), { path: [], offset: 0 });
    s = handleInput(s, char(' '));
    s = handleInput(s, char('o'));
    s = handleInput(s, char('r'));
    s = handleInput(s, char('\\'));
    expect(s.textBuffer).toBe(null);
    expect(s.commandBuffer).toBe('');
    expect(s.root.children).toHaveLength(1);
    expect((s.root.children[0] as any).content).toBe('or');
  });

  test('backspace on a TextNode (after creation) deletes it', () => {
    const root = mkRow([mkText('and')]);
    let s = mkState(root, { path: [], offset: 1 });
    s = handleInput(s, backspace());
    expect(s.root.children).toHaveLength(0);
    expect(s.cursor.offset).toBe(0);
  });

  test('full sequence: a <sp>and<sp> b', () => {
    let s = mkState(mkRow([]), { path: [], offset: 0 });
    s = handleInput(s, char('a'));
    s = handleInput(s, char(' '));
    s = handleInput(s, char('a'));
    s = handleInput(s, char('n'));
    s = handleInput(s, char('d'));
    s = handleInput(s, char(' '));
    s = handleInput(s, char('b'));
    expect(s.root.children).toHaveLength(3);
    expect(s.root.children[0].tag).toBe('Symbol');
    expect(s.root.children[1].tag).toBe('Text');
    expect((s.root.children[1] as any).content).toBe('and');
    expect(s.root.children[2].tag).toBe('Symbol');
  });

  test('\\text command enters text mode', () => {
    let s = mkState(mkRow([]), { path: [], offset: 0 });
    s = handleInput(s, char('\\'));
    s = handleInput(s, char('t'));
    s = handleInput(s, char('e'));
    s = handleInput(s, char('x'));
    s = handleInput(s, char('t'));
    // 'text' is unique in SYMBOL_TABLE → auto-fires → enters text mode
    expect(s.commandBuffer).toBe(null);
    expect(s.textBuffer).toBe('');
  });
});
