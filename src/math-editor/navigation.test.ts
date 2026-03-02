import { describe, test, expect, beforeEach } from 'vitest';
import { resetIds, mkRow, mkSymbol, mkHole, mkFrac, mkSub, mkSup, mkSubSup, mkBigOp, mkDelimiter, MathEditorState } from './types';
import { moveRight, moveLeft, moveUp, moveDown, exitCompound } from './navigation';

beforeEach(() => resetIds());

function mkState(root: ReturnType<typeof mkRow>, cursor: MathEditorState['cursor']): MathEditorState {
  return { root, cursor, commandBuffer: null, textBuffer: null };
}

// ============================================================================
// moveRight
// ============================================================================

describe('moveRight', () => {
  test('moves past a symbol', () => {
    const root = mkRow([mkSymbol('x'), mkSymbol('y')]);
    const s = mkState(root, { path: [], offset: 0 });
    const s2 = moveRight(s);
    expect(s2.cursor.offset).toBe(1);
    expect(s2.cursor.path).toEqual([]);
  });

  test('moves past second symbol to end', () => {
    const root = mkRow([mkSymbol('x'), mkSymbol('y')]);
    const s = mkState(root, { path: [], offset: 1 });
    const s2 = moveRight(s);
    expect(s2.cursor.offset).toBe(2);
  });

  test('at end of root, does nothing', () => {
    const root = mkRow([mkSymbol('x')]);
    const s = mkState(root, { path: [], offset: 1 });
    const s2 = moveRight(s);
    expect(s2.cursor.offset).toBe(1);
  });

  test('enters fraction numerator', () => {
    const frac = mkFrac(mkRow([mkSymbol('a')]), mkRow([mkSymbol('b')]));
    const root = mkRow([frac]);
    const s = mkState(root, { path: [], offset: 0 });
    const s2 = moveRight(s);
    // Should enter the numer slot
    expect(s2.cursor.path).toEqual([{ nodeId: frac.id, slot: 'numer' }]);
    expect(s2.cursor.offset).toBe(0);
  });

  test('exits numerator into denominator', () => {
    const frac = mkFrac(mkRow([mkSymbol('a')]), mkRow([mkSymbol('b')]));
    const root = mkRow([frac]);
    // Cursor at end of numerator
    const s = mkState(root, { path: [{ nodeId: frac.id, slot: 'numer' }], offset: 1 });
    const s2 = moveRight(s);
    // Should enter denom
    expect(s2.cursor.path).toEqual([{ nodeId: frac.id, slot: 'denom' }]);
    expect(s2.cursor.offset).toBe(0);
  });

  test('exits denominator to after fraction', () => {
    const frac = mkFrac(mkRow([mkSymbol('a')]), mkRow([mkSymbol('b')]));
    const root = mkRow([frac, mkSymbol('c')]);
    // Cursor at end of denominator
    const s = mkState(root, { path: [{ nodeId: frac.id, slot: 'denom' }], offset: 1 });
    const s2 = moveRight(s);
    // Should exit to root, after frac (offset 1)
    expect(s2.cursor.path).toEqual([]);
    expect(s2.cursor.offset).toBe(1);
  });

  test('full traversal: a frac{b}{c} d', () => {
    const frac = mkFrac(mkRow([mkSymbol('b')]), mkRow([mkSymbol('c')]));
    const root = mkRow([mkSymbol('a'), frac, mkSymbol('d')]);
    let s = mkState(root, { path: [], offset: 0 });

    // Step 1: past 'a'
    s = moveRight(s);
    expect(s.cursor).toEqual({ path: [], offset: 1 });

    // Step 2: enter frac numer
    s = moveRight(s);
    expect(s.cursor.path).toEqual([{ nodeId: frac.id, slot: 'numer' }]);
    expect(s.cursor.offset).toBe(0);

    // Step 3: past 'b' in numer
    s = moveRight(s);
    expect(s.cursor.path).toEqual([{ nodeId: frac.id, slot: 'numer' }]);
    expect(s.cursor.offset).toBe(1);

    // Step 4: exit numer, enter denom
    s = moveRight(s);
    expect(s.cursor.path).toEqual([{ nodeId: frac.id, slot: 'denom' }]);
    expect(s.cursor.offset).toBe(0);

    // Step 5: past 'c' in denom
    s = moveRight(s);
    expect(s.cursor.path).toEqual([{ nodeId: frac.id, slot: 'denom' }]);
    expect(s.cursor.offset).toBe(1);

    // Step 6: exit frac
    s = moveRight(s);
    expect(s.cursor).toEqual({ path: [], offset: 2 });

    // Step 7: past 'd'
    s = moveRight(s);
    expect(s.cursor).toEqual({ path: [], offset: 3 });

    // Step 8: at end, no change
    s = moveRight(s);
    expect(s.cursor).toEqual({ path: [], offset: 3 });
  });

  test('enters subscript base then sub', () => {
    const sub = mkSub(mkRow([mkSymbol('x')]), mkRow([mkSymbol('2')]));
    const root = mkRow([sub]);
    let s = mkState(root, { path: [], offset: 0 });

    // Enter base
    s = moveRight(s);
    expect(s.cursor.path).toEqual([{ nodeId: sub.id, slot: 'base' }]);
    expect(s.cursor.offset).toBe(0);

    // Past 'x' in base
    s = moveRight(s);
    expect(s.cursor.offset).toBe(1);

    // Exit base, enter sub
    s = moveRight(s);
    expect(s.cursor.path).toEqual([{ nodeId: sub.id, slot: 'sub' }]);
    expect(s.cursor.offset).toBe(0);

    // Past '2' in sub
    s = moveRight(s);
    expect(s.cursor.offset).toBe(1);

    // Exit sub, exit compound node
    s = moveRight(s);
    expect(s.cursor).toEqual({ path: [], offset: 1 });
  });

  test('enters BigOp below then above', () => {
    const op = mkBigOp('sum', mkRow([mkSymbol('i')]), mkRow([mkSymbol('n')]));
    const root = mkRow([op]);
    let s = mkState(root, { path: [], offset: 0 });

    // Enter below
    s = moveRight(s);
    expect(s.cursor.path).toEqual([{ nodeId: op.id, slot: 'below' }]);

    // Past 'i', exit below, enter above
    s = moveRight(s);
    s = moveRight(s);
    expect(s.cursor.path).toEqual([{ nodeId: op.id, slot: 'above' }]);

    // Past 'n', exit above, enter body
    s = moveRight(s);
    s = moveRight(s);
    expect(s.cursor.path).toEqual([{ nodeId: op.id, slot: 'body' }]);

    // Past body Hole, exit BigOp
    s = moveRight(s);
    s = moveRight(s);
    expect(s.cursor).toEqual({ path: [], offset: 1 });
  });
});

// ============================================================================
// moveLeft
// ============================================================================

describe('moveLeft', () => {
  test('moves before a symbol', () => {
    const root = mkRow([mkSymbol('x'), mkSymbol('y')]);
    const s = mkState(root, { path: [], offset: 2 });
    const s2 = moveLeft(s);
    expect(s2.cursor.offset).toBe(1);
  });

  test('at start of root, does nothing', () => {
    const root = mkRow([mkSymbol('x')]);
    const s = mkState(root, { path: [], offset: 0 });
    const s2 = moveLeft(s);
    expect(s2.cursor.offset).toBe(0);
  });

  test('enters fraction from right into denom end', () => {
    const frac = mkFrac(mkRow([mkSymbol('a')]), mkRow([mkSymbol('b')]));
    const root = mkRow([frac]);
    const s = mkState(root, { path: [], offset: 1 });
    const s2 = moveLeft(s);
    // Should enter denom (last slot) at end
    expect(s2.cursor.path).toEqual([{ nodeId: frac.id, slot: 'denom' }]);
    expect(s2.cursor.offset).toBe(1);
  });

  test('left from denom start enters numer end', () => {
    const frac = mkFrac(mkRow([mkSymbol('a')]), mkRow([mkSymbol('b')]));
    const root = mkRow([frac]);
    const s = mkState(root, { path: [{ nodeId: frac.id, slot: 'denom' }], offset: 0 });
    const s2 = moveLeft(s);
    // Should enter numer at end
    expect(s2.cursor.path).toEqual([{ nodeId: frac.id, slot: 'numer' }]);
    expect(s2.cursor.offset).toBe(1);
  });

  test('left from numer start exits fraction', () => {
    const frac = mkFrac(mkRow([mkSymbol('a')]), mkRow([mkSymbol('b')]));
    const root = mkRow([mkSymbol('z'), frac]);
    const s = mkState(root, { path: [{ nodeId: frac.id, slot: 'numer' }], offset: 0 });
    const s2 = moveLeft(s);
    // Should exit to root, before frac (offset 1)
    expect(s2.cursor.path).toEqual([]);
    expect(s2.cursor.offset).toBe(1);
  });

  test('full reverse traversal: a frac{b}{c} d', () => {
    const frac = mkFrac(mkRow([mkSymbol('b')]), mkRow([mkSymbol('c')]));
    const root = mkRow([mkSymbol('a'), frac, mkSymbol('d')]);
    let s = mkState(root, { path: [], offset: 3 });

    s = moveLeft(s); // before 'd' → offset 2
    expect(s.cursor).toEqual({ path: [], offset: 2 });

    s = moveLeft(s); // enter denom end
    expect(s.cursor.path).toEqual([{ nodeId: frac.id, slot: 'denom' }]);
    expect(s.cursor.offset).toBe(1);

    s = moveLeft(s); // before 'c'
    expect(s.cursor.offset).toBe(0);

    s = moveLeft(s); // enter numer end
    expect(s.cursor.path).toEqual([{ nodeId: frac.id, slot: 'numer' }]);
    expect(s.cursor.offset).toBe(1);

    s = moveLeft(s); // before 'b'
    expect(s.cursor.offset).toBe(0);

    s = moveLeft(s); // exit frac → before frac (offset 1)
    expect(s.cursor).toEqual({ path: [], offset: 1 });

    s = moveLeft(s); // before 'a' → offset 0
    expect(s.cursor).toEqual({ path: [], offset: 0 });

    s = moveLeft(s); // at start, no change
    expect(s.cursor).toEqual({ path: [], offset: 0 });
  });
});

// ============================================================================
// moveUp / moveDown
// ============================================================================

describe('moveUp', () => {
  test('from denom to numer in frac', () => {
    const frac = mkFrac(mkRow([mkSymbol('a')]), mkRow([mkSymbol('b')]));
    const root = mkRow([frac]);
    const s = mkState(root, { path: [{ nodeId: frac.id, slot: 'denom' }], offset: 1 });
    const s2 = moveUp(s);
    expect(s2.cursor.path).toEqual([{ nodeId: frac.id, slot: 'numer' }]);
    // Offset clamped to numer length
    expect(s2.cursor.offset).toBe(1);
  });

  test('from numer in frac, up does nothing', () => {
    const frac = mkFrac(mkRow([mkSymbol('a')]), mkRow([mkSymbol('b')]));
    const root = mkRow([frac]);
    const s = mkState(root, { path: [{ nodeId: frac.id, slot: 'numer' }], offset: 0 });
    const s2 = moveUp(s);
    expect(s2).toBe(s);
  });

  test('from sub slot to base in Sub', () => {
    const sub = mkSub(mkRow([mkSymbol('x')]), mkRow([mkSymbol('2')]));
    const root = mkRow([sub]);
    const s = mkState(root, { path: [{ nodeId: sub.id, slot: 'sub' }], offset: 0 });
    const s2 = moveUp(s);
    expect(s2.cursor.path).toEqual([{ nodeId: sub.id, slot: 'base' }]);
  });

  test('from base to sup in SubSup', () => {
    const ss = mkSubSup(mkRow([mkSymbol('x')]), mkRow([mkSymbol('i')]), mkRow([mkSymbol('2')]));
    const root = mkRow([ss]);
    const s = mkState(root, { path: [{ nodeId: ss.id, slot: 'base' }], offset: 0 });
    const s2 = moveUp(s);
    expect(s2.cursor.path).toEqual([{ nodeId: ss.id, slot: 'sup' }]);
  });

  test('from below to above in BigOp', () => {
    const op = mkBigOp('sum', mkRow([mkSymbol('i')]), mkRow([mkSymbol('n')]));
    const root = mkRow([op]);
    const s = mkState(root, { path: [{ nodeId: op.id, slot: 'below' }], offset: 0 });
    const s2 = moveUp(s);
    expect(s2.cursor.path).toEqual([{ nodeId: op.id, slot: 'above' }]);
  });

  test('from parent row enters frac numer (up)', () => {
    const frac = mkFrac(mkRow([mkSymbol('a')]), mkRow([mkSymbol('b')]));
    const root = mkRow([frac, mkSymbol('x')]);
    // Cursor at root offset 1 (after frac, before x)
    const s = mkState(root, { path: [], offset: 1 });
    const s2 = moveUp(s);
    // Should enter frac's numer from the left node
    expect(s2.cursor.path).toEqual([{ nodeId: frac.id, slot: 'numer' }]);
  });

  test('from parent row enters BigOp above (up)', () => {
    const op = mkBigOp('sum', mkRow([mkSymbol('i')]), mkRow([mkSymbol('n')]));
    const root = mkRow([op, mkSymbol('x')]);
    // Cursor at offset 0 (before BigOp)
    const s = mkState(root, { path: [], offset: 0 });
    const s2 = moveUp(s);
    expect(s2.cursor.path).toEqual([{ nodeId: op.id, slot: 'above' }]);
  });
});

describe('moveDown', () => {
  test('from numer to denom in frac', () => {
    const frac = mkFrac(mkRow([mkSymbol('a')]), mkRow([mkSymbol('b')]));
    const root = mkRow([frac]);
    const s = mkState(root, { path: [{ nodeId: frac.id, slot: 'numer' }], offset: 0 });
    const s2 = moveDown(s);
    expect(s2.cursor.path).toEqual([{ nodeId: frac.id, slot: 'denom' }]);
    expect(s2.cursor.offset).toBe(0);
  });

  test('from base to sub in SubSup', () => {
    const ss = mkSubSup(mkRow([mkSymbol('x')]), mkRow([mkSymbol('i')]), mkRow([mkSymbol('2')]));
    const root = mkRow([ss]);
    const s = mkState(root, { path: [{ nodeId: ss.id, slot: 'base' }], offset: 0 });
    const s2 = moveDown(s);
    expect(s2.cursor.path).toEqual([{ nodeId: ss.id, slot: 'sub' }]);
  });

  test('from parent row enters frac denom (down)', () => {
    const frac = mkFrac(mkRow([mkSymbol('a')]), mkRow([mkSymbol('b')]));
    const root = mkRow([frac]);
    const s = mkState(root, { path: [], offset: 0 });
    const s2 = moveDown(s);
    expect(s2.cursor.path).toEqual([{ nodeId: frac.id, slot: 'denom' }]);
  });

  test('from parent row enters BigOp below (down)', () => {
    const op = mkBigOp('sum', mkRow([mkSymbol('i')]), mkRow([mkSymbol('n')]));
    const root = mkRow([op]);
    const s = mkState(root, { path: [], offset: 0 });
    const s2 = moveDown(s);
    expect(s2.cursor.path).toEqual([{ nodeId: op.id, slot: 'below' }]);
  });

  test('offset is clamped to target row length', () => {
    const frac = mkFrac(mkRow([mkSymbol('a'), mkSymbol('b'), mkSymbol('c')]), mkRow([mkSymbol('d')]));
    const root = mkRow([frac]);
    // Cursor at end of numer (offset 3)
    const s = mkState(root, { path: [{ nodeId: frac.id, slot: 'numer' }], offset: 3 });
    const s2 = moveDown(s);
    expect(s2.cursor.path).toEqual([{ nodeId: frac.id, slot: 'denom' }]);
    // denom has 1 child, offset clamped to 1
    expect(s2.cursor.offset).toBe(1);
  });
});

// ============================================================================
// Hole-aware cursor placement
// ============================================================================

describe('Hole-aware cursor placement', () => {
  test('moveUp into Hole-only slot places cursor at offset 0', () => {
    // \int with Hole in both below and above slots
    const op = mkBigOp('int', mkRow([mkHole()]), mkRow([mkHole()]));
    const root = mkRow([op]);
    // Cursor in below slot at offset 1 (could happen with clamping)
    const s = mkState(root, { path: [{ nodeId: op.id, slot: 'below' }], offset: 1 });
    const s2 = moveUp(s);
    expect(s2.cursor.path).toEqual([{ nodeId: op.id, slot: 'above' }]);
    // Should be at 0, NOT 1 (before the Hole, not after it)
    expect(s2.cursor.offset).toBe(0);
  });

  test('moveDown into Hole-only slot places cursor at offset 0', () => {
    const frac = mkFrac(mkRow([mkSymbol('a')]), mkRow([mkHole()]));
    const root = mkRow([frac]);
    const s = mkState(root, { path: [{ nodeId: frac.id, slot: 'numer' }], offset: 1 });
    const s2 = moveDown(s);
    expect(s2.cursor.path).toEqual([{ nodeId: frac.id, slot: 'denom' }]);
    expect(s2.cursor.offset).toBe(0);
  });

  test('moveLeft into Hole-only slot places cursor at offset 0', () => {
    const frac = mkFrac(mkRow([mkHole()]), mkRow([mkSymbol('b')]));
    const root = mkRow([frac]);
    // Cursor at start of denom → moveLeft enters numer at end
    const s = mkState(root, { path: [{ nodeId: frac.id, slot: 'denom' }], offset: 0 });
    const s2 = moveLeft(s);
    expect(s2.cursor.path).toEqual([{ nodeId: frac.id, slot: 'numer' }]);
    // Numer is [Hole] — cursor should be at 0, not 1
    expect(s2.cursor.offset).toBe(0);
  });

  test('moveLeft entering compound node with Hole-only last slot', () => {
    const frac = mkFrac(mkRow([mkSymbol('a')]), mkRow([mkHole()]));
    const root = mkRow([frac]);
    // Cursor after frac → moveLeft enters denom (last slot)
    const s = mkState(root, { path: [], offset: 1 });
    const s2 = moveLeft(s);
    expect(s2.cursor.path).toEqual([{ nodeId: frac.id, slot: 'denom' }]);
    expect(s2.cursor.offset).toBe(0);
  });

  test('moveUp from parent row into Hole-only slot at offset 0', () => {
    const op = mkBigOp('sum', mkRow([mkHole()]), mkRow([mkHole()]));
    const root = mkRow([op]);
    const s = mkState(root, { path: [], offset: 0 });
    const s2 = moveUp(s);
    expect(s2.cursor.path).toEqual([{ nodeId: op.id, slot: 'above' }]);
    expect(s2.cursor.offset).toBe(0);
  });

  test('moveDown from parent row (left node) into Hole-only slot', () => {
    const op = mkBigOp('sum', mkRow([mkHole()]), mkRow([mkHole()]));
    const root = mkRow([op]);
    // Cursor after the BigOp → left node is the BigOp
    const s = mkState(root, { path: [], offset: 1 });
    const s2 = moveDown(s);
    expect(s2.cursor.path).toEqual([{ nodeId: op.id, slot: 'below' }]);
    // Should be 0 (before the Hole), not 1
    expect(s2.cursor.offset).toBe(0);
  });

  test('offset clamped to non-Hole content in mixed row', () => {
    // Row with [Symbol('a'), Hole] — effective end is 1
    const frac = mkFrac(mkRow([mkSymbol('x'), mkSymbol('y'), mkSymbol('z')]), mkRow([mkSymbol('a'), mkHole()]));
    const root = mkRow([frac]);
    // Cursor at end of numer (offset 3) → moveDown to denom
    const s = mkState(root, { path: [{ nodeId: frac.id, slot: 'numer' }], offset: 3 });
    const s2 = moveDown(s);
    expect(s2.cursor.path).toEqual([{ nodeId: frac.id, slot: 'denom' }]);
    // denom is [a, Hole], effective end = 1, clamped from 3 to 1
    expect(s2.cursor.offset).toBe(1);
  });
});

// ============================================================================
// Vertical navigation bubble-up through nested structures
// ============================================================================

describe('moveDown/moveUp bubble-up through hierarchy', () => {
  test('down from inside delimiter in frac numer reaches denom', () => {
    // frac{ n (n+1) }{ 2 } — cursor inside the parens in the numerator
    const delim = mkDelimiter('(', ')', mkRow([mkSymbol('n'), mkSymbol('+'), mkSymbol('1')]));
    const frac = mkFrac(mkRow([mkSymbol('n'), delim]), mkRow([mkSymbol('2')]));
    const root = mkRow([frac]);

    // Cursor inside delimiter's inner row, at offset 1 (between 'n' and '+')
    const s = mkState(root, {
      path: [
        { nodeId: frac.id, slot: 'numer' },
        { nodeId: delim.id, slot: 'inner' },
      ],
      offset: 1,
    });
    const s2 = moveDown(s);

    // Should bubble up: Delimiter has no vertical neighbors,
    // but its parent Frac does (numer → denom)
    expect(s2.cursor.path).toEqual([{ nodeId: frac.id, slot: 'denom' }]);
    expect(s2.cursor.offset).toBe(1); // clamped to denom length
  });

  test('up from inside delimiter in frac denom reaches numer', () => {
    const delim = mkDelimiter('(', ')', mkRow([mkSymbol('a')]));
    const frac = mkFrac(mkRow([mkSymbol('x')]), mkRow([delim]));
    const root = mkRow([frac]);

    // Cursor inside delimiter's inner row in the denominator
    const s = mkState(root, {
      path: [
        { nodeId: frac.id, slot: 'denom' },
        { nodeId: delim.id, slot: 'inner' },
      ],
      offset: 0,
    });
    const s2 = moveUp(s);

    expect(s2.cursor.path).toEqual([{ nodeId: frac.id, slot: 'numer' }]);
    expect(s2.cursor.offset).toBe(0);
  });

  test('down from deeply nested delimiter in frac numer', () => {
    // frac{ ( (x) ) }{ y } — delimiter inside delimiter inside frac numer
    const innerDelim = mkDelimiter('(', ')', mkRow([mkSymbol('x')]));
    const outerDelim = mkDelimiter('(', ')', mkRow([innerDelim]));
    const frac = mkFrac(mkRow([outerDelim]), mkRow([mkSymbol('y')]));
    const root = mkRow([frac]);

    // Cursor deep inside innermost delimiter
    const s = mkState(root, {
      path: [
        { nodeId: frac.id, slot: 'numer' },
        { nodeId: outerDelim.id, slot: 'inner' },
        { nodeId: innerDelim.id, slot: 'inner' },
      ],
      offset: 0,
    });
    const s2 = moveDown(s);

    // Should bubble up through both delimiters to reach frac denom
    expect(s2.cursor.path).toEqual([{ nodeId: frac.id, slot: 'denom' }]);
  });

  test('down from delimiter in sub base reaches sub slot', () => {
    // x_(delim) with cursor inside the delimiter → should reach sub
    const delim = mkDelimiter('(', ')', mkRow([mkSymbol('a')]));
    const sub = mkSub(mkRow([delim]), mkRow([mkSymbol('2')]));
    const root = mkRow([sub]);

    const s = mkState(root, {
      path: [
        { nodeId: sub.id, slot: 'base' },
        { nodeId: delim.id, slot: 'inner' },
      ],
      offset: 0,
    });
    const s2 = moveDown(s);

    expect(s2.cursor.path).toEqual([{ nodeId: sub.id, slot: 'sub' }]);
  });

  test('up from delimiter in BigOp below reaches above', () => {
    const delim = mkDelimiter('(', ')', mkRow([mkSymbol('i')]));
    const op = mkBigOp('sum', mkRow([delim]), mkRow([mkSymbol('n')]));
    const root = mkRow([op]);

    const s = mkState(root, {
      path: [
        { nodeId: op.id, slot: 'below' },
        { nodeId: delim.id, slot: 'inner' },
      ],
      offset: 0,
    });
    const s2 = moveUp(s);

    expect(s2.cursor.path).toEqual([{ nodeId: op.id, slot: 'above' }]);
  });

  test('no vertical neighbor at any level returns unchanged state', () => {
    // Delimiter at root level — no vertical neighbors anywhere
    const delim = mkDelimiter('(', ')', mkRow([mkSymbol('x')]));
    const root = mkRow([delim]);

    const s = mkState(root, {
      path: [{ nodeId: delim.id, slot: 'inner' }],
      offset: 0,
    });
    const s2 = moveDown(s);

    // No vertical neighbor found — state unchanged
    expect(s2).toBe(s);
  });
});

// ============================================================================
// exitCompound — Escape key
// ============================================================================

describe('exitCompound', () => {
  test('from BigOp below → cursor after BigOp', () => {
    const op = mkBigOp('sum', mkRow([mkSymbol('i')]), mkRow([mkSymbol('n')]));
    const root = mkRow([op, mkSymbol('x')]);
    const s = mkState(root, { path: [{ nodeId: op.id, slot: 'below' }], offset: 1 });
    const s2 = exitCompound(s);
    expect(s2.cursor).toEqual({ path: [], offset: 1 });
  });

  test('from BigOp above → cursor after BigOp', () => {
    const op = mkBigOp('sum', mkRow([mkSymbol('i')]), mkRow([mkSymbol('n')]));
    const root = mkRow([op, mkSymbol('x')]);
    const s = mkState(root, { path: [{ nodeId: op.id, slot: 'above' }], offset: 0 });
    const s2 = exitCompound(s);
    expect(s2.cursor).toEqual({ path: [], offset: 1 });
  });

  test('from Frac numer → cursor after Frac', () => {
    const frac = mkFrac(mkRow([mkSymbol('a')]), mkRow([mkSymbol('b')]));
    const root = mkRow([frac, mkSymbol('+')]);
    const s = mkState(root, { path: [{ nodeId: frac.id, slot: 'numer' }], offset: 0 });
    const s2 = exitCompound(s);
    expect(s2.cursor).toEqual({ path: [], offset: 1 });
  });

  test('at root → no change', () => {
    const root = mkRow([mkSymbol('x')]);
    const s = mkState(root, { path: [], offset: 0 });
    const s2 = exitCompound(s);
    expect(s2).toBe(s);
  });
});
