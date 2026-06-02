import { describe, expect, test } from 'vitest';
import {
  codeWithInfosToMathRow,
  tokenizeText,
  SUBEXPR_HTML_PREFIX,
  type TaggedJson,
} from './codeWithInfos';
import type { GroupNode, MathNode, SymbolNode } from '../math-editor/types';

const sym = (n: MathNode): string => (n as SymbolNode).value;

describe('tokenizeText', () => {
  test('keeps identifiers whole, drops whitespace', () => {
    const nodes = tokenizeText('Nat.succ n');
    expect(nodes.map(sym)).toEqual(['Nat.succ', 'n']);
  });

  test('translates unicode operators to LaTeX', () => {
    expect(tokenizeText('→').map(sym)).toEqual(['\\to']);
    expect(tokenizeText('a ≤ b').map(sym)).toEqual(['a', '\\leq', 'b']);
    expect(tokenizeText('ℕ').map(sym)).toEqual(['\\mathbb{N}']);
  });

  test('splits punctuation into its own symbols', () => {
    expect(tokenizeText('(a + b)').map(sym)).toEqual(['(', 'a', '+', 'b', ')']);
  });

  test('handles the arrow run "Nat → Nat" without a tag', () => {
    expect(tokenizeText('Nat → Nat').map(sym)).toEqual(['Nat', '\\to', 'Nat']);
  });

  test('empty / whitespace-only text yields no nodes', () => {
    expect(tokenizeText('')).toEqual([]);
    expect(tokenizeText('   ')).toEqual([]);
  });
});

describe('codeWithInfosToMathRow', () => {
  test('plain text → flat symbol row', () => {
    const row = codeWithInfosToMathRow({ t: 'text', s: 'x + 1' });
    expect(row.children.map(sym)).toEqual(['x', '+', '1']);
  });

  test('tag wraps its content in a Group keyed by subexpr pos', () => {
    const tagged: TaggedJson = { t: 'tag', pos: '/0', child: { t: 'text', s: 'Nat' } };
    const row = codeWithInfosToMathRow(tagged);
    expect(row.children).toHaveLength(1);
    const g = row.children[0] as GroupNode;
    expect(g.tag).toBe('Group');
    expect(g.htmlId).toBe(`${SUBEXPR_HTML_PREFIX}/0`);
    expect(g.children.map(sym)).toEqual(['Nat']);
  });

  test('append flattens children in order', () => {
    // Mirrors real `Nat → Nat` output: append[ tag(/0,"Nat"), text(" → "), tag(/1,"Nat") ]
    const tagged: TaggedJson = {
      t: 'append',
      kids: [
        { t: 'tag', pos: '/0', child: { t: 'text', s: 'Nat' } },
        { t: 'text', s: ' → ' },
        { t: 'tag', pos: '/1', child: { t: 'text', s: 'Nat' } },
      ],
    };
    const row = codeWithInfosToMathRow(tagged);
    expect(row.children).toHaveLength(3);
    expect((row.children[0] as GroupNode).tag).toBe('Group');
    expect(sym(row.children[1])).toBe('\\to');
    expect((row.children[2] as GroupNode).tag).toBe('Group');
    // group ids carry the subexpr positions
    expect((row.children[0] as GroupNode).htmlId).toBe(`${SUBEXPR_HTML_PREFIX}/0`);
    expect((row.children[2] as GroupNode).htmlId).toBe(`${SUBEXPR_HTML_PREFIX}/1`);
  });

  test('nested tags produce nested groups (subterm within subterm)', () => {
    // tag(/, append[ tag(/1, "a"), text(" + "), tag(/0, "b") ])  — like `a + b`
    const tagged: TaggedJson = {
      t: 'tag',
      pos: '/',
      child: {
        t: 'append',
        kids: [
          { t: 'tag', pos: '/1', child: { t: 'text', s: 'a' } },
          { t: 'text', s: ' + ' },
          { t: 'tag', pos: '/0', child: { t: 'text', s: 'b' } },
        ],
      },
    };
    const row = codeWithInfosToMathRow(tagged);
    expect(row.children).toHaveLength(1);
    const outer = row.children[0] as GroupNode;
    expect(outer.htmlId).toBe(`${SUBEXPR_HTML_PREFIX}/`);
    expect(outer.children).toHaveLength(3);
    expect((outer.children[0] as GroupNode).htmlId).toBe(`${SUBEXPR_HTML_PREFIX}/1`);
    expect(sym(outer.children[1])).toBe('+');
    expect((outer.children[2] as GroupNode).htmlId).toBe(`${SUBEXPR_HTML_PREFIX}/0`);
  });

  test('empty tag contributes nothing', () => {
    const tagged: TaggedJson = { t: 'tag', pos: '/0', child: { t: 'text', s: '' } };
    expect(codeWithInfosToMathRow(tagged).children).toEqual([]);
  });

  test('every node gets a unique id', () => {
    const row = codeWithInfosToMathRow({
      t: 'append',
      kids: [
        { t: 'text', s: 'a + b' },
        { t: 'tag', pos: '/0', child: { t: 'text', s: 'c' } },
      ],
    });
    const ids = new Set<number>();
    const walk = (nodes: readonly MathNode[]) => {
      for (const n of nodes) {
        expect(ids.has(n.id)).toBe(false);
        ids.add(n.id);
        if (n.tag === 'Group') walk(n.children);
      }
    };
    walk(row.children);
    expect(ids.size).toBeGreaterThan(0);
  });
});
