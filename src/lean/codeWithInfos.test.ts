import { describe, expect, test } from 'vitest';
import {
  codeWithInfosToMathRow,
  tokenizeText,
  SUBEXPR_HTML_PREFIX,
  type TaggedJson,
} from './codeWithInfos';
import type { GroupNode, MathNode, SymbolNode } from '../math-editor/types';
import { renderStaticLatex } from '../math-editor/render';

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

  test('limit notation lim⟦x0⟧ f = L renders as \\lim_{… → x0} … = L', () => {
    const variableF: TaggedJson = {
      t: 'append',
      kids: [
        { t: 'text', s: 'lim⟦' },
        { t: 'tag', pos: '/0', child: { t: 'text', s: 'x0' } },
        { t: 'text', s: '⟧ ' },
        { t: 'tag', pos: '/1', child: { t: 'text', s: 'f' } },
        { t: 'text', s: ' = ' },
        { t: 'tag', pos: '/2', child: { t: 'text', s: 'L' } },
      ],
    };
    const latex = renderStaticLatex(codeWithInfosToMathRow(variableF, { wrapSubterms: false }));
    expect(latex).toContain('\\lim');
    expect(latex).toContain('\\to'); // the x → x0 arrow
    expect(latex).not.toContain('lim⟦'); // marker consumed, not shown raw
  });

  test('limit with a lambda f shows the binder body, not "fun"', () => {
    const lambdaF: TaggedJson = {
      t: 'append',
      kids: [
        { t: 'text', s: 'lim⟦' },
        { t: 'tag', pos: '/0', child: { t: 'text', s: 'x0' } },
        { t: 'text', s: '⟧ ' },
        { t: 'tag', pos: '/1', child: { t: 'append', kids: [
          { t: 'text', s: 'fun ' },
          { t: 'tag', pos: '/1/0', child: { t: 'text', s: 'x' } },
          { t: 'text', s: ' => ' },
          { t: 'tag', pos: '/1/1', child: { t: 'text', s: 'k' } },
        ] } },
        { t: 'text', s: ' = ' },
        { t: 'tag', pos: '/2', child: { t: 'text', s: 'k' } },
      ],
    };
    const latex = renderStaticLatex(codeWithInfosToMathRow(lambdaF, { wrapSubterms: false }));
    expect(latex).toContain('\\lim');
    expect(latex).not.toContain('fun'); // lambda unfolded into bound var + body
  });
});

describe('structural restructuring', () => {
  // a / b  → append[ tag(a), " / ", tag(b) ]
  const div = (a: string, b: string): TaggedJson => ({
    t: 'append',
    kids: [
      { t: 'tag', pos: '/0', child: { t: 'text', s: a } },
      { t: 'text', s: ' / ' },
      { t: 'tag', pos: '/1', child: { t: 'text', s: b } },
    ],
  });

  test('a / b becomes a FracNode', () => {
    const row = codeWithInfosToMathRow(div('a', 'b'));
    expect(row.children).toHaveLength(1);
    const f = row.children[0] as any;
    expect(f.tag).toBe('Frac');
    // numer/denom are MathRows wrapping the (group-wrapped) operands
    expect(f.numer.children.length).toBeGreaterThan(0);
    expect(f.denom.children.length).toBeGreaterThan(0);
  });

  test('x ^ 2 becomes a SupNode', () => {
    const tagged: TaggedJson = {
      t: 'append',
      kids: [
        { t: 'tag', pos: '/0', child: { t: 'text', s: 'x' } },
        { t: 'text', s: ' ^ ' },
        { t: 'tag', pos: '/1', child: { t: 'text', s: '2' } },
      ],
    };
    const f = codeWithInfosToMathRow(tagged).children[0] as any;
    expect(f.tag).toBe('Sup');
  });

  test('∑ body becomes a BigOpNode (sum)', () => {
    const tagged: TaggedJson = { t: 'text', s: '∑ x' };
    const f = codeWithInfosToMathRow(tagged).children[0] as any;
    expect(f.tag).toBe('BigOp');
    expect(f.operator).toBe('sum');
  });

  test('dependent Pi binder (x : T) → body renders as ∀ x, body', () => {
    const tagged: TaggedJson = {
      t: 'append',
      kids: [
        { t: 'text', s: '(' },
        { t: 'tag', pos: '/n', child: { t: 'text', s: 'n' } },
        { t: 'text', s: ' : ' },
        { t: 'tag', pos: '/T', child: { t: 'text', s: 'MyNat' } },
        { t: 'text', s: ') → ' },
        { t: 'tag', pos: '/b', child: { t: 'text', s: 'P' } },
      ],
    };
    const syms = codeWithInfosToMathRow(tagged, { wrapSubterms: false }).children.map(
      (n) => (n.tag === 'Symbol' ? (n as SymbolNode).value : n.tag),
    );
    expect(syms[0]).toBe('\\forall');
    expect(syms).toContain(','); // ∀ n , …
    expect(syms).not.toContain(':'); // type dropped
  });

  test('non-dependent A → B stays an arrow (not ∀)', () => {
    const tagged: TaggedJson = {
      t: 'append',
      kids: [
        { t: 'tag', pos: '/0', child: { t: 'text', s: 'A' } },
        { t: 'text', s: ' → ' },
        { t: 'tag', pos: '/1', child: { t: 'text', s: 'B' } },
      ],
    };
    const syms = codeWithInfosToMathRow(tagged, { wrapSubterms: false }).children.map(
      (n) => (n.tag === 'Symbol' ? (n as SymbolNode).value : n.tag),
    );
    expect(syms).toContain('\\to');
    expect(syms).not.toContain('\\forall');
  });

  test('plain a + b is NOT restructured (stays flat symbols)', () => {
    const tagged: TaggedJson = {
      t: 'append',
      kids: [
        { t: 'tag', pos: '/0', child: { t: 'text', s: 'a' } },
        { t: 'text', s: ' + ' },
        { t: 'tag', pos: '/1', child: { t: 'text', s: 'b' } },
      ],
    };
    const kids = codeWithInfosToMathRow(tagged).children;
    expect(kids.map((n) => n.tag)).toEqual(['Group', 'Symbol', 'Group']);
  });
});
