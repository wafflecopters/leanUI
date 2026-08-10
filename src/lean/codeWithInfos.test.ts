import { describe, expect, test } from 'vitest';
import { mathTextToLatex,
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

  test('function application f x renders as f(x)', () => {
    const app: TaggedJson = {
      t: 'append',
      kids: [
        { t: 'tag', pos: '/0', child: { t: 'text', s: 'f' } },
        { t: 'text', s: ' ' },
        { t: 'tag', pos: '/1', child: { t: 'text', s: 'x' } },
      ],
    };
    const latex = renderStaticLatex(codeWithInfosToMathRow(app, { wrapSubterms: false }));
    expect(latex.replace(/\s/g, '')).toBe('f(x)');
  });

  test('multi-arg application g a b renders as g(a, b) (spine flattened)', () => {
    const app: TaggedJson = {
      t: 'append',
      kids: [
        { t: 'tag', pos: '/0', child: { t: 'text', s: 'g' } },
        { t: 'text', s: ' ' },
        { t: 'tag', pos: '/1', child: { t: 'text', s: 'a' } },
        { t: 'text', s: ' ' },
        { t: 'tag', pos: '/2', child: { t: 'text', s: 'b' } },
      ],
    };
    const latex = renderStaticLatex(codeWithInfosToMathRow(app, { wrapSubterms: false }));
    expect(latex.replace(/\s/g, '')).toBe('g(a,b)');
  });

  test('a + b stays infix (application rule does not fire across operators)', () => {
    const sum: TaggedJson = {
      t: 'append',
      kids: [
        { t: 'tag', pos: '/0', child: { t: 'text', s: 'a' } },
        { t: 'text', s: ' + ' },
        { t: 'tag', pos: '/1', child: { t: 'text', s: 'b' } },
      ],
    };
    const latex = renderStaticLatex(codeWithInfosToMathRow(sum, { wrapSubterms: false }));
    expect(latex.replace(/\s/g, '')).toBe('a+b');
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

  test('dependent Pi binder (x : T) → body renders as ∀ x ∈ T, body', () => {
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
    expect(syms).toContain('\\in'); // binder TYPE kept: ∀ n ∈ MyNat
    expect(syms).toContain('MyNat');
    expect(syms).toContain(','); // …, body
    expect(syms).not.toContain(':'); // the raw `:` is rewritten away
  });

  test('leading implicit binder {R : Real} → … is elided from display', () => {
    const tagged: TaggedJson = {
      t: 'append',
      kids: [
        { t: 'text', s: '{' },
        { t: 'tag', pos: '/R', child: { t: 'text', s: 'R' } },
        { t: 'text', s: ' : ' },
        { t: 'tag', pos: '/Real', child: { t: 'text', s: 'Real' } },
        { t: 'text', s: '} → ' },
        { t: 'tag', pos: '/b', child: { t: 'text', s: 'P' } },
      ],
    };
    const latex = renderStaticLatex(codeWithInfosToMathRow(tagged, { wrapSubterms: false }));
    expect(latex).not.toContain('Real');
    expect(latex).not.toContain('\\to');
    expect(latex.trim()).toBe('P');
  });

  test('a set-like brace without binder shape is NOT stripped', () => {
    // `{n}` alone (no `: T} →`) stays literal.
    const tagged: TaggedJson = { t: 'text', s: '{ n }' };
    const latex = renderStaticLatex(codeWithInfosToMathRow(tagged, { wrapSubterms: false }));
    expect(latex).toContain('n');
  });

  test('multi-var binder groups: one ∀, commas between vars, "and" between groups', () => {
    // (f g : T) → (x0 L M : S) → body   (inline form, no subterm wrappers)
    const tagged: TaggedJson = {
      t: 'append',
      kids: [
        { t: 'text', s: '(' },
        { t: 'tag', pos: '/f', child: { t: 'text', s: 'f ' } },
        { t: 'tag', pos: '/g', child: { t: 'text', s: 'g' } },
        { t: 'text', s: ' : ' },
        { t: 'tag', pos: '/T', child: { t: 'text', s: 'T' } },
        { t: 'text', s: ') → ' },
        {
          t: 'tag',
          pos: '/rest',
          child: {
            t: 'append',
            kids: [
              { t: 'text', s: '(' },
              { t: 'tag', pos: '/x0', child: { t: 'text', s: 'x0 ' } },
              { t: 'tag', pos: '/L', child: { t: 'text', s: 'L' } },
              { t: 'text', s: ' : ' },
              { t: 'tag', pos: '/S', child: { t: 'text', s: 'S' } },
              { t: 'text', s: ') → ' },
              { t: 'tag', pos: '/b', child: { t: 'text', s: 'P' } },
            ],
          },
        },
      ],
    };
    const latex = renderStaticLatex(codeWithInfosToMathRow(tagged, { wrapSubterms: false }));
    // ONE ∀ covering both groups, joined by "and".
    expect(latex.match(/\\forall/g)?.length).toBe(1);
    expect(latex).toContain('\\text{and}');
    expect(latex.match(/\\in/g)?.length).toBe(2);
  });

  test('prop implication chain renders hypotheses with "and" and final ⟹', () => {
    // (a = b) → (c = d) → e = f   — every segment prop-like.
    const tagged: TaggedJson = {
      t: 'append',
      kids: [
        { t: 'tag', pos: '/h1', child: { t: 'text', s: 'a = b' } },
        { t: 'text', s: ' → ' },
        {
          t: 'tag',
          pos: '/rest',
          child: {
            t: 'append',
            kids: [
              { t: 'tag', pos: '/h2', child: { t: 'text', s: 'c = d' } },
              { t: 'text', s: ' → ' },
              { t: 'tag', pos: '/c', child: { t: 'text', s: 'e = f' } },
            ],
          },
        },
      ],
    };
    const latex = renderStaticLatex(codeWithInfosToMathRow(tagged, { wrapSubterms: false }));
    expect(latex).toContain('\\text{and}');
    expect(latex).toContain(',\\;\\text{then}'); // consequent reads ", then"
    expect(latex).not.toContain('\\to');
  });

  test('function-type arrows are NOT rewritten to and/⟹', () => {
    // Carrier R → Carrier R: no relation symbols → keeps its arrow.
    const tagged: TaggedJson = {
      t: 'append',
      kids: [
        { t: 'tag', pos: '/0', child: { t: 'text', s: 'Carrier R' } },
        { t: 'text', s: ' → ' },
        { t: 'tag', pos: '/1', child: { t: 'text', s: 'Carrier R' } },
      ],
    };
    const latex = renderStaticLatex(codeWithInfosToMathRow(tagged, { wrapSubterms: false }));
    expect(latex).toContain('\\to');
    expect(latex).not.toContain('\\text{then}');
    expect(latex).not.toContain('\\text{and}');
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

describe('data-existential display', () => {
  test("∃' (the preset's DPair notation) renders as a plain ∃ quantifier", () => {
    const latex = renderStaticLatex(
      codeWithInfosToMathRow({ t: 'text', s: "∃' delta ∈ ℝ, P delta" }, { wrapSubterms: false }),
    );
    expect(latex).toContain('\\exists');
    expect(latex).not.toContain("'"); // prime stripped
    expect(latex).toContain('\\delta');
  });
});

describe('mathTextToLatex applications', () => {
  // One parenthesized argument used to break call-detection: everything after
  // it concatenated with NO separators ("…(ε/2)h₂", ")δ_Fδ_Gh₁a").
  test('multi-arg applications render call-style regardless of arg shape', () => {
    expect(mathTextToLatex('ltLeTrans |x - x0| deltaF deltaG h1 a')).toBe(
      '\\operatorname{ltLeTrans}(|x - {x}_{0}|, \\delta_{F} , \\delta_{G} , {h}_{1}, a)',
    );
    expect(mathTextToLatex('limF.eps_delta (ε / 2) h2')).toBe(
      '\\operatorname{limF.eps\\_delta}(\\frac{\\varepsilon }{2}, {h}_{2})',
    );
  });

  test('expressions with top-level operators keep the expression path', () => {
    expect(mathTextToLatex('0 < ε / 2')).toBe('0<\\frac{\\varepsilon }{2}');
  });
});

describe('projections and list append', () => {
  test('a postfix projection glues to its operand — never a call argument', () => {
    // These rendered as vs(.length) / (…)(.length): the application rule
    // treated the `.length` atom as an argument.
    expect(mathTextToLatex('(pre ++ post).length ≤ n')).toContain('.length');
    expect(mathTextToLatex('(pre ++ post).length ≤ n')).not.toContain('(.');
    expect(mathTextToLatex('List W.V')).toBe('\\operatorname{List}(W.V)');
  });

  test('++ is one operator, not two pluses and not an application', () => {
    expect(mathTextToLatex('pre ++ post')).toBe(
      '\\operatorname{pre}+\\!\\!+\\operatorname{post}',
    );
    expect(mathTextToLatex('ih (pre ++ post)')).toBe(
      '\\operatorname{ih}(\\operatorname{pre}+\\!\\!+\\operatorname{post})',
    );
  });
});

describe('forall binder telescopes', () => {
  test('implicit groups are elided; explicit groups get separators', () => {
    // Rendered as the mashed "K : Field'W : VectorSpace(K)(n : Nat)…" before:
    // the {} braces reached KaTeX as invisible grouping.
    expect(mathTextToLatex('∀ {K : Nat} {W : Nat} (n : Nat) (vs : Nat), vs ≤ n')).toBe(
      '\\forall n \\in \\operatorname{Nat}\\;\\text{and}\\;\\operatorname{vs} \\in \\operatorname{Nat},\\operatorname{vs} \\leq n',
    );
  });

  test('an all-implicit telescope drops the ∀ entirely', () => {
    expect(mathTextToLatex('∀ {K : Nat}, K = K')).toBe('K = K');
  });
});
