import { describe, expect, test } from 'vitest';
import { exprToLatex } from './expr-latex';

describe('exprToLatex', () => {
  // The three mangles from the Tactics tab, each pinned.
  test('snake_case projections keep their underscore — never a subscript', () => {
    // `eps_delta` rendered as "epsₐelta": KaTeX read the raw `_`.
    expect(exprToLatex('limF.eps_delta (ε / 2) h2')).toBe(
      '\\textsf{limF}.\\textsf{eps\\_delta}\\,(\\varepsilon/2)\\,h_{2}',
    );
  });

  test('application arguments get thin spaces, not concatenation', () => {
    // Rendered as one italic word "divTwoPosεepsPos".
    expect(exprToLatex('divTwoPos ε epsPos')).toBe(
      '\\textsf{divTwoPos}\\,\\varepsilon\\,\\textsf{epsPos}',
    );
  });

  test('trailing digits subscript: h1 → h₁, x0 → x₀', () => {
    expect(exprToLatex('fFn x h h1')).toBe('\\textsf{fFn}\\,x\\,h\\,h_{1}');
    expect(exprToLatex('x0')).toBe('x_{0}');
  });

  test('multichar names are upright, single chars stay math italic', () => {
    expect(exprToLatex('assumption')).toBe('\\textsf{assumption}');
    expect(exprToLatex('f')).toBe('f');
  });

  test('abs bars gap on the outside, stay tight inside', () => {
    expect(exprToLatex('ltLeTrans |x - x0| deltaF h1 a')).toBe(
      // `deltaF` renders as the δ_F the goal view shows — same name pipeline.
      '\\textsf{ltLeTrans}\\,|x-x_{0}|\\,\\delta_{F}\\,h_{1}\\,a',
    );
  });

  test('anonymous-constructor brackets', () => {
    expect(exprToLatex('⟨dfPos, fFn⟩')).toBe('⟨\\textsf{dfPos},\\textsf{fFn}⟩');
  });

  test('arrows and lambda', () => {
    expect(exprToLatex('fun x => f x + g x')).toBe(
      '\\textsf{fun}\\,x\\Rightarrow f\\,x+g\\,x',
    );
    expect(exprToLatex('Nat -> Nat')).toBe('\\mathbb{N}\\to \\mathbb{N}');
  });

  test('primes survive', () => {
    expect(exprToLatex("f' x")).toBe("f'\\,x");
  });

  test('metavariable names pass through legibly', () => {
    expect(exprToLatex('?eps_delta.mk.fst')).toBe(
      '?\\textsf{eps\\_delta}.\\textsf{mk}.\\textsf{fst}',
    );
  });

  test('empty and whitespace-only input', () => {
    expect(exprToLatex('')).toBe('');
    expect(exprToLatex('   ')).toBe('');
  });
});
