import { describe, test, expect, beforeEach } from 'vitest';
import { resetIds, mkRow, mkSymbol, mkHole, mkDelimiter, mkFrac, mkSub, mkSup, mkBigOp, mkAccent } from './types';
import {
  matchRow, convertToSource, substituteTemplate, patternToDisplayLatex,
  pat, createDefaultRegistry, lookupSymbol,
  SyntaxRegistry, SyntaxEntry, PatternElement,
  parsePatternString, parseSyntaxAnnotation, buildRegistryFromAnnotations,
} from './syntax-registry';

beforeEach(() => resetIds());

// ============================================================================
// Pattern matching — basics
// ============================================================================

describe('matchRow', () => {
  test('empty pattern matches empty nodes', () => {
    expect(matchRow([], [])).toEqual(new Map());
  });

  test('empty pattern fails on non-empty nodes', () => {
    expect(matchRow([], [mkSymbol('x')])).toBe(null);
  });

  test('literal matches exact symbol', () => {
    const result = matchRow([pat.literal('+')], [mkSymbol('+')]);
    expect(result).toEqual(new Map());
  });

  test('literal fails on wrong symbol', () => {
    expect(matchRow([pat.literal('+')], [mkSymbol('-')])).toBe(null);
  });

  test('literal fails on non-symbol node', () => {
    expect(matchRow([pat.literal('+')], [mkHole()])).toBe(null);
  });

  test('capture grabs all remaining when no anchor', () => {
    const nodes = [mkSymbol('x'), mkSymbol('+'), mkSymbol('y')];
    const result = matchRow([pat.capture('a')], nodes);
    expect(result).not.toBe(null);
    expect(result!.get('a')).toHaveLength(3);
    expect(result!.get('a')![0]).toMatchObject({ tag: 'Symbol', value: 'x' });
  });

  test('capture with literal anchor splits correctly', () => {
    const nodes = [mkSymbol('x'), mkSymbol('+'), mkSymbol('y')];
    const result = matchRow(
      [pat.capture('a'), pat.literal('+'), pat.capture('b')],
      nodes
    );
    expect(result).not.toBe(null);
    expect(result!.get('a')).toHaveLength(1);
    expect(result!.get('a')![0]).toMatchObject({ tag: 'Symbol', value: 'x' });
    expect(result!.get('b')).toHaveLength(1);
    expect(result!.get('b')![0]).toMatchObject({ tag: 'Symbol', value: 'y' });
  });

  test('capture finds first anchor occurrence (leftmost match)', () => {
    // a + b + c  matched against $x + $y
    const nodes = [mkSymbol('a'), mkSymbol('+'), mkSymbol('b'), mkSymbol('+'), mkSymbol('c')];
    const result = matchRow(
      [pat.capture('x'), pat.literal('+'), pat.capture('y')],
      nodes
    );
    expect(result).not.toBe(null);
    // x captures [a], y captures [b, +, c]
    expect(result!.get('x')).toHaveLength(1);
    expect(result!.get('y')).toHaveLength(3);
  });

  test('capture can be empty (zero nodes)', () => {
    // pattern: literal(+) capture(a) — if + is at end
    const nodes = [mkSymbol('+')];
    const result = matchRow([pat.literal('+'), pat.capture('a')], nodes);
    expect(result).not.toBe(null);
    expect(result!.get('a')).toHaveLength(0);
  });

  test('literal after capture fails when anchor not found', () => {
    const nodes = [mkSymbol('x'), mkSymbol('y')];
    expect(matchRow(
      [pat.capture('a'), pat.literal('+'), pat.capture('b')],
      nodes
    )).toBe(null);
  });

  test('leftover input after pattern fails', () => {
    const nodes = [mkSymbol('x'), mkSymbol('y')];
    expect(matchRow([pat.literal('x')], nodes)).toBe(null);
  });
});

// ============================================================================
// Pattern matching — structural nodes
// ============================================================================

describe('matchRow structural', () => {
  test('bigop matches operator and below slot', () => {
    const lim = mkBigOp('lim', mkRow([mkSymbol('x'), mkSymbol('\\to'), mkSymbol('a')]), null);
    const result = matchRow(
      [pat.bigop('lim', [pat.capture('var'), pat.literal('\\to'), pat.capture('pt')])],
      [lim]
    );
    expect(result).not.toBe(null);
    expect(result!.get('var')).toHaveLength(1);
    expect(result!.get('var')![0]).toMatchObject({ tag: 'Symbol', value: 'x' });
    expect(result!.get('pt')).toHaveLength(1);
    expect(result!.get('pt')![0]).toMatchObject({ tag: 'Symbol', value: 'a' });
  });

  test('bigop fails on wrong operator', () => {
    const sum = mkBigOp('sum', mkRow([mkHole()]), null);
    expect(matchRow([pat.bigop('lim', [pat.capture('x')])], [sum])).toBe(null);
  });

  test('bigop with above slot', () => {
    const sum = mkBigOp('sum', mkRow([mkSymbol('i'), mkSymbol('='), mkSymbol('0')]),
                                mkRow([mkSymbol('n')]));
    const result = matchRow(
      [pat.bigop('sum',
        [pat.capture('i'), pat.literal('='), pat.capture('low')],
        [pat.capture('high')]
      )],
      [sum]
    );
    expect(result).not.toBe(null);
    expect(result!.get('i')![0]).toMatchObject({ value: 'i' });
    expect(result!.get('low')![0]).toMatchObject({ value: '0' });
    expect(result!.get('high')![0]).toMatchObject({ value: 'n' });
  });

  test('frac matches numer and denom', () => {
    const frac = mkFrac(mkRow([mkSymbol('a')]), mkRow([mkSymbol('b')]));
    const result = matchRow(
      [pat.frac([pat.capture('n')], [pat.capture('d')])],
      [frac]
    );
    expect(result).not.toBe(null);
    expect(result!.get('n')![0]).toMatchObject({ value: 'a' });
    expect(result!.get('d')![0]).toMatchObject({ value: 'b' });
  });

  test('delimiter matches open/close and inner', () => {
    const delim = mkDelimiter('|', '|', mkRow([mkSymbol('x')]));
    const result = matchRow(
      [pat.delimiter('|', '|', [pat.capture('a')])],
      [delim]
    );
    expect(result).not.toBe(null);
    expect(result!.get('a')![0]).toMatchObject({ value: 'x' });
  });

  test('delimiter fails on wrong open/close', () => {
    const delim = mkDelimiter('(', ')', mkRow([mkSymbol('x')]));
    expect(matchRow([pat.delimiter('|', '|', [pat.capture('a')])], [delim])).toBe(null);
  });

  test('accent matches type and body', () => {
    const acc = mkAccent('overline', mkRow([mkSymbol('A')]));
    const result = matchRow(
      [pat.accent('overline', [pat.capture('A')])],
      [acc]
    );
    expect(result).not.toBe(null);
    expect(result!.get('A')![0]).toMatchObject({ value: 'A' });
  });

  test('sub matches base and subscript', () => {
    const sub = mkSub(mkRow([mkSymbol('x')]), mkRow([mkSymbol('0')]));
    const result = matchRow(
      [pat.sub([pat.capture('base')], [pat.capture('idx')])],
      [sub]
    );
    expect(result).not.toBe(null);
    expect(result!.get('base')![0]).toMatchObject({ value: 'x' });
    expect(result!.get('idx')![0]).toMatchObject({ value: '0' });
  });

  test('sup matches base and superscript', () => {
    const sup = mkSup(mkRow([mkSymbol('x')]), mkRow([mkSymbol('2')]));
    const result = matchRow(
      [pat.sup([pat.capture('base')], [pat.capture('exp')])],
      [sup]
    );
    expect(result).not.toBe(null);
    expect(result!.get('base')![0]).toMatchObject({ value: 'x' });
    expect(result!.get('exp')![0]).toMatchObject({ value: '2' });
  });

  test('bigop + trailing capture: lim with body', () => {
    const lim = mkBigOp('lim', mkRow([mkSymbol('x'), mkSymbol('\\to'), mkSymbol('a')]), null);
    const nodes = [lim, mkSymbol('f'), mkDelimiter('(', ')', mkRow([mkSymbol('x')]))];
    const result = matchRow(
      [
        pat.bigop('lim', [pat.capture('var'), pat.literal('\\to'), pat.capture('pt')]),
        pat.capture('body'),
      ],
      nodes
    );
    expect(result).not.toBe(null);
    expect(result!.get('var')![0]).toMatchObject({ value: 'x' });
    expect(result!.get('pt')![0]).toMatchObject({ value: 'a' });
    expect(result!.get('body')).toHaveLength(2); // f and (x)
  });

  test('bigop + body + literal + capture: lim with equality', () => {
    const lim = mkBigOp('lim', mkRow([mkSymbol('x'), mkSymbol('\\to'), mkSymbol('a')]), null);
    const nodes = [lim, mkSymbol('f'), mkSymbol('='), mkSymbol('L')];
    const result = matchRow(
      [
        pat.bigop('lim', [pat.capture('x'), pat.literal('\\to'), pat.capture('a')]),
        pat.capture('body'),
        pat.literal('='),
        pat.capture('L'),
      ],
      nodes
    );
    expect(result).not.toBe(null);
    expect(result!.get('body')).toHaveLength(1); // [f]
    expect(result!.get('body')![0]).toMatchObject({ value: 'f' });
    expect(result!.get('L')![0]).toMatchObject({ value: 'L' });
  });
});

// ============================================================================
// Template substitution
// ============================================================================

describe('substituteTemplate', () => {
  test('simple substitution', () => {
    const bindings = new Map([['a', 'x'], ['b', 'y']]);
    expect(substituteTemplate('Equal $a $b', bindings)).toBe('Equal x y');
  });

  test('$$name auto-parenthesizes multi-word values', () => {
    const bindings = new Map([['a', 'f x'], ['b', 'g y']]);
    expect(substituteTemplate('radd $$a $$b', bindings)).toBe('radd (f x) (g y)');
  });

  test('$name does NOT auto-parenthesize', () => {
    const bindings = new Map([['a', 'f x'], ['b', 'g y']]);
    expect(substituteTemplate('$a -> $b', bindings)).toBe('f x -> g y');
  });

  test('$$name does not double-parenthesize', () => {
    const bindings = new Map([['a', '(f x)']]);
    expect(substituteTemplate('foo $$a', bindings)).toBe('foo (f x)');
  });

  test('lambda binders: \\$x substitutes plain, $body stays plain', () => {
    const bindings = new Map([['x', 'n'], ['body', 'f n']]);
    expect(substituteTemplate('Limit (\\$x => $body) $$a', new Map([...bindings, ['a', 'a']]))).toBe('Limit (\\n => f n) a');
  });

  test('unbound variables left as-is', () => {
    const bindings = new Map<string, string>();
    expect(substituteTemplate('foo $unbound', bindings)).toBe('foo $unbound');
  });
});

// ============================================================================
// Source conversion
// ============================================================================

describe('convertToSource', () => {
  const registry = createDefaultRegistry();

  test('single symbol via symbolMap', () => {
    const nodes = [mkSymbol('\\mathbb{R}')];
    const result = convertToSource(registry, nodes);
    expect(result.source).toBe('Carrier R');
    expect(result.needsR).toBe(true);
  });

  test('Nat symbol does not need R', () => {
    const nodes = [mkSymbol('\\mathbb{N}')];
    const result = convertToSource(registry, nodes);
    expect(result.source).toBe('Nat');
    expect(result.needsR).toBe(false);
  });

  test('unknown symbol passed through', () => {
    const nodes = [mkSymbol('z')];
    const result = convertToSource(registry, nodes);
    expect(result.source).toBe('z');
    expect(result.needsR).toBe(false);
  });

  test('infix +: a + b → radd a b', () => {
    const nodes = [mkSymbol('a'), mkSymbol('+'), mkSymbol('b')];
    const result = convertToSource(registry, nodes);
    expect(result.source).toBe('radd a b');
    expect(result.needsR).toBe(true);
  });

  test('infix =: a = b → Equal a b', () => {
    const nodes = [mkSymbol('a'), mkSymbol('='), mkSymbol('b')];
    const result = convertToSource(registry, nodes);
    expect(result.source).toBe('Equal a b');
    expect(result.needsR).toBe(false);
  });

  test('infix \\leq: a ≤ b → rle a b', () => {
    const nodes = [mkSymbol('a'), mkSymbol('\\leq'), mkSymbol('b')];
    const result = convertToSource(registry, nodes);
    expect(result.source).toBe('rle a b');
    expect(result.needsR).toBe(true);
  });

  test('arrow: ℝ → ℝ → Carrier R -> Carrier R', () => {
    const nodes = [mkSymbol('\\mathbb{R}'), mkSymbol('\\to'), mkSymbol('\\mathbb{R}')];
    const result = convertToSource(registry, nodes);
    expect(result.source).toBe('Carrier R -> Carrier R');
    expect(result.needsR).toBe(true);
  });

  test('fraction: a/b → rdiv a b', () => {
    const frac = mkFrac(mkRow([mkSymbol('a')]), mkRow([mkSymbol('b')]));
    const result = convertToSource(registry, [frac]);
    expect(result.source).toBe('rdiv a b');
    expect(result.needsR).toBe(true);
  });

  test('fraction: 1/b → rinv b', () => {
    const frac = mkFrac(mkRow([mkSymbol('1')]), mkRow([mkSymbol('b')]));
    const result = convertToSource(registry, [frac]);
    expect(result.source).toBe('rinv b');
    expect(result.needsR).toBe(true);
  });

  test('absolute value: |x| → rabs x', () => {
    const delim = mkDelimiter('|', '|', mkRow([mkSymbol('x')]));
    const result = convertToSource(registry, [delim]);
    expect(result.source).toBe('rabs x');
    expect(result.needsR).toBe(true);
  });

  test('parenthesized expression', () => {
    const delim = mkDelimiter('(', ')', mkRow([mkSymbol('a'), mkSymbol('+'), mkSymbol('b')]));
    const result = convertToSource(registry, [delim]);
    expect(result.source).toBe('(radd a b)');
    expect(result.needsR).toBe(true);
  });

  test('closure: overline{A} → closure A', () => {
    const acc = mkAccent('overline', mkRow([mkSymbol('A')]));
    const result = convertToSource(registry, [acc]);
    expect(result.source).toBe('closure A');
  });

  test('hole → ?', () => {
    expect(convertToSource(registry, [mkHole()]).source).toBe('?');
  });

  test('empty nodes → ?', () => {
    expect(convertToSource(registry, []).source).toBe('?');
  });

  test('subscript name: x₀ → x0', () => {
    const sub = mkSub(mkRow([mkSymbol('x')]), mkRow([mkSymbol('0')]));
    const result = convertToSource(registry, [sub]);
    expect(result.source).toBe('x0');
  });
});

// ============================================================================
// Source conversion — recursive / composed patterns
// ============================================================================

describe('convertToSource recursive', () => {
  const registry = createDefaultRegistry();

  test('f(x) + g(y) → radd (f (x)) (g (y))', () => {
    const nodes = [
      mkSymbol('f'),
      mkDelimiter('(', ')', mkRow([mkSymbol('x')])),
      mkSymbol('+'),
      mkSymbol('g'),
      mkDelimiter('(', ')', mkRow([mkSymbol('y')])),
    ];
    const result = convertToSource(registry, nodes);
    expect(result.source).toBe('radd (f (x)) (g (y))');
  });

  test('a + b = c + d → Equal (radd a b) (radd c d)', () => {
    const nodes = [
      mkSymbol('a'), mkSymbol('+'), mkSymbol('b'),
      mkSymbol('='),
      mkSymbol('c'), mkSymbol('+'), mkSymbol('d'),
    ];
    const result = convertToSource(registry, nodes);
    // = is priority 5, + is priority 10
    // The = pattern matches first at the row level
    // $a captures [a, +, b], $b captures [c, +, d]
    // Each side recursively matches the + pattern
    expect(result.source).toBe('Equal (radd a b) (radd c d)');
  });

  test('lim_{x → a} f(x) → Limit (\\x => f (x)) a', () => {
    const lim = mkBigOp('lim', mkRow([mkSymbol('x'), mkSymbol('\\to'), mkSymbol('a')]), null,
      mkRow([mkSymbol('f'), mkDelimiter('(', ')', mkRow([mkSymbol('x')]))]));
    const nodes = [lim];
    const result = convertToSource(registry, nodes);
    expect(result.source).toBe('Limit (\\x => f (x)) a');
    expect(result.needsR).toBe(true);
  });

  test('lim_{x → a} f(x) = L → Limit (\\x => f (x)) a L', () => {
    const lim = mkBigOp('lim', mkRow([mkSymbol('x'), mkSymbol('\\to'), mkSymbol('a')]), null,
      mkRow([mkSymbol('f'), mkDelimiter('(', ')', mkRow([mkSymbol('x')]))]));
    const nodes = [lim, mkSymbol('='), mkSymbol('L')];
    const result = convertToSource(registry, nodes);
    expect(result.source).toBe('Limit (\\x => f (x)) a L');
    expect(result.needsR).toBe(true);
  });

  test('lim_{x → a} f(x) + g(x) = L → nested lim with + body', () => {
    const lim = mkBigOp('lim', mkRow([mkSymbol('x'), mkSymbol('\\to'), mkSymbol('a')]), null,
      mkRow([
        mkSymbol('f'), mkDelimiter('(', ')', mkRow([mkSymbol('x')])),
        mkSymbol('+'),
        mkSymbol('g'), mkDelimiter('(', ')', mkRow([mkSymbol('x')])),
      ]));
    const nodes = [
      lim,
      mkSymbol('='),
      mkSymbol('L'),
    ];
    const result = convertToSource(registry, nodes);
    // limit-equals pattern matches: body = [f, (x), +, g, (x)], L = [L]
    // body recursively matches +: radd (f (x)) (g (x))
    expect(result.source).toBe('Limit (\\x => radd (f (x)) (g (x))) a L');
  });

  test('(ℝ → ℝ) → ℝ → parenthesized arrow chain', () => {
    const inner = mkDelimiter('(', ')',
      mkRow([mkSymbol('\\mathbb{R}'), mkSymbol('\\to'), mkSymbol('\\mathbb{R}')])
    );
    const nodes = [inner, mkSymbol('\\to'), mkSymbol('\\mathbb{R}')];
    const result = convertToSource(registry, nodes);
    expect(result.source).toBe('(Carrier R -> Carrier R) -> Carrier R');
  });

  test('|a + b| → rabs (radd a b)', () => {
    const delim = mkDelimiter('|', '|',
      mkRow([mkSymbol('a'), mkSymbol('+'), mkSymbol('b')])
    );
    const result = convertToSource(registry, [delim]);
    expect(result.source).toBe('rabs (radd a b)');
  });
});

// ============================================================================
// Priority ordering
// ============================================================================

describe('priority ordering', () => {
  test('limit-equals (50) beats equality (5)', () => {
    const registry = createDefaultRegistry();
    const lim = mkBigOp('lim', mkRow([mkSymbol('x'), mkSymbol('\\to'), mkSymbol('a')]), null,
      mkRow([mkSymbol('f')]));
    const nodes = [lim, mkSymbol('='), mkSymbol('L')];
    const result = convertToSource(registry, nodes);
    // Should use limit-equals, not plain equality
    expect(result.source).toBe('Limit (\\x => f) a L');
    expect(result.source).not.toContain('Equal');
  });

  test('child registry shadows parent at same precedence', () => {
    const custom: SyntaxRegistry = {
      entries: [{
        name: 'custom-plus',
        pattern: [pat.capture('a'), pat.literal('+'), pat.capture('b')],
        template: 'myAdd $$a $$b',
        priority: 10, // same precedence as default — shadows via child-first ordering
      }],
      symbolMap: new Map(),
      parent: createDefaultRegistry(),
    };
    const nodes = [mkSymbol('x'), mkSymbol('+'), mkSymbol('y')];
    const result = convertToSource(custom, nodes);
    expect(result.source).toBe('myAdd x y');
  });

  test('child registry symbolMap shadows parent', () => {
    const child: SyntaxRegistry = {
      entries: [],
      symbolMap: new Map([['\\mathbb{R}', { source: 'MyReal', needsR: false }]]),
      parent: createDefaultRegistry(),
    };
    const result = convertToSource(child, [mkSymbol('\\mathbb{R}')]);
    expect(result.source).toBe('MyReal');
    expect(result.needsR).toBe(false);
  });
});

// ============================================================================
// needsR tracking
// ============================================================================

describe('needsR tracking', () => {
  const registry = createDefaultRegistry();

  test('pure Nat expression: no R needed', () => {
    const nodes = [mkSymbol('n'), mkSymbol('='), mkSymbol('\\mathbb{N}')];
    const result = convertToSource(registry, nodes);
    expect(result.needsR).toBe(false);
  });

  test('expression with ℝ symbol: needs R', () => {
    const nodes = [mkSymbol('\\mathbb{R}')];
    expect(convertToSource(registry, nodes).needsR).toBe(true);
  });

  test('expression with + operator: needs R from pattern', () => {
    const nodes = [mkSymbol('a'), mkSymbol('+'), mkSymbol('b')];
    expect(convertToSource(registry, nodes).needsR).toBe(true);
  });

  test('nested: ℝ inside delimiter propagates needsR', () => {
    const delim = mkDelimiter('(', ')', mkRow([mkSymbol('\\mathbb{R}')]));
    expect(convertToSource(registry, [delim]).needsR).toBe(true);
  });
});

// ============================================================================
// Pattern display (LaTeX)
// ============================================================================

describe('patternToDisplayLatex', () => {
  test('infix pattern: $a + $b', () => {
    const pattern = [pat.capture('a'), pat.literal('+'), pat.capture('b')];
    const latex = patternToDisplayLatex(pattern);
    expect(latex).toContain('\\textcolor{#58a6ff}{a}');
    expect(latex).toContain('+');
    expect(latex).toContain('\\textcolor{#58a6ff}{b}');
  });

  test('bigop pattern: lim_{x → a}', () => {
    const pattern = [
      pat.bigop('lim', [pat.capture('x'), pat.literal('\\to'), pat.capture('a')]),
    ];
    const latex = patternToDisplayLatex(pattern);
    expect(latex).toContain('\\lim');
    expect(latex).toContain('\\to');
  });

  test('frac pattern', () => {
    const pattern = [pat.frac([pat.capture('a')], [pat.capture('b')])];
    const latex = patternToDisplayLatex(pattern);
    expect(latex).toContain('\\frac');
  });

  test('delimiter pattern: |a|', () => {
    const pattern = [pat.delimiter('|', '|', [pat.capture('a')])];
    const latex = patternToDisplayLatex(pattern);
    expect(latex).toContain('\\left|');
    expect(latex).toContain('\\right|');
  });

  test('accent pattern: overline{A}', () => {
    const pattern = [pat.accent('overline', [pat.capture('A')])];
    const latex = patternToDisplayLatex(pattern);
    expect(latex).toContain('\\overline');
  });
});

// ============================================================================
// Default registry completeness
// ============================================================================

describe('default registry entries', () => {
  const registry = createDefaultRegistry();

  test('has symbol mappings for ℝ, ℕ, ℤ', () => {
    expect(registry.symbolMap.get('\\mathbb{R}')).toEqual({ source: 'Carrier R', needsR: true });
    expect(registry.symbolMap.get('\\mathbb{N}')).toEqual({ source: 'Nat', needsR: false });
    expect(registry.symbolMap.get('\\mathbb{Z}')).toEqual({ source: 'Int', needsR: false });
  });

  test('has entries for all planned operations', () => {
    const names = registry.entries.map(e => e.name);
    expect(names).toContain('addition');
    expect(names).toContain('subtraction');
    expect(names).toContain('multiplication');
    expect(names).toContain('equality');
    expect(names).toContain('less-equal');
    expect(names).toContain('less-than');
    expect(names).toContain('arrow');
    expect(names).toContain('limit');
    expect(names).toContain('limit-equals');
    expect(names).toContain('fraction');
    expect(names).toContain('absolute-value');
  });

  test('limit-equals has higher priority than equality', () => {
    const limEq = registry.entries.find(e => e.name === 'limit-equals')!;
    const eq = registry.entries.find(e => e.name === 'equality')!;
    expect(limEq.priority).toBeGreaterThan(eq.priority);
  });
});

// ============================================================================
// @syntax pattern string parser
// ============================================================================

describe('parsePatternString', () => {
  test('single LaTeX command: \\N → \\mathbb{N}', () => {
    const result = parsePatternString('\\N');
    expect(result).toEqual([pat.literal('\\mathbb{N}')]);
  });

  test('single LaTeX command: \\R → \\mathbb{R}', () => {
    const result = parsePatternString('\\R');
    expect(result).toEqual([pat.literal('\\mathbb{R}')]);
  });

  test('single literal: 0', () => {
    const result = parsePatternString('0');
    expect(result).toEqual([pat.literal('0')]);
  });

  test('single literal: 1', () => {
    const result = parsePatternString('1');
    expect(result).toEqual([pat.literal('1')]);
  });

  test('infix: $0 + $1', () => {
    const result = parsePatternString('$0 + $1');
    expect(result).toEqual([
      pat.capture('0'),
      pat.literal('+'),
      pat.capture('1'),
    ]);
  });

  test('infix: $0 \\cdot $1', () => {
    const result = parsePatternString('$0 \\cdot $1');
    expect(result).toEqual([
      pat.capture('0'),
      pat.literal('\\cdot'),
      pat.capture('1'),
    ]);
  });

  test('prime postfix: $0\\prime → Sup', () => {
    const result = parsePatternString('$0\\prime');
    expect(result).toEqual([
      pat.sup([pat.capture('0')], [pat.literal('\\prime')]),
    ]);
  });

  test('subscript: =_{$A}', () => {
    const result = parsePatternString('$0 =_{$A} $1');
    expect(result).toEqual([
      pat.capture('0'),
      pat.sub([pat.literal('=')], [pat.capture('A')]),
      pat.capture('1'),
    ]);
  });

  test('BigOp: \\sum_{= $0}^{$1} $2', () => {
    const result = parsePatternString('\\sum_{= $0}^{$1} $2');
    expect(result).toEqual([
      pat.bigop('sum', [pat.literal('='), pat.capture('0')], [pat.capture('1')], [pat.capture('2')]),
    ]);
  });

  test('BigOp without braces on superscript: \\sum_{= $0}^$1 $2', () => {
    const result = parsePatternString('\\sum_{= $0}^$1 $2');
    expect(result).toEqual([
      pat.bigop('sum', [pat.literal('='), pat.capture('0')], [pat.capture('1')], [pat.capture('2')]),
    ]);
  });

  test('\\mathbb{N} is passed through', () => {
    const result = parsePatternString('\\mathbb{N}');
    expect(result).toEqual([pat.literal('\\mathbb{N}')]);
  });

  test('superscript: $0^{$1}', () => {
    const result = parsePatternString('$0^{$1}');
    expect(result).toEqual([
      pat.sup([pat.capture('0')], [pat.capture('1')]),
    ]);
  });

  test('lim with arrow: \\lim_{$x \\to $a} $body', () => {
    const result = parsePatternString('\\lim_{$x \\to $a} $body');
    expect(result).toEqual([
      pat.bigop('lim', [pat.capture('x'), pat.literal('\\to'), pat.capture('a')], null, [pat.capture('body')]),
    ]);
  });
});

// ============================================================================
// @syntax annotation → SyntaxEntry / symbol mapping
// ============================================================================

describe('parseSyntaxAnnotation', () => {
  test('symbol mapping: \\N → Nat', () => {
    const result = parseSyntaxAnnotation('\\N', 'Nat');
    expect(result.symbolMapping).toEqual({ symbol: '\\mathbb{N}', source: 'Nat' });
    expect(result.entry).toBeUndefined();
  });

  test('symbol mapping: 0 → Zero', () => {
    const result = parseSyntaxAnnotation('0', 'Zero');
    expect(result.symbolMapping).toEqual({ symbol: '0', source: 'Zero' });
    expect(result.entry).toBeUndefined();
  });

  test('symbol mapping: 1 → one', () => {
    const result = parseSyntaxAnnotation('1', 'one');
    expect(result.symbolMapping).toEqual({ symbol: '1', source: 'one' });
    expect(result.entry).toBeUndefined();
  });

  test('infix pattern: $0 + $1 → plus', () => {
    const result = parseSyntaxAnnotation('$0 + $1', 'plus');
    expect(result.symbolMapping).toBeUndefined();
    expect(result.entry).toBeDefined();
    expect(result.entry!.name).toBe('plus');
    expect(result.entry!.template).toBe('plus $$0 $$1');
    expect(result.entry!.pattern).toEqual([
      pat.capture('0'), pat.literal('+'), pat.capture('1'),
    ]);
  });

  test('infix pattern: $0 \\cdot $1 → mul', () => {
    const result = parseSyntaxAnnotation('$0 \\cdot $1', 'mul');
    expect(result.entry!.name).toBe('mul');
    expect(result.entry!.template).toBe('mul $$0 $$1');
  });

  test('sup pattern: $0\\prime → Succ', () => {
    const result = parseSyntaxAnnotation('$0\\prime', 'Succ');
    expect(result.entry!.name).toBe('Succ');
    expect(result.entry!.template).toBe('Succ $$0');
    expect(result.entry!.priority).toBe(50); // structural (first elem is sup, not capture)
  });

  test('infix with implicit: $0 =_{$A} $1 → Equal', () => {
    const result = parseSyntaxAnnotation('$0 =_{$A} $1', 'Equal');
    expect(result.entry!.name).toBe('Equal');
    // Named capture A → implicit, explicit 0 and 1 → explicit args
    expect(result.entry!.template).toBe('Equal {$$A} $$0 $$1');
  });

  test('BigOp: \\sum_{= $0}^$1 $2 → sumFromIndexWithCount', () => {
    const result = parseSyntaxAnnotation('\\sum_{= $0}^$1 $2', 'sumFromIndexWithCount');
    expect(result.entry!.name).toBe('sumFromIndexWithCount');
    expect(result.entry!.template).toBe('sumFromIndexWithCount $$0 $$1 $$2');
    expect(result.entry!.priority).toBe(50); // structural (first elem is bigop)
  });

  test('= and \\to operators get low priority (bind wider)', () => {
    const eqResult = parseSyntaxAnnotation('$0 = $1', 'Equal');
    expect(eqResult.entry!.priority).toBe(5); // wide binding

    const arrowResult = parseSyntaxAnnotation('$0 \\to $1', 'arrow');
    expect(arrowResult.entry!.priority).toBe(5); // wide binding

    const plusResult = parseSyntaxAnnotation('$0 + $1', 'plus');
    expect(plusResult.entry!.priority).toBe(10); // normal binding
  });

  test('@becomes overrides auto-generated template', () => {
    const result = parseSyntaxAnnotation(
      '\\sum_{$0 = $1}^{$2} $3 @becomes summation $1 $2 (\\$0 => $3)',
      'summation'
    );
    expect(result.entry).toBeDefined();
    expect(result.entry!.template).toBe('summation $1 $2 (\\$0 => $3)');
  });

  test('@becomes absent uses auto-generated template', () => {
    const result = parseSyntaxAnnotation('$0 + $1', 'plus');
    expect(result.entry!.template).toBe('plus $$0 $$1');
  });

  test('@becomes pattern still parses correctly', () => {
    const result = parseSyntaxAnnotation(
      '\\sum_{$0 = $1}^{$2} $3 @becomes summation $1 $2 (\\$0 => $3)',
      'summation'
    );
    // Pattern should only contain the part before @becomes
    // BigOp now includes body inside the pattern element
    expect(result.entry!.pattern[0]).toEqual(
      pat.bigop('sum', [pat.capture('0'), pat.literal('='), pat.capture('1')], [pat.capture('2')], [pat.capture('3')])
    );
    expect(result.entry!.pattern).toHaveLength(1);
  });
});

// ============================================================================
// Registry builder from @syntax annotations
// ============================================================================

describe('buildRegistryFromAnnotations', () => {
  test('builds symbol mappings', () => {
    const registry = buildRegistryFromAnnotations([
      { declName: 'Nat', pattern: '\\N' },
      { declName: 'Zero', pattern: '0' },
      { declName: 'one', pattern: '1' },
    ]);

    expect(registry.symbolMap.get('\\mathbb{N}')).toEqual({ source: 'Nat', needsR: false });
    expect(registry.symbolMap.get('0')).toEqual({ source: 'Zero', needsR: false });
    expect(registry.symbolMap.get('1')).toEqual({ source: 'one', needsR: false });
    expect(registry.entries).toHaveLength(0);
  });

  test('builds pattern entries', () => {
    const registry = buildRegistryFromAnnotations([
      { declName: 'plus', pattern: '$0 + $1' },
      { declName: 'mul', pattern: '$0 \\cdot $1' },
    ]);

    expect(registry.entries).toHaveLength(2);
    expect(registry.entries[0].name).toBe('plus');
    expect(registry.entries[1].name).toBe('mul');
  });

  test('infix priorities increment: earlier binds wider', () => {
    const registry = buildRegistryFromAnnotations([
      { declName: 'Equal', pattern: '$0 = $1' },
      { declName: 'plus', pattern: '$0 + $1' },
      { declName: 'mul', pattern: '$0 \\cdot $1' },
    ]);

    const eq = registry.entries.find(e => e.name === 'Equal')!;
    const plus = registry.entries.find(e => e.name === 'plus')!;
    const mul = registry.entries.find(e => e.name === 'mul')!;

    // Earlier = lower priority = tried first in ascending sort = binds wider
    expect(eq.priority).toBeLessThan(plus.priority);
    expect(plus.priority).toBeLessThan(mul.priority);
  });

  test('mixed symbol mappings and entries', () => {
    const registry = buildRegistryFromAnnotations([
      { declName: 'Nat', pattern: '\\N' },
      { declName: 'Zero', pattern: '0' },
      { declName: 'Succ', pattern: '$0\\prime' },
      { declName: 'Equal', pattern: '$0 = $1' },
      { declName: 'plus', pattern: '$0 + $1' },
    ]);

    expect(registry.symbolMap.size).toBe(2);
    expect(registry.entries).toHaveLength(3); // Succ, Equal, plus
  });

  test('end-to-end: built registry converts expressions correctly', () => {
    const registry = buildRegistryFromAnnotations([
      { declName: 'Nat', pattern: '\\N' },
      { declName: 'Zero', pattern: '0' },
      { declName: 'Equal', pattern: '$0 = $1' },
      { declName: 'plus', pattern: '$0 + $1' },
    ]);

    // Symbol mapping: 0 → Zero
    expect(convertToSource(registry, [mkSymbol('0')]).source).toBe('Zero');

    // Symbol mapping: ℕ → Nat
    expect(convertToSource(registry, [mkSymbol('\\mathbb{N}')]).source).toBe('Nat');

    // Infix: a + b → plus a b
    const plusNodes = [mkSymbol('a'), mkSymbol('+'), mkSymbol('b')];
    expect(convertToSource(registry, plusNodes).source).toBe('plus a b');

    // Infix: a = b → Equal a b
    const eqNodes = [mkSymbol('a'), mkSymbol('='), mkSymbol('b')];
    expect(convertToSource(registry, eqNodes).source).toBe('Equal a b');

    // Composed: a + b = c → Equal (plus a b) c
    const composedNodes = [
      mkSymbol('a'), mkSymbol('+'), mkSymbol('b'),
      mkSymbol('='),
      mkSymbol('c'),
    ];
    expect(convertToSource(registry, composedNodes).source).toBe('Equal (plus a b) c');
  });

  test('end-to-end: BigOp sum pattern', () => {
    const registry = buildRegistryFromAnnotations([
      { declName: 'sumFromIndexWithCount', pattern: '\\sum_{= $0}^{$1} $2' },
    ]);

    // Create a BigOp sum with below = [=, 0], above = [n], body = [f]
    const sum = mkBigOp('sum',
      mkRow([mkSymbol('='), mkSymbol('0')]),
      mkRow([mkSymbol('n')]),
      mkRow([mkSymbol('f')])
    );
    const nodes = [sum];
    const result = convertToSource(registry, nodes);
    expect(result.source).toBe('sumFromIndexWithCount 0 n f');
  });

  test('end-to-end: Succ prime pattern', () => {
    const registry = buildRegistryFromAnnotations([
      { declName: 'Succ', pattern: '$0\\prime' },
    ]);

    // Create a Sup node: n' (n with prime superscript)
    const sup = mkSup(mkRow([mkSymbol('n')]), mkRow([mkSymbol('\\prime')]));
    const result = convertToSource(registry, [sup]);
    expect(result.source).toBe('Succ n');
  });

  test('end-to-end: Equal with subscript type annotation', () => {
    const registry = buildRegistryFromAnnotations([
      { declName: 'Nat', pattern: '\\N' },
      { declName: 'Equal', pattern: '$0 =_{$A} $1' },
    ]);

    // Create: a =_ℕ b → Sub node on = with ℕ subscript
    const eqSub = mkSub(mkRow([mkSymbol('=')]), mkRow([mkSymbol('\\mathbb{N}')]));
    const nodes = [mkSymbol('a'), eqSub, mkSymbol('b')];
    const result = convertToSource(registry, nodes);
    expect(result.source).toBe('Equal {Nat} a b');
  });

  test('end-to-end: @becomes with bigop binder — ∑_{k=m}^{n} body', () => {
    const registry = buildRegistryFromAnnotations([
      { declName: 'summation',
        pattern: '\\sum_{$0 = $1}^{$2} $3 @becomes summation $1 $2 (\\$0 => $3)' },
    ]);

    // ∑_{k = m}^{n} with body k
    const sumNode = mkBigOp('sum',
      mkRow([mkSymbol('k'), mkSymbol('='), mkSymbol('m')]),  // below: k = m
      mkRow([mkSymbol('n')]),                                 // above: n
      mkRow([mkSymbol('k')]),                                 // body: k
    );
    const nodes = [sumNode];
    const result = convertToSource(registry, nodes);
    expect(result.source).toBe('summation m n (\\k => k)');
  });

  test('end-to-end: ∑_{j=i}^{n\'} j with Succ pattern — upper limit is Sup node', () => {
    const registry = buildRegistryFromAnnotations([
      { declName: 'Succ', pattern: '$0\\prime' },
      { declName: 'sum',
        pattern: '\\sum_{$0 = $1}^{$2} $3 @becomes sum $$1 $$2 (\\$0 => $$3)' },
    ]);

    // ∑_{j = i}^{n'} j — upper limit n' is a Sup(n, prime) node
    const nPrime = mkSup(mkRow([mkSymbol('n')]), mkRow([mkSymbol('\\prime')]));
    const sumNode = mkBigOp('sum',
      mkRow([mkSymbol('j'), mkSymbol('='), mkSymbol('i')]),  // below: j = i
      mkRow([nPrime]),                                        // above: n'
      mkRow([mkSymbol('j')]),                                 // body: j
    );
    const result = convertToSource(registry, [sumNode]);
    // BigOp wraps in parens since it produces multi-arg application
    expect(result.source).toContain('sum i (Succ n) (\\j => j)');
  });

  test('Succ pattern converts standalone Sup node', () => {
    const registry = buildRegistryFromAnnotations([
      { declName: 'Succ', pattern: '$0\\prime' },
    ]);
    const nPrime = mkSup(mkRow([mkSymbol('n')]), mkRow([mkSymbol('\\prime')]));
    // As a single node in a row
    const result = convertToSource(registry, [nPrime]);
    expect(result.source).toBe('Succ n');
  });

  test('Succ pattern converts Sup node inside body expression', () => {
    const registry = buildRegistryFromAnnotations([
      { declName: 'Succ', pattern: '$0\\prime' },
      { declName: 'Equal', pattern: '$0 = $1' },
    ]);
    const nPrime = mkSup(mkRow([mkSymbol('n')]), mkRow([mkSymbol('\\prime')]));
    // n' = m  — Sup node followed by = and m
    const result = convertToSource(registry, [nPrime, mkSymbol('='), mkSymbol('m')]);
    expect(result.source).toBe('Equal (Succ n) m');
  });
});

// ============================================================================
// isRecord propagation
// ============================================================================

describe('isRecord propagation', () => {
  test('buildRegistryFromAnnotations propagates isRecord to symbolMap', () => {
    const registry = buildRegistryFromAnnotations([
      { declName: 'PeanoNat', pattern: '\\N', isRecord: true },
    ]);
    const entry = registry.symbolMap.get('\\mathbb{N}');
    expect(entry).toBeDefined();
    expect(entry!.isRecord).toBe(true);
  });

  test('isRecord defaults to undefined for inductive types', () => {
    const registry = buildRegistryFromAnnotations([
      { declName: 'Nat', pattern: '\\N' },
    ]);
    const entry = registry.symbolMap.get('\\mathbb{N}');
    expect(entry).toBeDefined();
    expect(entry!.isRecord).toBeUndefined();
  });

  test('lookupSymbol returns isRecord through parent chain', () => {
    const parent = buildRegistryFromAnnotations([
      { declName: 'PeanoNat', pattern: '\\N', isRecord: true },
    ]);
    const child: SyntaxRegistry = { entries: [], symbolMap: new Map(), parent };
    const result = lookupSymbol(child, '\\mathbb{N}');
    expect(result).toBeDefined();
    expect(result!.isRecord).toBe(true);
  });
});

// ============================================================================
// @syntax @unfold
// ============================================================================

describe('@syntax @unfold', () => {
  test('parseSyntaxAnnotation recognizes @unfold', () => {
    const result = parseSyntaxAnnotation('@unfold', 'EpsDeltaWitness');
    expect(result.unfold).toBe(true);
    expect(result.symbolMapping).toBeUndefined();
    expect(result.entry).toBeUndefined();
  });

  test('parseSyntaxAnnotation with leading/trailing spaces', () => {
    const result = parseSyntaxAnnotation('  @unfold  ', 'Foo');
    expect(result.unfold).toBe(true);
  });

  test('buildRegistryFromAnnotations collects unfoldNames', () => {
    const registry = buildRegistryFromAnnotations([
      { declName: 'plus', pattern: '$0 + $1' },
      { declName: 'EpsDeltaWitness', pattern: '@unfold' },
      { declName: 'MyAlias', pattern: '@unfold' },
    ]);

    expect(registry.unfoldNames).toBeDefined();
    expect(registry.unfoldNames!.has('EpsDeltaWitness')).toBe(true);
    expect(registry.unfoldNames!.has('MyAlias')).toBe(true);
    expect(registry.unfoldNames!.has('plus')).toBe(false);
    // Other annotations should still be processed normally
    expect(registry.entries).toHaveLength(1);
    expect(registry.entries[0].name).toBe('plus');
  });

  test('buildRegistryFromAnnotations omits unfoldNames when none present', () => {
    const registry = buildRegistryFromAnnotations([
      { declName: 'plus', pattern: '$0 + $1' },
    ]);

    expect(registry.unfoldNames).toBeUndefined();
  });
});
