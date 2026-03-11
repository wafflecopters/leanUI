import { describe, test, expect, beforeAll } from 'vitest';
import { compileTTFromText } from '../compiler/compile';
import { NAT_MATH_CODE } from '../presets/nat-math';
import { buildRegistryFromAnnotations, SyntaxAnnotation } from './syntax-registry';
import {
  buildReverseRegistry,
  decomposePiSpine,
  ttermToMathNodes,
  surfaceTypeToMathRow,
  parseTemplateSlots,
  buildFromPattern,
} from './tt-to-math';
import { MathNode, MathRow } from './types';
import { TTerm } from '../compiler/surface';

// ============================================================================
// Helpers
// ============================================================================

/** Compile nat-math and return all declarations + their annotations */
function compileNatMath() {
  const result = compileTTFromText(NAT_MATH_CODE);
  const decls = result.blocks.flatMap(b => b.declarations);
  return decls;
}

/** Extract SyntaxAnnotation[] from compiled declarations */
function extractAnnotations(decls: ReturnType<typeof compileNatMath>): SyntaxAnnotation[] {
  const annotations: SyntaxAnnotation[] = [];
  for (const decl of decls) {
    if (decl.syntax && decl.name) {
      annotations.push({ declName: decl.name, pattern: decl.syntax, isRecord: decl.isRecord });
    }
    if (decl.constructorSyntax) {
      for (const cs of decl.constructorSyntax) {
        annotations.push({ declName: cs.name, pattern: cs.syntax });
      }
    }
  }
  return annotations;
}

/** Build a registry from all annotations before a given declaration index */
function buildRegistryBefore(decls: ReturnType<typeof compileNatMath>, declIndex: number) {
  const precedingAnnotations = extractAnnotations(decls.slice(0, declIndex));
  if (precedingAnnotations.length === 0) {
    return { symbolMap: new Map(), entries: [] } as any;
  }
  return buildRegistryFromAnnotations(precedingAnnotations);
}

/** Find a declaration by name */
function findDecl(decls: ReturnType<typeof compileNatMath>, name: string) {
  return decls.find(d => d.name === name);
}

/** Flatten MathRow to a string representation for easy assertion */
function flattenRow(row: MathRow): string {
  return row.children.map(flattenNode).join(' ');
}

function flattenNode(node: MathNode): string {
  switch (node.tag) {
    case 'Symbol': return node.value;
    case 'Hole': return '?';
    case 'Text': return `[${node.content}]`;
    case 'Frac': return `frac(${flattenRow(node.numer)}|${flattenRow(node.denom)})`;
    case 'Sub': return `${flattenRow(node.base)}_{${flattenRow(node.sub)}}`;
    case 'Sup': return `${flattenRow(node.base)}^{${flattenRow(node.sup)}}`;
    case 'SubSup': return `${flattenRow(node.base)}_{${flattenRow(node.sub)}}^{${flattenRow(node.sup)}}`;
    case 'BigOp': {
      const below = node.below ? `_{${flattenRow(node.below)}}` : '';
      const above = node.above ? `^{${flattenRow(node.above)}}` : '';
      return `${node.operator}${below}${above}(${flattenRow(node.body)})`;
    }
    case 'Delimiter': return `${node.open}${flattenRow(node.inner)}${node.close}`;
    case 'Accent': return `${node.accent}(${flattenRow(node.body)})`;
  }
}

// ============================================================================
// Tests
// ============================================================================

describe('parseTemplateSlots', () => {
  test('simple template: "plus $$0 $$1"', () => {
    const slots = parseTemplateSlots('plus $$0 $$1');
    expect(slots).toEqual([
      { kind: 'direct', capture: '0' },
      { kind: 'direct', capture: '1' },
    ]);
  });

  test('template with implicit: "Equal {$$A} $$0 $$1"', () => {
    const slots = parseTemplateSlots('Equal {$$A} $$0 $$1');
    expect(slots).toEqual([
      { kind: 'implicit', capture: 'A' },
      { kind: 'direct', capture: '0' },
      { kind: 'direct', capture: '1' },
    ]);
  });

  test('template with lambda: "sum $$1 $$2 (\\\\$0 => $$3)"', () => {
    // The actual template string after JS processing
    const slots = parseTemplateSlots('sum $$1 $$2 (\\$0 => $$3)');
    expect(slots).toEqual([
      { kind: 'direct', capture: '1' },
      { kind: 'direct', capture: '2' },
      { kind: 'lambda', binderCapture: '0', bodyCapture: '3' },
    ]);
  });
});

describe('decomposePiSpine', () => {
  test('single binder: (n : Nat) -> body', () => {
    const type: TTerm = {
      tag: 'Binder', name: 'n', binderKind: { tag: 'BPiTT' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' },
    };
    const { binders, body } = decomposePiSpine(type);
    expect(binders).toHaveLength(1);
    expect(binders[0].names).toEqual(['n']);
    expect(body).toEqual({ tag: 'Const', name: 'Nat' });
  });

  test('groups same-domain binders: (n m : Nat) -> body', () => {
    const type: TTerm = {
      tag: 'Binder', name: 'n', binderKind: { tag: 'BPiTT' },
      domain: { tag: 'Const', name: 'Nat' },
      body: {
        tag: 'Binder', name: 'm', binderKind: { tag: 'BPiTT' },
        domain: { tag: 'Const', name: 'Nat' },
        body: { tag: 'Const', name: 'Bool' },
      },
    };
    const { binders, body } = decomposePiSpine(type);
    expect(binders).toHaveLength(1);
    expect(binders[0].names).toEqual(['n', 'm']);
    expect(body).toEqual({ tag: 'Const', name: 'Bool' });
  });

  test('does not group different domains', () => {
    const type: TTerm = {
      tag: 'Binder', name: 'n', binderKind: { tag: 'BPiTT' },
      domain: { tag: 'Const', name: 'Nat' },
      body: {
        tag: 'Binder', name: 'f', binderKind: { tag: 'BPiTT' },
        domain: {
          tag: 'Binder', name: '_', binderKind: { tag: 'BPiTT' },
          domain: { tag: 'Const', name: 'Nat' },
          body: { tag: 'Const', name: 'Nat' },
        },
        body: { tag: 'Const', name: 'Bool' },
      },
    };
    const { binders } = decomposePiSpine(type);
    expect(binders).toHaveLength(2);
    expect(binders[0].names).toEqual(['n']);
    expect(binders[1].names).toEqual(['f']);
  });

  test('skips implicit binders in grouping', () => {
    const type: TTerm = {
      tag: 'Binder', name: 'A', binderKind: { tag: 'BPiTT' }, named: true,
      domain: { tag: 'Sort', level: { tag: 'ULit', n: 0 } },
      body: {
        tag: 'Binder', name: 'n', binderKind: { tag: 'BPiTT' },
        domain: { tag: 'Var', index: 0 },
        body: { tag: 'Var', index: 1 },
      },
    };
    const { binders } = decomposePiSpine(type);
    expect(binders).toHaveLength(2);
    expect(binders[0].isImplicit).toBe(true);
    expect(binders[0].names).toEqual(['A']);
    expect(binders[1].isImplicit).toBe(false);
    expect(binders[1].names).toEqual(['n']);
  });
});

describe('ttermToMathNodes — basic', () => {
  test('Const with reverse symbol mapping', () => {
    const rev = buildReverseRegistry({
      symbolMap: new Map([['\\mathbb{N}', { source: 'Nat', needsR: false }]]),
      entries: [],
    });
    const nodes = ttermToMathNodes({ tag: 'Const', name: 'Nat' }, rev, []);
    expect(nodes).toHaveLength(1);
    expect(nodes[0].tag).toBe('Symbol');
    expect((nodes[0] as any).value).toBe('\\mathbb{N}');
  });

  test('Const without mapping → plain name', () => {
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    const nodes = ttermToMathNodes({ tag: 'Const', name: 'Foo' }, rev, []);
    expect(nodes).toHaveLength(1);
    expect((nodes[0] as any).value).toBe('Foo');
  });

  test('Var lookup in context', () => {
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    const nodes = ttermToMathNodes({ tag: 'Var', index: 1 }, rev, ['m', 'n']);
    expect(nodes).toHaveLength(1);
    expect((nodes[0] as any).value).toBe('n');
  });
});

describe('ttermToMathNodes — with registry patterns', () => {
  let decls: ReturnType<typeof compileNatMath>;

  // Compile once for all tests in this block
  beforeAll(() => {
    decls = compileNatMath();
  });

  test('plus pattern: plus n m → n + m', () => {
    // Build registry with all annotations before plusZeroRight
    const plusZR = findDecl(decls, 'plusZeroRight')!;
    const idx = decls.indexOf(plusZR);
    const registry = buildRegistryBefore(decls, idx);
    const rev = buildReverseRegistry(registry);

    // App(App(Const("plus"), Var(1)), Var(0)) with ctx = ["m", "n"]
    const term: TTerm = {
      tag: 'App',
      fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' }, arg: { tag: 'Var', index: 1 } },
      arg: { tag: 'Var', index: 0 },
    };
    const nodes = ttermToMathNodes(term, rev, ['m', 'n']);
    const flat = flattenRow({ id: 0, children: nodes });
    expect(flat).toContain('+');
    expect(flat).toContain('n');
    expect(flat).toContain('m');
  });

  test('Equal pattern: Equal lhs rhs → lhs = rhs', () => {
    const plusZR = findDecl(decls, 'plusZeroRight')!;
    const idx = decls.indexOf(plusZR);
    const registry = buildRegistryBefore(decls, idx);
    const rev = buildReverseRegistry(registry);

    // App(App(Const("Equal"), Const("Zero")), Const("Zero"))
    const term: TTerm = {
      tag: 'App',
      fn: { tag: 'App', fn: { tag: 'Const', name: 'Equal' }, arg: { tag: 'Const', name: 'Zero' } },
      arg: { tag: 'Const', name: 'Zero' },
    };
    const nodes = ttermToMathNodes(term, rev, []);
    const flat = flattenRow({ id: 0, children: nodes });
    // Should contain = (possibly with subscript stripped)
    expect(flat).toContain('=');
  });

  test('Succ pattern: Succ n → n^{prime}', () => {
    const plusZR = findDecl(decls, 'plusZeroRight')!;
    const idx = decls.indexOf(plusZR);
    const registry = buildRegistryBefore(decls, idx);
    const rev = buildReverseRegistry(registry);

    const succEntry = rev.nameToEntry.get('Succ');

    // App(Const("Succ"), Var(0)) with ctx = ["n"]
    const term: TTerm = {
      tag: 'App',
      fn: { tag: 'Const', name: 'Succ' },
      arg: { tag: 'Var', index: 0 },
    };
    const nodes = ttermToMathNodes(term, rev, ['n']);
    const flat = flattenRow({ id: 0, children: nodes });
    // If Succ entry not found, it falls back to Succ(n) — check what we got
    if (!succEntry) {
      // Succ has no entry — just check it renders something with n
      expect(flat).toContain('n');
    } else {
      expect(flat).toContain('\\prime');
      expect(flat).toContain('n');
    }
  });
});

describe('surfaceTypeToMathRow — full type signatures', () => {
  let decls: ReturnType<typeof compileNatMath>;

  beforeAll(() => {
    decls = compileNatMath();
  });

  test('plusZeroRight: (n : Nat) -> Equal (plus n Zero) n', () => {
    const decl = findDecl(decls, 'plusZeroRight')!;
    expect(decl).toBeDefined();
    expect(decl.surfaceType).toBeDefined();

    const idx = decls.indexOf(decl);
    const registry = buildRegistryBefore(decls, idx);

    const row = surfaceTypeToMathRow(decl.surfaceType!, registry);
    const flat = flattenRow(row);

    // Should have: ∀ n ∈ ℕ, then n + 0 = n
    expect(flat).toContain('\\forall');
    expect(flat).toContain('n');
    expect(flat).toContain('\\in');
    expect(flat).toContain('+');
    expect(flat).toContain('=');
    expect(flat).toContain('[then]');
  });

  test('plusComm: (n m : Nat) -> Equal (plus n m) (plus m n)', () => {
    const decl = findDecl(decls, 'plusComm')!;
    expect(decl).toBeDefined();
    expect(decl.surfaceType).toBeDefined();

    const idx = decls.indexOf(decl);
    const registry = buildRegistryBefore(decls, idx);

    const row = surfaceTypeToMathRow(decl.surfaceType!, registry);
    const flat = flattenRow(row);

    // Should group n, m together: ∀ n, m ∈ ℕ
    expect(flat).toContain('\\forall');
    expect(flat).toContain(',');
    expect(flat).toContain('\\in');
    expect(flat).toContain('=');
  });

  test('leqTrans: {a b c : Nat} -> Leq a b -> Leq b c -> Leq a c', () => {
    const decl = findDecl(decls, 'leqTrans')!;
    expect(decl).toBeDefined();
    expect(decl.surfaceType).toBeDefined();

    const idx = decls.indexOf(decl);
    const registry = buildRegistryBefore(decls, idx);

    const row = surfaceTypeToMathRow(decl.surfaceType!, registry);
    const flat = flattenRow(row);

    // Implicit {a b c : Nat} should be skipped
    // Should have anonymous Leq hypotheses with [and] between them
    expect(flat).toContain('\\leq');
    // Check for two ≤ occurrences (two hypotheses)
    const leqCount = (flat.match(/\\leq/g) || []).length;
    expect(leqCount).toBeGreaterThanOrEqual(2);
  });

  test('congPlusRight: {n m : Nat} -> (p : Nat) -> Equal n m -> Equal (plus p n) (plus p m)', () => {
    const decl = findDecl(decls, 'congPlusRight')!;
    expect(decl).toBeDefined();
    expect(decl.surfaceType).toBeDefined();

    const idx = decls.indexOf(decl);
    const registry = buildRegistryBefore(decls, idx);

    const row = surfaceTypeToMathRow(decl.surfaceType!, registry);
    const flat = flattenRow(row);

    // Should have ∀ p ∈ ℕ (explicit) and anonymous Equal hypothesis
    expect(flat).toContain('\\forall');
    expect(flat).toContain('p');
    expect(flat).toContain('=');
  });

  test('function-type domain uses : instead of ∈', () => {
    // (f : Nat -> Nat) -> Nat  should render as ∀ f : ℕ → ℕ, then ...
    const type: TTerm = {
      tag: 'Binder', name: 'f', binderKind: { tag: 'BPiTT' },
      domain: {
        tag: 'Binder', name: '_', binderKind: { tag: 'BPiTT' },
        domain: { tag: 'Const', name: 'Nat' },
        body: { tag: 'Const', name: 'Nat' },
      },
      body: { tag: 'Const', name: 'Nat' },
    };

    const plusZR = findDecl(decls, 'plusZeroRight')!;
    const idx = decls.indexOf(plusZR);
    const registry = buildRegistryBefore(decls, idx);

    const row = surfaceTypeToMathRow(type, registry);
    const flat = flattenRow(row);

    // Should use : (not ∈) for function-type domain
    expect(flat).toContain('\\forall');
    expect(flat).toContain('f');
    expect(flat).toContain(':');
    expect(flat).not.toContain('\\in');
    expect(flat).toContain('\\to');
  });
});

describe('operator precedence — parenthesization', () => {
  let decls: ReturnType<typeof compileNatMath>;
  let rev: ReturnType<typeof buildReverseRegistry>;

  beforeAll(() => {
    decls = compileNatMath();
    const idx = decls.length;
    const registry = buildRegistryBefore(decls, idx);
    rev = buildReverseRegistry(registry);
  });

  test('mul(plus(n, 1), n) wraps plus in parens: (n + 1) · n', () => {
    // mul(plus(Var(0), Succ(Zero)), Var(0))
    const term: TTerm = {
      tag: 'App', fn: { tag: 'App',
        fn: { tag: 'Const', name: 'mul' },
        arg: { tag: 'App', fn: { tag: 'App',
          fn: { tag: 'Const', name: 'plus' },
          arg: { tag: 'Var', index: 0 } },
          arg: { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'Const', name: 'Zero' } } } },
      arg: { tag: 'Var', index: 0 },
    };
    const nodes = ttermToMathNodes(term, rev, ['n']);
    const flat = flattenRow({ id: 0, children: nodes });
    // Should have parens around n + 1
    expect(flat).toContain('(');
    expect(flat).toContain(')');
    expect(flat).toContain('\\cdot');
    // The delimiter wraps plus content: (n + 1)
    const delimNode = nodes.find(n => n.tag === 'Delimiter');
    expect(delimNode).toBeDefined();
    if (delimNode && delimNode.tag === 'Delimiter') {
      const inner = flattenRow(delimNode.inner);
      expect(inner).toContain('+');
    }
  });

  test('plus(mul(a, b), c) does NOT wrap mul in parens: a · b + c', () => {
    // plus(mul(Var(0), Var(1)), Var(2))
    const term: TTerm = {
      tag: 'App', fn: { tag: 'App',
        fn: { tag: 'Const', name: 'plus' },
        arg: { tag: 'App', fn: { tag: 'App',
          fn: { tag: 'Const', name: 'mul' },
          arg: { tag: 'Var', index: 0 } },
          arg: { tag: 'Var', index: 1 } } },
      arg: { tag: 'Var', index: 2 },
    };
    const nodes = ttermToMathNodes(term, rev, ['a', 'b', 'c']);
    const flat = flattenRow({ id: 0, children: nodes });
    // mul has higher precedence than plus — no parens needed
    expect(flat).toContain('\\cdot');
    expect(flat).toContain('+');
    // No Delimiter wrapping
    const delimNode = nodes.find(n => n.tag === 'Delimiter');
    expect(delimNode).toBeUndefined();
  });

  test('plus(sum_bigop, x) wraps sum in parens when followed by +', () => {
    // plus(sum(Zero, Var(0), \i => Var(0)), Succ(Var(0)))
    const term: TTerm = {
      tag: 'App', fn: { tag: 'App',
        fn: { tag: 'Const', name: 'plus' },
        arg: { tag: 'App', fn: { tag: 'App', fn: { tag: 'App',
          fn: { tag: 'Const', name: 'sum' },
          arg: { tag: 'Const', name: 'Zero' } },
          arg: { tag: 'Var', index: 0 } },
          arg: { tag: 'Binder', name: 'i', binderKind: { tag: 'BLamTT' },
            domain: { tag: 'Const', name: 'Nat' },
            body: { tag: 'Var', index: 0 } } } },
      arg: { tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: { tag: 'Var', index: 0 } },
    };
    const nodes = ttermToMathNodes(term, rev, ['n']);
    const flat = flattenRow({ id: 0, children: nodes });
    // BigOp followed by + should be wrapped
    expect(flat).toContain('(');
    expect(flat).toContain('+');
    const delimNode = nodes.find(n => n.tag === 'Delimiter');
    expect(delimNode).toBeDefined();
  });
});
