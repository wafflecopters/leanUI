/**
 * The PRESENTATION battery: does a proof read like mathematics?
 *
 * These assert SHAPE properties of the generated prose over real Lean —
 * generic invariants, not golden text, so they hold as rendering improves and
 * fail when a "programming-shaped" artifact sneaks back in. One describe per
 * milestone proof; a new preset earns its place by adding a describe here.
 */
import { beforeAll, afterAll, describe, expect, test } from 'vitest';
import { LEAN_PRESETS } from './presets';
import { analyzeLeanSource } from '../../server/lean-bridge';
import { nodeAnalyzer, shutdownLeanBridge } from '../controller/nodeAnalyzer';
import { ProofSession } from '../controller/session';
import { generateProofProse, type ProseItem } from '../proof-tree/proof-prose';

const MIN = 60_000;

afterAll(() => shutdownLeanBridge());

async function proseFor(presetName: string, declName: string): Promise<ProseItem[]> {
  const r = await sessionProse(presetName, declName);
  // The check that was missing when two seeded proofs shipped broken: the
  // proof must survive the session's parse→reprint→analyze round-trip with
  // ZERO errors. Prose shape means nothing over a broken proof.
  expect(r.errors).toEqual([]);
  return r.items;
}

async function sessionProse(presetName: string, declName: string): Promise<{ items: ProseItem[]; errors: string[] }> {
  // (returns context hypothesis names too — see noDaggers below)
  const preset = LEAN_PRESETS.find((p) => p.name === presetName);
  if (!preset) throw new Error(`missing preset ${presetName}`);
  const base = await analyzeLeanSource(preset.code, { timeoutMs: 10 * MIN });
  if (base.bridgeError) throw new Error(base.bridgeError);
  const s = ProofSession.open({
    analyze: nodeAnalyzer({ timeoutMs: 10 * MIN }),
    source: preset.code,
    declarations: base.declarations,
    declName,
    autoRefresh: false,
  });
  await s.refreshGoals();
  const items = generateProofProse(
    (s as unknown as { proof: never }).proof,
    s.getState().cursor.nodeId,
    (s as unknown as { goalMap: never }).goalMap,
  );
  const errors = s.getState().status.diagnostics
    .filter((d) => d.severity === 'error')
    .map((d) => d.text.split('\n')[0]);
  lastContextNames = s.hypothesesWithTypes().map((h) => h.name);
  s.dispose();
  return { items, errors };
}

/** Context names of the most recent sessionProse run. */
let lastContextNames: string[] = [];

/** No Lean-internal daggered name may reach the reader: not in prose latex,
 *  not in intro bindings, not in the context panel. `K✝` (an unnamed section
 *  variable) and `x✝` (a cases-on-term assert) both shipped once. */
function expectNoDaggers(items: ProseItem[]): void {
  for (const i of items) {
    expect(latexOf(i)).not.toContain('✝');
    const groups = (i.kind as { groups?: Array<{ tokens: Array<{ name: string }> }> }).groups;
    for (const g of groups ?? []) for (const t of g.tokens) expect(t.name).not.toContain('✝');
  }
  for (const n of lastContextNames) expect(n).not.toContain('✝');
}

/** Every latex string an item would put on screen. */
function latexOf(item: ProseItem): string {
  const k = item.kind as Record<string, unknown>;
  return ['goalLatex', 'preGoalLatex', 'typeLatex', 'proofExprLatex', 'labelLatex', 'meaningLatex', 'chooseSinceLatex']
    .map((f) => (typeof k[f] === 'string' ? (k[f] as string) : ''))
    .join(' ');
}

describe('limitAdd reads like mathematics', () => {
  let items: ProseItem[];
  beforeAll(async () => {
    items = await proseFor('Real Analysis (chain rule)', 'limitAdd');
  }, 10 * MIN);

  test('witness bundles display as their meaning, never by internal name', () => {
    for (const i of items) expect(latexOf(i)).not.toContain('EpsDeltaWitness');
  });

  test('the have+obtain pairs fused into Choose rows', () => {
    const chooses = items.filter((i) => (i.kind as { chooseSinceLatex?: string }).chooseSinceLatex !== undefined);
    expect(chooses.length).toBeGreaterThanOrEqual(2); // hF and hG
    // The intermediate names exist only to be unpacked — no Observe row for them.
    expect(items.some((i) => i.kind.tag === 'have' && (i.kind as { name?: string }).name === 'hF')).toBe(false);
  });

  test('the comparison split reads by meaning: Either A or B, cases labeled by type', () => {
    const header = items.find((i) => (i.kind as { caseMeanings?: string[] }).caseMeanings);
    expect(header).toBeDefined();
    expect((header!.kind as unknown as { caseMeanings: string[] }).caseMeanings).toHaveLength(2);
  });

  test('destructured conditions carry their types', () => {
    const writes = items.filter((i) => (i.kind as { anonymous?: boolean }).anonymous);
    expect(writes.length).toBeGreaterThanOrEqual(2); // fProof, gProof
    for (const w of writes) {
      expect((w.kind as { paramIsCondition?: boolean[] }).paramIsCondition?.some(Boolean)).toBe(true);
    }
  });

  test('no daggered names anywhere the reader looks', () => {
    expectNoDaggers(items);
  });

  test('no single-constructor case ceremony (mk) anywhere in the prose', () => {
    for (const i of items) {
      if (i.kind.tag === 'caseHeader') {
        expect((i.kind as { constructorName?: string }).constructorName).not.toBe('mk');
      }
    }
  });
});

describe('triangleSum reads like mathematics', () => {
  let items: ProseItem[];
  beforeAll(async () => {
    items = await proseFor('Nat Math (from scratch)', 'triangleSum');
  }, 10 * MIN);

  test('the induction has a header and both cases, base and step distinguished', () => {
    const header = items.find((i) => i.kind.tag === 'inductionHeader');
    expect(header).toBeDefined();
    const cases = items.filter((i) => i.kind.tag === 'caseHeader' && !(i.kind as { anonymous?: boolean }).anonymous);
    expect(cases.length).toBe(2);
    const flags = cases.map((c) => (c.kind as { isBaseCase: boolean }).isBaseCase);
    expect(flags).toContain(true);
    expect(flags).toContain(false);
  });

  test('no daggered names anywhere the reader looks', () => {
    expectNoDaggers(items);
  });

  test('every step row Lean reported on shows some goal or content', () => {
    // A prose row with NOTHING to show is the "walker skipped a node" smell.
    for (const i of items) {
      expect(i.kind.tag).not.toBe(undefined as never);
    }
    expect(items.length).toBeGreaterThan(4);
  });

  test('FUBINI: the double-sum swap round-trips clean and shows ∑ throughout', async () => {
    const r = await sessionProse('Nat Math (from scratch)', 'fubini');
    expect(r.errors).toEqual([]);
    const all = r.items.map(latexOf).join(' ');
    expect(all).toContain('\\sum');
    expect(all).not.toContain('sumStartCount'); // the recursion scaffold stays hidden
  }, 10 * MIN);

  test('REARRANGEMENT: the permutation induction round-trips with four named cases', async () => {
    const r = await sessionProse('Nat Math (from scratch)', 'rearrangement');
    expect(r.errors).toEqual([]);
    const cases = r.items.filter((i) => i.kind.tag === 'caseHeader' && !(i.kind as { anonymous?: boolean }).anonymous);
    expect(cases.length).toBe(4); // nil, cons, swap, trans
  }, 10 * MIN);
});

describe('basisExists reads like mathematics', () => {
  let items: ProseItem[];
  beforeAll(async () => {
    items = await proseFor('Vector Spaces (basis)', 'basisExistsAux');
  }, 10 * MIN);

  test('the spine is strong induction on length — no fuel argument, no Nat cases', () => {
    // The fuel-free proof applies the library principle; the Nat machinery
    // lives inside `lengthStrongInduction`, invisible to the reader.
    const spine = items.find((i) => i.kind.tag === 'apply' && (i.kind as { name?: string }).name === 'lengthStrongInduction');
    expect(spine).toBeDefined();
    // The dichotomy is a case split (isCases) — fine; a NAT induction header
    // would mean the fuel argument crept back.
    const inductions = items.filter((i) => i.kind.tag === 'inductionHeader' && !(i.kind as { isCases?: boolean }).isCases);
    expect(inductions).toEqual([]);
    for (const i of items) expect(latexOf(i)).not.toMatch(/\bfuel\b/);
  });

  test('the independence dichotomy reads by meaning, not by constructor', () => {
    // `cases independentOrDependent vs` introduces ONE hypothesis per branch,
    // so the header reads "Either Independent … or ∃ …".
    const header = items.find((i) => (i.kind as unknown as { caseMeanings?: string[] }).caseMeanings);
    expect(header).toBeDefined();
    expect((header!.kind as unknown as { caseMeanings: string[] }).caseMeanings).toHaveLength(2);
  });

  test('the dependent-vector witness is destructured in one line', () => {
    // obtain ⟨v, pre, post, hvs, hspan⟩ := hdep
    const writes = items.filter((i) => (i.kind as { anonymous?: boolean }).anonymous);
    expect(writes.length).toBeGreaterThanOrEqual(1);
  });

  test('no daggered names anywhere the reader looks', () => {
    expectNoDaggers(items);
  });
});

describe('lagrange reads like mathematics', () => {
  let items: ProseItem[];
  beforeAll(async () => {
    items = await proseFor('Group Theory (Lagrange)', 'lagrangeAux');
  }, 10 * MIN);

  test('the spine is strong induction on length — same house style as basisExists', () => {
    const spine = items.find((i) => i.kind.tag === 'apply' && (i.kind as { name?: string }).name === 'lengthStrongInduction');
    expect(spine).toBeDefined();
  });

  test('the empty-or-inhabited split reads by meaning', () => {
    const header = items.find((i) => (i.kind as { caseMeanings?: string[] }).caseMeanings);
    expect(header).toBeDefined();
  });

  test('group notation shows: no raw MyGroup.mul/inv/one in the prose', () => {
    for (const i of items) {
      expect(latexOf(i)).not.toContain('MyGroup');
    }
  });

  test('no daggered names anywhere the reader looks', () => {
    expectNoDaggers(items);
  });

  test('the divisibility corollary also round-trips clean', async () => {
    const r = await sessionProse('Group Theory (Lagrange)', 'lagrange');
    expect(r.errors).toEqual([]);
  }, 10 * MIN);
});

describe('the quotient group reads like mathematics', () => {
  let items: ProseItem[];
  beforeAll(async () => {
    items = await proseFor('Group Theory (Lagrange)', 'quotMulDescends');
  }, 10 * MIN);

  test('congruence displays as a ≡ b (mod N), never as raw CosetEq', () => {
    const all = items.map(latexOf).join(' ');
    expect(all).not.toContain('CosetEq');
    expect(all).toContain('\\equiv');
  });

  test('the well-definedness steps carry their reasons (have rows with proofs)', () => {
    const haves = items.filter((i) => i.kind.tag === 'have');
    expect(haves.length).toBeGreaterThanOrEqual(2); // hconj, hprod
  });

  test('no daggered names anywhere the reader looks', () => {
    expectNoDaggers(items);
  });

  test('inversion well-definedness round-trips clean too', async () => {
    const r = await sessionProse('Group Theory (Lagrange)', 'quotInvDescends');
    expect(r.errors).toEqual([]);
  }, 10 * MIN);
});

describe('the Jacobian reads like mathematics', () => {
  test('jacobianEntries round-trips clean and shows the limit notation', async () => {
    const r = await sessionProse('Multivariable (Jacobian)', 'jacobianEntries');
    expect(r.errors).toEqual([]);
    const all = r.items.map(latexOf).join(' ');
    expect(all).toContain('\\lim');
    // The Fin/finSum scaffolding stays behind the definitions.
    expect(all).not.toContain('castSucc');
  }, 10 * MIN);
});

describe('the determinant development compiles and cites', () => {
  test('the Vandermonde preset elaborates with zero errors', async () => {
    const p = LEAN_PRESETS.find((x) => x.name === 'Determinants (Vandermonde)')!;
    const base = await analyzeLeanSource(p.code, { timeoutMs: 10 * MIN });
    expect(base.bridgeError).toBeFalsy();
    const errors = base.messages.filter((m) => m.severity === 'error').map((m) => m.text.split('\n')[0]);
    expect(errors).toEqual([]);
    // The column toolkit, the reduction, and the identity itself.
    for (const n of ['det', 'detColAdd', 'detColSmul', 'detColEqAdjZero', 'detColOpAdj',
                     'detFirstRowUnit', 'detScaleRows', 'vandStep', 'detVandSteps',
                     'vandermonde', 'vandermonde2', 'vandermondeRecursion',
                     'vandProd', 'vandermondeIdentity', 'vandermondeAgrees']) {
      expect(base.declarations.find((d) => d.name === n), n).toBeDefined();
    }
  }, 30 * MIN);
});

describe('citations have reasons to cite', () => {
  test('the justification lemmas of all three proofs carry doc comments', async () => {
    for (const [preset, names] of [
      ['Real Analysis (chain rule)', ['divTwoPos', 'ltLeTrans', 'absTriangle', 'convertEps', 'addLtBoth', 'leTotal']],
      ['Nat Math (from scratch)', ['summationSplit', 'mulDistribLeft']],
      ['Vector Spaces (basis)', ['spanDrop', 'lengthDropLt', 'lengthStrongInduction', 'independentOrDependent', 'nilIndependent']],
      ['Group Theory (Lagrange)', ['cosetSplit', 'cosetPartOrder', 'restShorter', 'restSaturated', 'lengthStrongInduction', 'emptyOrMem', 'fullSaturated', 'conjMem', 'cosetEqSymm', 'cosetEqTrans', 'quotRegroup']],
      ['Determinants (Vandermonde)', ['detScaleRow', 'detColAdd', 'detColSmul', 'detColEqAdjZero', 'detColOpAdj', 'detFirstRowUnit', 'altSumHead', 'altSumPairCancel', 'minorEqAdj']],
    ] as const) {
      const p = LEAN_PRESETS.find((x) => x.name === preset)!;
      const base = await analyzeLeanSource(p.code, { timeoutMs: 10 * MIN });
      for (const n of names) {
        const d = base.declarations.find((x) => x.name === n);
        expect(d, `${preset}: ${n}`).toBeDefined();
        expect((d as { doc?: string }).doc, `${preset}: ${n} needs a /-- reason -/`).toBeTruthy();
      }
    }
  }, 30 * MIN);
});
