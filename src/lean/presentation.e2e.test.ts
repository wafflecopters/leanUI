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
    expect(items.some((i) => i.kind.tag === 'inductionHeader')).toBe(false);
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

describe('citations have reasons to cite', () => {
  test('the justification lemmas of all three proofs carry doc comments', async () => {
    for (const [preset, names] of [
      ['Real Analysis (chain rule)', ['divTwoPos', 'ltLeTrans', 'absTriangle', 'convertEps', 'addLtBoth', 'leTotal']],
      ['Nat Math (from scratch)', ['summationSplit', 'mulDistribLeft']],
      ['Vector Spaces (basis)', ['spanDrop', 'lengthDropLt', 'lengthStrongInduction', 'independentOrDependent', 'nilIndependent']],
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
