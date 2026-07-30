/**
 * Ask LEAN what it would suggest — the other half of the suggestion engine.
 *
 * `candidates.ts` proposes moves from the file's own lemmas; this asks Lean's
 * built-in search (`exact?`, `simp?`) what it can find. The two are
 * complementary: Lean's search is strong on library lemmas and closers, and
 * weak on the presets' Type-valued relations, where the file-lemma ranking
 * finds things `exact?` never will.
 *
 * Discovered tactics come back as ordinary candidates, so they go through the
 * same validation as everything else and earn the same previews and honest
 * `closes` flags — rather than being trusted on Lean's word and shown unproven.
 */
import type { ProofNode, ProofNodeId } from '../proof-tree/proof-tree';
import { assembleProofInSource } from '../lean/assembleProofDecl';
import {
  DISCOVERY_TACTICS,
  suggestionsFromMessages,
  type LeanSuggestion,
} from '../lean/leanSuggestions';
import type { LeanAnalyzer } from './analyzer';
import type { CancelToken } from './validate';

export interface DiscoverInput {
  analyze: LeanAnalyzer;
  source: string;
  declLine: number;
  nextDeclLine?: number;
  proof: ProofNode;
  /** The hole to run the discovery tactic at. */
  cursorId: ProofNodeId;
  mathlib?: boolean;
  cancel?: CancelToken;
}

/**
 * Run each discovery tactic at the cursor hole and collect its `Try this:`
 * results. Probes run concurrently — `exact?` can be slow, and there's no
 * reason `simp?` should queue behind it.
 */
export async function discoverSuggestions(input: DiscoverInput): Promise<LeanSuggestion[]> {
  const { analyze, source, declLine, nextDeclLine, proof, cursorId, mathlib, cancel } = input;

  const probes = DISCOVERY_TACTICS.map(async ({ kind, tactic }) => {
    if (cancel?.cancelled) return [];
    let assembled;
    try {
      assembled = assembleProofInSource({
        source,
        decl: { line: declLine },
        nextDeclLine,
        proof,
        holeOverrideId: cursorId,
        holeOverrideTactic: tactic,
      });
    } catch {
      return [];
    }
    const data = await analyze({
      source: assembled.source,
      prefix: assembled.prefixSource,
      body: assembled.bodySource,
      mathlib,
    });
    if (!data || cancel?.cancelled) return [];
    return suggestionsFromMessages(data.messages, kind);
  });

  const found = (await Promise.all(probes)).flat();
  const seen = new Set<string>();
  return found.filter((s) => (seen.has(s.tactic) ? false : (seen.add(s.tactic), true)));
}

export interface SimpNarrowInput extends Omit<DiscoverInput, 'cancel'> {
  /** The lemmas offered to simp. */
  lemmas: readonly string[];
}

/**
 * Which of `lemmas` did simp actually USE?
 *
 * The ring-solver candidate offers simp every equality lemma in the file, so
 * when it fires the proof would otherwise record a wall of names. `simp?`
 * reports `Try this: simp only [<fired subset>]`, which is both shorter and
 * more informative — it says which facts the step actually depended on.
 * Returns null when it couldn't be determined; the caller keeps the broad form.
 */
export async function narrowSimpLemmas(input: SimpNarrowInput): Promise<string[] | null> {
  const { analyze, source, declLine, nextDeclLine, proof, cursorId, lemmas, mathlib } = input;
  let assembled;
  try {
    assembled = assembleProofInSource({
      source,
      decl: { line: declLine },
      nextDeclLine,
      proof,
      holeOverrideId: cursorId,
      holeOverrideTactic: `simp? [${lemmas.join(', ')}]`,
    });
  } catch {
    return null;
  }
  const data = await analyze({
    source: assembled.source,
    prefix: assembled.prefixSource,
    body: assembled.bodySource,
    mathlib,
  });
  if (!data) return null;
  for (const m of data.messages) {
    const fired = m.text.match(/simp only \[([^\]]*)\]/);
    if (fired) return fired[1].split(',').map((s) => s.trim()).filter(Boolean);
  }
  return null;
}
