/**
 * Ask Lean which lemmas a `simp [...]` actually USED, via `simp?` (which reports
 * `Try this: simp only [<fired subset>]`). Used to narrow a broad
 * `simp [<many lemmas>]` down to just the lemmas that fired, so the proof reads
 * cleanly and shows what mattered.
 */
import type { ProofNode, ProofNodeId } from '../proof-tree/proof-tree';
import type { AnalyzeResult } from './types';
import { assembleProofInSource } from './assembleProofDecl';
import { analyzeRequest } from './analyzeClient';

export interface ProbeSimpFiredArgs {
  source: string;
  declLine: number;
  nextDeclLine?: number;
  proof: ProofNode;
  /** The hole where the simp runs. */
  cursorId: ProofNodeId;
  /** Lemmas offered to simp. */
  lemmas: readonly string[];
  mathlib?: boolean;
}

/**
 * Returns the subset of `lemmas` that simp actually fired (Lean's `simp?`
 * suggestion), or null if it couldn't be determined.
 */
export async function probeSimpFired(args: ProbeSimpFiredArgs): Promise<string[] | null> {
  const { source, declLine, nextDeclLine, proof, cursorId, lemmas, mathlib } = args;
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
  // Background request: must not hold a browser connection the goal refresh needs.
  const data = await analyzeRequest(
    { source: assembled.source, prefix: assembled.prefixSource, body: assembled.bodySource, mathlib },
    { background: true },
  );
  if (!data) return null;
  // `Try this: … simp only [a, b, c]` — pull out the fired lemma list.
  for (const m of data.messages) {
    const mm = m.text.match(/simp only \[([^\]]*)\]/);
    if (mm) return mm[1].split(',').map((s) => s.trim()).filter(Boolean);
  }
  return null;
}
