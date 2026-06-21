/**
 * Validate candidate tactic suggestions against Lean BEFORE showing them — the
 * "try before you suggest" behaviour: a pill only appears if its tactic actually
 * applies at the cursor goal.
 *
 * For each candidate we splice its (single-line) validation tactic in place of
 * the cursor hole, analyze, and keep it iff Lean reports NO error AT the hole's
 * line. A genuine tactic failure (type mismatch, "did not find occurrence",
 * unknown identifier, …) is reported at that line; a tactic that applies but
 * leaves work reports "unsolved goals" elsewhere (the `by` line), which does NOT
 * count — so both closers (`exact .refl`) and progress tactics (`rw [lemma]`,
 * `induction n`) are judged correctly. Scoping to the hole line also means a
 * failing tactic elsewhere in the proof can't suppress valid suggestions.
 *
 * Trials run with bounded concurrency and surface incrementally.
 */
import { useEffect, useRef, useState } from 'react';
import type { ProofNode, ProofNodeId } from '../proof-tree/proof-tree';
import type { AnalyzeResult } from './types';
import { assembleProofInSource } from './assembleProofDecl';
import type { LeanSuggestion } from './leanSuggestions';

export interface UseLeanValidatedSuggestionsArgs {
  source: string;
  declLine: number;
  nextDeclLine?: number;
  proof: ProofNode;
  cursorId: ProofNodeId;
  cursorIsHole: boolean;
  /** Candidate suggestions to validate (already ordered by the caller). */
  candidates: readonly LeanSuggestion[];
  mathlib?: boolean;
  enabled?: boolean;
}

const EMPTY = { suggestions: [] as LeanSuggestion[], loading: false };

async function analyze(source: string, mathlib?: boolean): Promise<AnalyzeResult | null> {
  try {
    const resp = await fetch('/api/analyze', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ source, mathlib }),
    });
    return (await resp.json()) as AnalyzeResult;
  } catch {
    return null;
  }
}

/** Map an array through `fn` with at most `limit` concurrent calls. */
async function mapPool<T>(items: readonly T[], limit: number, fn: (t: T) => Promise<void>): Promise<void> {
  let next = 0;
  async function worker() {
    for (;;) {
      const i = next++;
      if (i >= items.length) return;
      await fn(items[i]);
    }
  }
  await Promise.all(Array.from({ length: Math.min(limit, items.length) }, worker));
}

export function useLeanValidatedSuggestions(args: UseLeanValidatedSuggestionsArgs): { suggestions: LeanSuggestion[]; loading: boolean } {
  const { source, declLine, nextDeclLine, proof, cursorId, cursorIsHole, candidates, mathlib, enabled = true } = args;
  const [state, setState] = useState(EMPTY);
  const reqRef = useRef(0);

  // Stable key so the effect doesn't re-run on a fresh candidate-array identity.
  const candKey = candidates.map((c) => c.id).join('|');

  useEffect(() => {
    if (!enabled || !source || !cursorIsHole || candidates.length === 0) {
      setState(EMPTY);
      return;
    }
    const reqId = ++reqRef.current;
    let cancelled = false;
    setState({ suggestions: [], loading: true });

    const handle = setTimeout(async () => {
      const valid: LeanSuggestion[] = [];
      await mapPool(candidates, 4, async (cand) => {
        if (cancelled || reqId !== reqRef.current) return;
        let assembled;
        try {
          assembled = assembleProofInSource({
            source,
            decl: { line: declLine },
            nextDeclLine,
            proof,
            holeOverrideId: cursorId,
            holeOverrideTactic: cand.validateTactic ?? cand.tactic,
          });
        } catch {
          return;
        }
        const holeLine = assembled.lean.nodeRanges.get(cursorId)?.startLine;
        const data = await analyze(assembled.source, mathlib);
        if (cancelled || reqId !== reqRef.current || !data || holeLine === undefined) return;
        // Valid iff no error AT the candidate's own line (errors elsewhere — the
        // `by`-line "unsolved goals", or unrelated failing tactics — don't count).
        const failsHere = data.messages.some((m) => m.severity === 'error' && m.startLine === holeLine);
        if (!failsHere) {
          valid.push(cand);
          // Preserve the caller's candidate order as results stream in.
          valid.sort((a, b) => candidates.indexOf(a) - candidates.indexOf(b));
          setState({ suggestions: [...valid], loading: true });
        }
      });
      if (!cancelled && reqId === reqRef.current) setState({ suggestions: valid, loading: false });
    }, 450);

    return () => {
      cancelled = true;
      clearTimeout(handle);
    };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [source, declLine, nextDeclLine, proof, cursorId, cursorIsHole, candKey, mathlib, enabled]);

  return state;
}
