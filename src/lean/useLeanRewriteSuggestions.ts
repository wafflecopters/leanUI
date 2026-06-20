/**
 * "Try the file's rewrite lemmas at this goal" — the core-Lean stand-in for
 * Mathlib's `rw?`. For each candidate equality lemma we splice `rw [lemma]` in
 * place of the cursor hole, analyze, and keep the lemmas whose rewrite actually
 * fires (i.e. Lean does NOT report a rewrite failure). Trials run with bounded
 * concurrency and surface incrementally.
 *
 * Note: this needs the preset to use Lean's native `Eq` — `rw` cannot rewrite a
 * custom `Equal` type.
 */
import { useEffect, useRef, useState } from 'react';
import type { ProofNode, ProofNodeId } from '../proof-tree/proof-tree';
import type { AnalyzeResult } from './types';
import { assembleProofInSource } from './assembleProofDecl';
import type { LeanSuggestion } from './leanSuggestions';
import type { RewriteCandidate } from './rewriteCandidates';

export interface UseLeanRewriteSuggestionsArgs {
  source: string;
  declLine: number;
  nextDeclLine?: number;
  proof: ProofNode;
  cursorId: ProofNodeId;
  cursorIsHole: boolean;
  /** Equality lemmas to try, already ranked + capped by the caller. */
  candidates: readonly RewriteCandidate[];
  mathlib?: boolean;
  enabled?: boolean;
}

const EMPTY = { suggestions: [] as LeanSuggestion[], loading: false };

/** Errors that mean the rewrite did NOT apply (vs. "unsolved goals" = it did). */
const REWRITE_FAILED = /did not find|motive is not|expected an equality|unknown identifier|unknown constant|failed to rewrite/i;

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
async function mapPool<T, R>(items: readonly T[], limit: number, fn: (t: T) => Promise<R>): Promise<R[]> {
  const out: R[] = new Array(items.length);
  let next = 0;
  async function worker() {
    for (;;) {
      const i = next++;
      if (i >= items.length) return;
      out[i] = await fn(items[i]);
    }
  }
  await Promise.all(Array.from({ length: Math.min(limit, items.length) }, worker));
  return out;
}

export function useLeanRewriteSuggestions(args: UseLeanRewriteSuggestionsArgs): { suggestions: LeanSuggestion[]; loading: boolean } {
  const { source, declLine, nextDeclLine, proof, cursorId, cursorIsHole, candidates, mathlib, enabled = true } = args;
  const [state, setState] = useState(EMPTY);
  const reqRef = useRef(0);

  // Stable key so the effect doesn't re-run on a fresh candidate-array identity.
  const candKey = candidates.map((c) => c.name).join(',');

  useEffect(() => {
    if (!enabled || !source || !cursorIsHole || candidates.length === 0) {
      setState(EMPTY);
      return;
    }
    const reqId = ++reqRef.current;
    let cancelled = false;
    setState({ suggestions: [], loading: true });

    const handle = setTimeout(async () => {
      const found: LeanSuggestion[] = [];
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
            holeOverrideTactic: `rw [${cand.name}]`,
          });
        } catch {
          return;
        }
        const data = await analyze(assembled.source, mathlib);
        if (cancelled || reqId !== reqRef.current || !data) return;
        const fired = !data.messages.some((m) => m.severity === 'error' && REWRITE_FAILED.test(m.text));
        if (fired) {
          found.push({ id: `lean-rw:${cand.name}`, label: `rw [${cand.name}]`, tactic: `rw [${cand.name}]`, kind: 'rw' });
          // Surface incrementally as each firing lemma is confirmed.
          setState({ suggestions: [...found], loading: true });
        }
      });
      if (!cancelled && reqId === reqRef.current) setState({ suggestions: found, loading: false });
    }, 450);

    return () => {
      cancelled = true;
      clearTimeout(handle);
    };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [source, declLine, nextDeclLine, proof, cursorId, cursorIsHole, candKey, mathlib, enabled]);

  return state;
}
