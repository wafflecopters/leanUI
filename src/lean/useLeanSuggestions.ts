import { useEffect, useRef, useState } from 'react';
import type { ProofNode, ProofNodeId } from '../proof-tree/proof-tree';
import type { AnalyzeResult } from './types';
import { assembleProofInSource } from './assembleProofDecl';
import { DISCOVERY_TACTICS, suggestionsFromMessages, type LeanSuggestion } from './leanSuggestions';

/**
 * Lean-backed tactic suggestions for the cursor's hole (the async provider for
 * the suggestion pills). For each discovery tactic (exact?/simp?/apply?/rw?) we
 * assemble the proof with that tactic emitted in place of the cursor hole's
 * `sorry`, run /api/analyze, and parse the `Try this:` messages into
 * suggestions. Debounced; only runs when the cursor is on a hole.
 */
export interface LeanSuggestionsState {
  suggestions: LeanSuggestion[];
  loading: boolean;
}

export interface UseLeanSuggestionsArgs {
  /** Full source file (declaration context). */
  source: string;
  declLine: number;
  nextDeclLine?: number;
  proof: ProofNode;
  /** The cursor node — suggestions are computed only when it's a hole. */
  cursorId: ProofNodeId;
  cursorIsHole: boolean;
  mathlib?: boolean;
  enabled?: boolean;
}

const EMPTY: LeanSuggestionsState = { suggestions: [], loading: false };

async function analyze(
  assembled: { source: string; prefixSource?: string; bodySource?: string },
  mathlib?: boolean,
): Promise<AnalyzeResult | null> {
  try {
    const resp = await fetch('/api/analyze', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      // prefix/body split → server's prefix-olean fast path.
      body: JSON.stringify({
        source: assembled.source,
        prefix: assembled.prefixSource,
        body: assembled.bodySource,
        mathlib,
      }),
    });
    return (await resp.json()) as AnalyzeResult;
  } catch {
    return null;
  }
}

export function useLeanSuggestions(args: UseLeanSuggestionsArgs): LeanSuggestionsState {
  const { source, declLine, nextDeclLine, proof, cursorId, cursorIsHole, mathlib, enabled = true } = args;
  const [state, setState] = useState<LeanSuggestionsState>(EMPTY);
  const reqRef = useRef(0);

  useEffect(() => {
    if (!enabled || !source || !cursorIsHole) {
      setState(EMPTY);
      return;
    }
    const reqId = ++reqRef.current;
    let cancelled = false;
    setState({ suggestions: [], loading: true });

    const handle = setTimeout(async () => {
      const collected: LeanSuggestion[] = [];
      const seen = new Set<string>();
      // Run discovery tactics in priority order; surface results as they arrive.
      for (const { kind, tactic } of DISCOVERY_TACTICS) {
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
          continue;
        }
        const data = await analyze(assembled, mathlib);
        if (cancelled || reqId !== reqRef.current) return;
        if (!data) continue;
        for (const s of suggestionsFromMessages(data.messages, kind)) {
          if (seen.has(s.tactic)) continue;
          seen.add(s.tactic);
          collected.push(s);
        }
        // Push incrementally so pills appear as each discovery tactic returns.
        setState({ suggestions: [...collected], loading: true });
      }
      if (!cancelled && reqId === reqRef.current) {
        setState({ suggestions: collected, loading: false });
      }
    }, 400);

    return () => {
      cancelled = true;
      clearTimeout(handle);
    };
  }, [source, declLine, nextDeclLine, proof, cursorId, cursorIsHole, mathlib, enabled]);

  return state;
}
