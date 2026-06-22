/**
 * Validate candidate tactic suggestions against Lean BEFORE showing them — the
 * "try before you suggest" behaviour — AND capture a preview of the goal each
 * one produces.
 *
 * For each candidate we splice its parsed tactic in place of the cursor hole,
 * analyze, and keep it iff Lean reports NO error at the spliced tactic's line (a
 * genuine failure — type mismatch, "did not find occurrence", unknown
 * identifier — lands there; a tactic that applies but leaves work does not).
 * The resulting goal at the tactic's first remaining hole becomes the pill's
 * `preview` (rendered LaTeX), so the UI can show what the tactic transforms the
 * goal into — like the TT/TTK editor.
 *
 * Trials run with bounded concurrency and surface incrementally.
 */
import { useEffect, useRef, useState } from 'react';
import { type ProofNode, type ProofNodeId, replaceNode } from '../proof-tree/proof-tree';
import { findFirstHole } from '../proof-tree/tactic-to-tree';
import type { AnalyzeResult } from './types';
import { assembleProofInSource } from './assembleProofDecl';
import { leanTacticsToTree } from './leanTacticsToTree';
import { mapLeanGoalsToNodes } from './leanGoalMapping';
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
        let sub;
        try {
          // Splice the PARSED tactic (so its remaining hole carries the
          // post-tactic goal we preview), not a raw override.
          sub = leanTacticsToTree(cand.tactic);
          const applied = replaceNode(proof, cursorId, sub);
          assembled = assembleProofInSource({ source, decl: { line: declLine }, nextDeclLine, proof: applied });
        } catch {
          return;
        }
        const tacticLine = assembled.lean.nodeRanges.get(sub.id)?.startLine;
        const data = await analyze(assembled.source, mathlib);
        if (cancelled || reqId !== reqRef.current || !data || tacticLine === undefined) return;
        // Valid iff no error AT the candidate's own line (errors elsewhere — the
        // `by`-line "unsolved goals", or unrelated failing tactics — don't count).
        const failsHere = data.messages.some((m) => m.severity === 'error' && m.startLine === tacticLine);
        if (failsHere) return;
        // Preview: the goal at the tactic's first remaining hole (empty if it
        // closes the goal). Rendered to LaTeX by mapLeanGoalsToNodes.
        let preview = '';
        const firstHole = findFirstHole(sub);
        if (firstHole) {
          const goalMap = mapLeanGoalsToNodes({
            nodeRanges: assembled.lean.nodeRanges,
            holeNodeIds: assembled.lean.holeNodeIds,
            goals: data.goals,
            messages: data.messages,
          });
          preview = goalMap.get(firstHole.id)?.goalLatex ?? '';
        }
        valid.push({ ...cand, preview });
        // Preserve the caller's candidate order as results stream in.
        valid.sort((a, b) => candidates.findIndex((c) => c.id === a.id) - candidates.findIndex((c) => c.id === b.id));
        setState({ suggestions: [...valid], loading: true });
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
