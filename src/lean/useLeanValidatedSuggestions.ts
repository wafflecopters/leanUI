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
import { analyzeRequest } from './analyzeClient';
import { assembleProofInSource } from './assembleProofDecl';
import { leanTacticsToTree } from './leanTacticsToTree';
import { subtermLatexAtPos, taggedText } from './leanInteractiveGoal';
import { taggedToLatex } from './codeWithInfos';
import { orderedSubgoalTags, type LeanSuggestion } from './leanSuggestions';

export interface UseLeanValidatedSuggestionsArgs {
  source: string;
  declLine: number;
  nextDeclLine?: number;
  proof: ProofNode;
  cursorId: ProofNodeId;
  cursorIsHole: boolean;
  /** Candidate suggestions to validate (already ordered by the caller). */
  candidates: readonly LeanSuggestion[];
  /** Lean SubExpr.Pos of the FOCUSED subterm, if any — its post-tactic form is
   *  the suggestion's preview (e.g. `b + c` → `c + b`). */
  focusPos?: string | null;
  /** LaTeX of the focused subterm BEFORE any tactic — a preview is only shown
   *  when the tactic actually changes it. */
  focusOriginal?: string | null;
  mathlib?: boolean;
  enabled?: boolean;
}

const EMPTY = { suggestions: [] as LeanSuggestion[], loading: false };

// Trials are BACKGROUND requests: throttled client-side so they never exhaust
// the browser's per-origin connection pool and starve the goal refresh.
function analyze(
  assembled: { source: string; prefixSource?: string; bodySource?: string },
  mathlib?: boolean,
): Promise<AnalyzeResult | null> {
  return analyzeRequest(
    { source: assembled.source, prefix: assembled.prefixSource, body: assembled.bodySource, mathlib },
    { background: true },
  );
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
  const { source, declLine, nextDeclLine, proof, cursorId, cursorIsHole, candidates, focusPos, focusOriginal, mathlib, enabled = true } = args;
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
      await mapPool(candidates, 3, async (cand) => {
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
        const data = await analyze(assembled, mathlib);
        if (cancelled || reqId !== reqRef.current || !data || tacticLine === undefined) return;
        // A bridge failure (timeout, spawn error) is NOT a validation: with no
        // messages/goals the candidate would read as a spurious closer. Skip it.
        if (data.bridgeError) return;
        // Valid iff no error AT the candidate's own line (errors elsewhere — the
        // `by`-line "unsolved goals", or unrelated failing tactics — don't count).
        const failsHere = data.messages.some((m) => m.severity === 'error' && m.startLine === tacticLine);
        if (failsHere) return;
        const firstHole = findFirstHole(sub);
        // Does it close the goal? A terminal tactic (no remaining hole) that
        // validated closed it; otherwise it closed iff no open goal remains at
        // the tactic's first hole.
        let closes = false;
        let postTarget;
        let subgoals = 0;
        let subgoalTags: string[] | null = null;
        if (!firstHole) {
          // Terminal tactic (rfl/omega/constructor/exact …) with no continuation
          // hole: it CLOSES only if Lean reports no leftover "unsolved goals". A
          // tactic that applies but leaves subgoals (e.g. `constructor` on a
          // multi-premise constructor) reports them at the enclosing `by`, not at
          // the tactic line — so checking the tactic line alone would wrongly call
          // it a closer. (All other holes are `sorry`, which absorb their goals as
          // warnings, so an "unsolved goals" ERROR can only come from this tactic.)
          closes = !data.messages.some((m) => m.severity === 'error' && /unsolved goals/i.test(m.text));
        } else {
          const range = assembled.lean.nodeRanges.get(firstHole.id);
          const g = range ? data.goals.find((x) => x.startLine === range.startLine && x.startCol === range.startCol) : undefined;
          closes = !g || g.goals.length === 0;
          postTarget = g?.goals?.[0]?.targetTagged;
          // The trial's lone `sorry` sees ALL remaining goals (goalsBefore), so
          // this is the tactic's true subgoal count — e.g. 2 for `constructor`
          // on DPair (body + witness). Carried on the suggestion so applying it
          // opens that many child holes.
          subgoals = g?.goals.length ?? 0;
          // Tags in DISPLAY order (witness before dependent body) — applying
          // then prints `case <tag> =>` blocks in that order.
          if (g && g.goals.length > 1) {
            subgoalTags = orderedSubgoalTags(
              g.goals.map((gs) => ({ tag: gs.case, target: taggedText(gs.targetTagged) })),
            );
          }
        }
        // Preview: how the FOCUSED subterm looks after the tactic (e.g.
        // `b + c` → `c + b`). Only for rewrites/unfold (induction etc. case-split
        // rather than transform the focus in place), and only when it actually
        // changed the focus (so `unfold plus` on `n` doesn't preview `n`).
        let preview = '';
        if (postTarget && focusPos && (cand.kind === 'rw' || cand.kind === 'unfold')) {
          const after = subtermLatexAtPos(postTarget, focusPos) ?? '';
          if (after && after !== (focusOriginal ?? '')) preview = after;
        }
        // `constructor` transforms the WHOLE goal (opens the structure's field)
        // — its preview is the resulting goal itself, so the pill shows what
        // you'd be proving next (e.g. the ε-δ obligation) instead of nothing.
        if (!preview && cand.id === 'lean-constructor' && postTarget) {
          preview = taggedToLatex(postTarget);
        }
        // Drop suggestions whose result is headed by a raw `match`/recursor — it
        // didn't reduce to anything useful (e.g. `unfold mul` exposing the
        // pattern-match body).
        if (/\\operatorname\{match\}|\bmatch\b/.test(preview)) return;
        valid.push({ ...cand, preview, closes, ...(subgoals > 1 ? { subgoals } : {}), ...(subgoalTags ? { subgoalTags } : {}) });
        // Preserve the caller's candidate order as results stream in.
        valid.sort((a, b) => candidates.findIndex((c) => c.id === a.id) - candidates.findIndex((c) => c.id === b.id));
        setState({ suggestions: [...valid], loading: true });
      });
      if (!cancelled && reqId === reqRef.current) setState({ suggestions: valid, loading: false });
    }, 250);

    return () => {
      cancelled = true;
      clearTimeout(handle);
    };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [source, declLine, nextDeclLine, proof, cursorId, cursorIsHole, candKey, mathlib, enabled]);

  return state;
}
