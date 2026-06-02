import { useEffect, useRef, useState } from 'react';
import type { ProofNode, ProofNodeId } from '../proof-tree/proof-tree';
import type { NodeGoalInfo, TypedProofContext } from '../proof-tree/goal-computation';
import type { AnalyzeResult } from './types';
import { assembleProofDecl } from './assembleProofDecl';
import { mapLeanGoalsToNodes } from './leanGoalMapping';

/**
 * Compute a proof tree's goal state from Lean (the async provider for the
 * dependency-injection seam in ProofTreeEditor).
 *
 * Flow: proof tree → `assembleProofDecl` (theorem … := by <block>) → POST
 * /api/analyze → `mapLeanGoalsToNodes` → { goalMap, cursor context }. The result
 * is fed to ProofTreeEditor as `goalMapOverride` / `typedContextOverride`, so the
 * REAL editor renders entirely off Lean-computed goals. Debounced; stale
 * responses are discarded.
 */
export interface LeanProofGoals {
  goalMap: Map<ProofNodeId, NodeGoalInfo>;
  typedContext: TypedProofContext | null;
  loading: boolean;
  error?: string;
}

export interface UseLeanProofGoalsArgs {
  name?: string;
  /** The declaration type as Lean source (no signature binders). */
  typeSource?: string;
  proof: ProofNode;
  cursorId: ProofNodeId;
  preamble?: string[];
  mathlib?: boolean;
  /** Disable the round-trip (e.g. when typeSource is unavailable). */
  enabled?: boolean;
}

const EMPTY: LeanProofGoals = { goalMap: new Map(), typedContext: null, loading: false };

export function useLeanProofGoals(args: UseLeanProofGoalsArgs): LeanProofGoals {
  const { name, typeSource, proof, cursorId, preamble, mathlib, enabled = true } = args;
  const [state, setState] = useState<LeanProofGoals>(EMPTY);
  // Monotonic request id so out-of-order responses are ignored.
  const reqRef = useRef(0);

  useEffect(() => {
    if (!enabled || !typeSource) {
      setState(EMPTY);
      return;
    }
    const reqId = ++reqRef.current;
    let cancelled = false;
    setState((s) => ({ ...s, loading: true, error: undefined }));

    const handle = setTimeout(async () => {
      let assembled;
      try {
        assembled = assembleProofDecl({ name, typeSource, proof, preamble });
      } catch (e) {
        if (!cancelled && reqId === reqRef.current) {
          setState({ goalMap: new Map(), typedContext: null, loading: false, error: String(e) });
        }
        return;
      }
      try {
        const resp = await fetch('/api/analyze', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({ source: assembled.source, mathlib }),
        });
        const data: AnalyzeResult = await resp.json();
        if (cancelled || reqId !== reqRef.current) return;

        const goalMap = mapLeanGoalsToNodes({
          nodeRanges: assembled.lean.nodeRanges,
          holeNodeIds: assembled.lean.holeNodeIds,
          goals: data.goals,
          messages: data.messages,
        });
        const cursorInfo = goalMap.get(cursorId);
        const typedContext: TypedProofContext | null = cursorInfo
          ? {
              hypotheses: cursorInfo.hypotheses,
              goal: cursorInfo.goalLatex,
              ...(cursorInfo.caseLabelLatex ? { caseLabelLatex: cursorInfo.caseLabelLatex } : {}),
              ...(cursorInfo.validation ? { validation: cursorInfo.validation } : {}),
            }
          : null;

        setState({
          goalMap,
          typedContext,
          loading: false,
          ...(data.bridgeError ? { error: data.bridgeError } : {}),
        });
      } catch (e) {
        if (!cancelled && reqId === reqRef.current) {
          setState({
            goalMap: new Map(),
            typedContext: null,
            loading: false,
            error: `Request failed: ${e instanceof Error ? e.message : String(e)}`,
          });
        }
      }
    }, 350);

    return () => {
      cancelled = true;
      clearTimeout(handle);
    };
  }, [name, typeSource, proof, cursorId, preamble, mathlib, enabled]);

  return state;
}
