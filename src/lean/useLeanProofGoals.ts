import { useEffect, useRef, useState } from 'react';
import type { ProofNode, ProofNodeId } from '../proof-tree/proof-tree';
import type { NodeGoalInfo, TypedProofContext } from '../proof-tree/goal-computation';
import type { AnalyzeResult, LeanGoal, LeanGoalState } from './types';
import { assembleProofInSource } from './assembleProofDecl';
import { mapLeanGoalsToNodes } from './leanGoalMapping';

/**
 * Compute a proof tree's goal state from Lean (the async provider for the
 * dependency-injection seam in ProofTreeEditor).
 *
 * Flow: splice the printed proof into the REAL declaration in the full source
 * (so its type's dependencies — earlier defs — are in scope), POST /api/analyze
 * on the whole file → `mapLeanGoalsToNodes` → { goalMap, cursor context }. Fed to
 * ProofTreeEditor as `goalMapOverride` / `typedContextOverride`. Debounced; stale
 * responses discarded.
 */
export interface LeanProofGoals {
  goalMap: Map<ProofNodeId, NodeGoalInfo>;
  typedContext: TypedProofContext | null;
  /** The cursor node's full Lean goal state (tagged target + hyps), for the
   *  interactive clickable-subterm goal view. Null when no open goal there. */
  cursorGoal: LeanGoalState | null;
  loading: boolean;
  error?: string;
}

export interface UseLeanProofGoalsArgs {
  /** The full Lean source file (provides the declaration's context). */
  source: string;
  /** The declaration being proved (its 1-based start line). */
  declLine: number;
  /** Start line of the next declaration, bounding this decl's region. */
  nextDeclLine?: number;
  proof: ProofNode;
  cursorId: ProofNodeId;
  mathlib?: boolean;
  /** Disable the round-trip. */
  enabled?: boolean;
}

const EMPTY: LeanProofGoals = { goalMap: new Map(), typedContext: null, cursorGoal: null, loading: false };

export function useLeanProofGoals(args: UseLeanProofGoalsArgs): LeanProofGoals {
  const { source, declLine, nextDeclLine, proof, cursorId, mathlib, enabled = true } = args;
  const [state, setState] = useState<LeanProofGoals>(EMPTY);
  // Monotonic request id so out-of-order responses are ignored.
  const reqRef = useRef(0);

  useEffect(() => {
    if (!enabled || !source) {
      setState(EMPTY);
      return;
    }
    const reqId = ++reqRef.current;
    let cancelled = false;
    setState((s) => ({ ...s, loading: true, error: undefined }));

    const handle = setTimeout(async () => {
      let assembled;
      try {
        assembled = assembleProofInSource({ source, decl: { line: declLine }, nextDeclLine, proof });
      } catch (e) {
        if (!cancelled && reqId === reqRef.current) {
          setState({ goalMap: new Map(), typedContext: null, cursorGoal: null, loading: false, error: String(e) });
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

        // The cursor node's full Lean goal state (tagged target) for the
        // interactive clickable-subterm goal view.
        const cursorRange = assembled.lean.nodeRanges.get(cursorId);
        let cursorGoal: LeanGoalState | null = null;
        if (cursorRange) {
          const g: LeanGoal | undefined = data.goals.find(
            (x) => x.startLine === cursorRange.startLine && x.startCol === cursorRange.startCol,
          );
          cursorGoal = g && g.goals.length > 0 ? g.goals[0] : null;
        }

        setState({
          goalMap,
          typedContext,
          cursorGoal,
          loading: false,
          ...(data.bridgeError ? { error: data.bridgeError } : {}),
        });
      } catch (e) {
        if (!cancelled && reqId === reqRef.current) {
          setState({
            goalMap: new Map(),
            typedContext: null,
            cursorGoal: null,
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
  }, [source, declLine, nextDeclLine, proof, cursorId, mathlib, enabled]);

  return state;
}
