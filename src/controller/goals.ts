/**
 * One goal round-trip: proof tree → Lean source → Lean's goal at every step.
 *
 * Framework-free, so the React hook, the session, the REPL and the tests all
 * get identical answers. Splice the printed proof into the REAL declaration in
 * the full source (so its type's dependencies — earlier defs — are in scope),
 * analyze, and map Lean's range-keyed goal states back onto proof node ids.
 */
import type { ProofNode, ProofNodeId } from '../proof-tree/proof-tree';
import type { NodeGoalInfo, TypedProofContext } from '../proof-tree/goal-types';
import type { LeanGoal, LeanGoalState, LeanMessage } from '../lean/types';
import { assembleProofInSource } from '../lean/assembleProofDecl';
import { collectBranchTags, mapLeanGoalsToNodes } from '../lean/leanGoalMapping';
import { mathTextToLatex } from '../lean/codeWithInfos';
import { taggedText } from '../lean/leanInteractiveGoal';
import type { LeanAnalyzer } from './analyzer';

export interface GoalRoundTripInput {
  analyze: LeanAnalyzer;
  /** The full Lean source file. */
  source: string;
  /** 1-based start line of the declaration being proved. */
  declLine: number;
  nextDeclLine?: number;
  proof: ProofNode;
  cursorId: ProofNodeId;
  mathlib?: boolean;
}

export interface GoalRoundTrip {
  goalMap: Map<ProofNodeId, NodeGoalInfo>;
  /** Source lines of FABRICATED continuation holes in the analyzed assembly —
   *  where the printer's own `sorry` placeholders sit. */
  holeLines?: ReadonlySet<number>;
  typedContext: TypedProofContext | null;
  /** The cursor node's full Lean goal state, or null when nothing is open there. */
  cursorGoal: LeanGoalState | null;
  /** Plain-text target per node — what a test or a REPL reads. */
  goalTexts: Map<ProofNodeId, string>;
  /** Lean's full goal state per node. Keeping ALL of them (not just the
   *  cursor's) means the cursor can move without another round-trip — which is
   *  what post-refresh normalizations like branch reordering need. */
  goalStates: Map<ProofNodeId, LeanGoalState>;
  messages: LeanMessage[];
  /** Set when the round-trip itself failed (assembly, transport, bridge). */
  error?: string;
}

const FAILED = (error: string): GoalRoundTrip => ({
  goalMap: new Map(),
  typedContext: null,
  cursorGoal: null,
  goalTexts: new Map(),
  goalStates: new Map(),
  messages: [],
  error,
});

/** Direct child proof nodes of any node tag. */
function childNodes(n: ProofNode): ProofNode[] {
  const out: ProofNode[] = [];
  const rec = n as unknown as Record<string, unknown>;
  for (const k of ['child', 'byProof', 'proofTree'] as const) {
    const v = rec[k];
    if (v && typeof v === 'object' && 'tag' in v) out.push(v as ProofNode);
  }
  for (const k of ['children', 'steps'] as const) {
    const v = rec[k];
    if (Array.isArray(v)) out.push(...(v as ProofNode[]));
  }
  if (n.tag === 'induction') for (const c of n.cases) out.push(c.body);
  return out;
}

/**
 * Render each have/exact node's EXPRESSION as math into the goal map — the
 * affordance the term builder hangs on: the have shows "since ⟨math⟩", and
 * clicking the math opens the builder. `?_` term-holes render as □.
 */
function addProofExprLatex(node: ProofNode, goalMap: Map<ProofNodeId, NodeGoalInfo>): void {
  if ((node.tag === 'have' && !node.proofTree) || node.tag === 'exact') {
    const expr = (node as { expr: string }).expr.trim();
    if (expr && expr !== '?') {
      const existing = goalMap.get(node.id) ?? { goalLatex: '', hypotheses: [] };
      if (!existing.proofExprLatex) {
        goalMap.set(node.id, {
          ...existing,
          proofExprLatex: mathTextToLatex(
            expr.replace(/\?_/g, '\\square').replace(/\?(?![a-zA-Z_])/g, '\\square'),
          ),
        });
      }
    }
  }
  for (const child of childNodes(node)) addProofExprLatex(child, goalMap);
}

/**
 * Demote "solved" holes that are only reachable through a FAILED tactic.
 *
 * Lean reports no goal at such a hole because the proof broke upstream, not
 * because it was discharged — and "Goal solved" is exactly the wrong thing to
 * tell someone whose proof is broken.
 */
function unsolveAfterErrors(
  node: ProofNode,
  goalMap: Map<ProofNodeId, NodeGoalInfo>,
  blocked: boolean,
): void {
  const info = goalMap.get(node.id);
  if (node.tag === 'hole' && blocked && info?.validation?.status === 'solved') {
    goalMap.set(node.id, {
      goalLatex: '',
      hypotheses: info.hypotheses ?? [],
      validation: { status: 'error', message: 'a previous step failed' },
    });
  }
  const blockedBelow = blocked || !!info?.tacticError;
  for (const child of childNodes(node)) unsolveAfterErrors(child, goalMap, blockedBelow);
}

export async function goalRoundTrip(input: GoalRoundTripInput): Promise<GoalRoundTrip> {
  const { analyze, source, declLine, nextDeclLine, proof, cursorId, mathlib } = input;

  let assembled;
  try {
    assembled = assembleProofInSource({ source, decl: { line: declLine }, nextDeclLine, proof });
  } catch (e) {
    return FAILED(`could not assemble the proof: ${e instanceof Error ? e.message : String(e)}`);
  }

  const data = await analyze({
    source: assembled.source,
    prefix: assembled.prefixSource,
    body: assembled.bodySource,
    mathlib,
    // The VISIBLE goal state — never queued behind background trials.
    priority: true,
  });
  if (!data) return FAILED('analyze request failed');

  const goalMap = mapLeanGoalsToNodes({
    nodeRanges: assembled.lean.nodeRanges,
    holeNodeIds: assembled.lean.holeNodeIds,
    goals: data.goals,
    messages: data.messages,
    // Lean clears a goal's case tag once its `case` block focuses it, so the
    // tree is what remembers which branch each node proves.
    branchTags: collectBranchTags(proof),
  });
  unsolveAfterErrors(proof, goalMap, false);
  addProofExprLatex(proof, goalMap);

  // Goal state (and its readable form) node by node.
  const goalTexts = new Map<ProofNodeId, string>();
  const goalStates = new Map<ProofNodeId, LeanGoalState>();
  for (const [nodeId, range] of assembled.lean.nodeRanges) {
    const g = data.goals.find(
      (x: LeanGoal) => x.startLine === range.startLine && x.startCol === range.startCol,
    );
    const first = g?.goals[0];
    if (first) {
      goalStates.set(nodeId, first);
      goalTexts.set(nodeId, taggedText(first.targetTagged));
    }
  }

  const cursorInfo = goalMap.get(cursorId);
  const typedContext: TypedProofContext | null = cursorInfo
    ? {
        hypotheses: cursorInfo.hypotheses,
        goal: cursorInfo.goalLatex,
        ...(cursorInfo.caseLabelLatex ? { caseLabelLatex: cursorInfo.caseLabelLatex } : {}),
        ...(cursorInfo.validation ? { validation: cursorInfo.validation } : {}),
      }
    : null;

  const holeLines = new Set<number>();
  for (const id of assembled.lean.holeNodeIds) {
    const r = assembled.lean.nodeRanges.get(id);
    if (r) holeLines.add(r.startLine);
  }
  return {
    goalMap,
    holeLines,
    typedContext,
    cursorGoal: goalStates.get(cursorId) ?? null,
    goalTexts,
    goalStates,
    messages: data.messages,
    ...(data.bridgeError ? { error: data.bridgeError } : {}),
  };
}
