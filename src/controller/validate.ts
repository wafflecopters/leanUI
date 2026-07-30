/**
 * "Try before you suggest" — run each candidate tactic at the cursor's hole and
 * keep only the ones Lean actually accepts, along with a preview of what each
 * leaves behind.
 *
 * Framework-free and cancellable: the React hook, the REPL and the tests all
 * call the same function. A trial splices the candidate's PARSED tactic in
 * place of the cursor hole, analyzes, and keeps it iff Lean reports no error at
 * the spliced tactic's own line — errors elsewhere (the `by`-line "unsolved
 * goals", or unrelated failing tactics) don't count, because they're about the
 * rest of the proof, not this candidate.
 */
import { replaceNode, type ProofNode, type ProofNodeId } from '../proof-tree/proof-tree';
import { findFirstHole } from '../proof-tree/tactic-to-tree';
import { assembleProofInSource } from '../lean/assembleProofDecl';
import { leanTacticsToTree } from '../lean/leanTacticsToTree';
import { taggedText, subtermLatexAtPos } from '../lean/leanInteractiveGoal';
import { taggedToLatex } from '../lean/codeWithInfos';
import {
  orderedSubgoalTags,
  orderGoalsForDisplay,
  type LeanSuggestion,
} from '../lean/leanSuggestions';
import { mapPool, type LeanAnalyzer } from './analyzer';

/** A cooperative cancellation token: set `cancelled` and in-flight trials stop
 *  contributing results. */
export interface CancelToken {
  cancelled: boolean;
}

export interface ValidateInput {
  analyze: LeanAnalyzer;
  /** The full Lean file (the declaration's context). */
  source: string;
  /** 1-based line of the declaration being proved. */
  declLine: number;
  nextDeclLine?: number;
  proof: ProofNode;
  /** The hole each candidate is trialed at. */
  cursorId: ProofNodeId;
  candidates: readonly LeanSuggestion[];
  /** Lean `SubExpr.Pos` of the clicked subterm — its post-tactic form is the
   *  preview for rewrites (a smaller, more legible delta than the whole goal). */
  focusPos?: string | null;
  /** LaTeX of that subterm BEFORE the tactic; a preview only shows when the
   *  tactic actually changed it. */
  focusOriginal?: string | null;
  /** LaTeX of the whole target before the tactic; a tactic that leaves exactly
   *  this goal previews nothing rather than echoing the goal back. */
  goalOriginal?: string | null;
  mathlib?: boolean;
  /** Max concurrent trials. */
  concurrency?: number;
  cancel?: CancelToken;
  /** Called with the validated-so-far list each time one lands, in candidate
   *  order — so a UI can stream pills in as they arrive. */
  onProgress?: (partial: LeanSuggestion[]) => void;
}

/** A result whose goal is headed by a raw `match`/recursor didn't reduce to
 *  anything useful (e.g. `unfold mul` exposing the pattern-match body). */
const UNREDUCED = /\\operatorname\{match\}|\bmatch\b/;

const DEFAULT_CONCURRENCY = 3;

/**
 * Validate one candidate. Returns the enriched suggestion, or null when Lean
 * rejected it (or the trial couldn't be assembled/sent).
 */
export async function validateOne(
  cand: LeanSuggestion,
  input: ValidateInput,
): Promise<LeanSuggestion | null> {
  const { analyze, source, declLine, nextDeclLine, proof, cursorId, mathlib } = input;

  let sub: ProofNode;
  let assembled: ReturnType<typeof assembleProofInSource>;
  try {
    // Splice the PARSED tactic (so its remaining hole carries the post-tactic
    // goal we preview), not a raw text override.
    sub = leanTacticsToTree(cand.validateTactic ?? cand.tactic);
    // A tactic that parses to a bare hole is not a tactic: blank text and a
    // literal `sorry` both land here. Splicing one into the cursor hole is a
    // NO-OP, so the trial would validate the unchanged proof, read the
    // untouched goal back, and surface a pill that does nothing when clicked.
    if (sub.tag === 'hole') return null;
    assembled = assembleProofInSource({
      source,
      decl: { line: declLine },
      nextDeclLine,
      proof: replaceNode(proof, cursorId, sub),
    });
  } catch {
    return null;
  }

  const tacticLine = assembled.lean.nodeRanges.get(sub.id)?.startLine;
  const data = await analyze({
    source: assembled.source,
    prefix: assembled.prefixSource,
    body: assembled.bodySource,
    mathlib,
  });
  if (!data || tacticLine === undefined) return null;
  // A bridge failure (timeout, spawn error) is NOT a validation: with no
  // messages or goals the candidate would read as a spurious closer.
  if (data.bridgeError) return null;
  // Scoped to the tactic's OWN line, and that scoping is load-bearing — it's
  // what lets us offer Mathlib tactics on a file that may not have Mathlib.
  // Verified against core Lean: an unavailable tactic reports TWO errors, its
  // own `unknown tactic` here plus a knock-on `unsolved goals` back on the
  // declaration line. Widening this to "any error" would still drop the right
  // candidate, but for the wrong reason, and would start dropping tactics that
  // legitimately leave goals behind. Narrow is correct.
  if (data.messages.some((m) => m.severity === 'error' && m.startLine === tacticLine)) return null;

  const firstHole = findFirstHole(sub);
  let closes = false;
  let subgoals = 0;
  let subgoalTags: string[] | null = null;
  let previews: string[] = [];
  let postTarget;

  if (!firstHole) {
    // Terminal tactic (rfl/omega/exact …) with no continuation hole: it CLOSES
    // only if Lean reports no leftover "unsolved goals". A tactic that applies
    // but leaves subgoals reports them at the enclosing `by`, not at the tactic
    // line — so checking the tactic line alone would wrongly call it a closer.
    // (Every other hole is `sorry`, which absorbs its goal as a warning, so an
    // "unsolved goals" ERROR can only have come from this tactic.)
    closes = !data.messages.some((m) => m.severity === 'error' && /unsolved goals/i.test(m.text));
  } else {
    const range = assembled.lean.nodeRanges.get(firstHole.id);
    const g = range
      ? data.goals.find((x) => x.startLine === range.startLine && x.startCol === range.startCol)
      : undefined;
    closes = !g || g.goals.length === 0;
    postTarget = g?.goals?.[0]?.targetTagged;
    // The trial's lone `sorry` sees ALL remaining goals, so this is the
    // tactic's true subgoal count — e.g. 2 for `constructor` on DPair.
    subgoals = g?.goals.length ?? 0;
    if (g && g.goals.length > 1) {
      subgoalTags = orderedSubgoalTags(
        g.goals.map((gs) => ({ tag: gs.case, target: taggedText(gs.targetTagged) })),
      );
    }
    // Every goal the tactic leaves, in the order its branches will appear.
    if (g) {
      previews = orderGoalsForDisplay(g.goals, subgoalTags).map((gs) => taggedToLatex(gs.targetTagged));
    }
  }

  // Preview: how the FOCUSED subterm looks after the tactic (`b + c` → `c + b`).
  // Only for rewrites/unfold — induction and friends case-split rather than
  // transform the focus in place — and only when the focus actually changed.
  let preview = '';
  if (postTarget && input.focusPos && (cand.kind === 'rw' || cand.kind === 'unfold')) {
    const after = subtermLatexAtPos(postTarget, input.focusPos) ?? '';
    if (after && after !== (input.focusOriginal ?? '')) preview = after;
  }
  // A lone resulting goal identical to the current one isn't a preview — the
  // tactic changed nothing visible. Say nothing rather than echo the goal back.
  if (previews.length === 1 && previews[0] === (input.goalOriginal ?? '')) previews = [];
  if ([preview, ...previews].some((p) => UNREDUCED.test(p))) return null;

  return {
    ...cand,
    preview,
    ...(previews.length ? { previews } : {}),
    closes,
    ...(subgoals > 1 ? { subgoals } : {}),
    ...(subgoalTags ? { subgoalTags } : {}),
  };
}

/**
 * Validate every candidate, bounded-concurrently. Results keep the CALLER'S
 * candidate order (trial priority) regardless of which trial finishes first, so
 * the list a user sees is stable as it fills in.
 */
export async function validateSuggestions(input: ValidateInput): Promise<LeanSuggestion[]> {
  const { candidates, cancel, onProgress } = input;
  const rank = new Map(candidates.map((c, i) => [c.id, i] as const));
  const valid: LeanSuggestion[] = [];

  await mapPool(candidates, input.concurrency ?? DEFAULT_CONCURRENCY, async (cand) => {
    if (cancel?.cancelled) return;
    const result = await validateOne(cand, input);
    if (cancel?.cancelled || !result) return;
    valid.push(result);
    valid.sort((a, b) => (rank.get(a.id) ?? 0) - (rank.get(b.id) ?? 0));
    onProgress?.([...valid]);
  });

  return valid;
}

/**
 * Collapse validated suggestions to one pill per LABEL.
 *
 * The scoped `conv in (..) => rw [L]` and the whole-goal `rw [L]` share a label:
 * keep the scoped form's tactic (listed first, so it wins), but adopt the
 * whole-goal form's preview — `conv` hides its exit goal from Lean's InfoTree,
 * so only the whole-goal trial produces a usable one.
 */
export function dedupeByLabel(suggestions: readonly LeanSuggestion[]): LeanSuggestion[] {
  const byLabel = new Map<string, LeanSuggestion>();
  for (const s of suggestions) {
    const existing = byLabel.get(s.label);
    if (!existing) {
      byLabel.set(s.label, s);
    } else if (!existing.preview && s.preview) {
      byLabel.set(s.label, { ...existing, preview: s.preview });
    } else if (!existing.preview && !existing.previews?.length && s.previews?.length) {
      byLabel.set(s.label, { ...existing, previews: s.previews });
    }
  }
  return [...byLabel.values()];
}
