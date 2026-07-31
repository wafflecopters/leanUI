/**
 * Which tactics are WORTH TRYING at the cursor — the input to the "try before
 * you suggest" pipeline.
 *
 * This is pure: goal text + context + the file's declarations in, an ordered
 * candidate list out. No Lean, no React. Every candidate is trialed afterwards
 * (see `validate.ts`), so being generous here costs latency, not correctness —
 * but being WRONG here is invisible, because a candidate that is never
 * generated simply never appears and reads as "nothing applies".
 *
 * Order matters: it is trial priority, and results surface in it. Cheap,
 * high-value candidates go first.
 */
import type { LeanDeclaration } from '../lean/types';
import {
  applyCandidates,
  comparisonCandidates,
  equalityLemmas,
  valueCandidates,
  rankByGoalOverlap,
  unfoldableDefs,
} from '../lean/rewriteCandidates';
import {
  hypothesisSuggestions,
  targetedSuggestions,
  type LeanSuggestion,
} from '../lean/leanSuggestions';
import { projectionCandidates } from '../lean/termSlots';
import { introBinderNames } from '../lean/introBinders';

/** Probe binder for the slot builder. NOT `__`-prefixed: Lean's interactive
 *  goal display filters double-underscore names as internal, which would hide
 *  the probed term's type from us. */
export const PROBE_NAME = 'leanuiProbe';

export interface CandidateInput {
  /** Every declaration in the file (the lemma library). */
  declarations: readonly LeanDeclaration[];
  /** The declaration being proved — excluded from its own lemma candidates. */
  currentDeclName: string;
  /**
   * Plain text of the goal's TARGET. Must NOT be the whole goal state: the
   * hypothesis block's operators drown out the target's, and a context carrying
   * `limF : lim⟦x0⟧ f = L` makes a `0 < ε / 2` goal read as an equality —
   * filtering out every `<` lemma before it can be trialed.
   */
  goalText: string;
  /** Hypotheses in scope, with plain type text. */
  hypotheses: ReadonlyArray<{ name: string; type: string }>;
  /** Plain text of the clicked subterm; empty when nothing is selected. */
  selectedSubtermText?: string;
  /** Clicked hypothesis name, when the user selected one. */
  selectedHypName?: string | null;
  /**
   * True when the goal is a VALUE to choose (`⊢ ℝ` — a δ, a midpoint) rather
   * than a claim to prove. A different kind of move applies, so a different set
   * is offered: see `valueCandidates`.
   */
  isValueGoal?: boolean;
}

/** How many file rewrite lemmas to trial (each is a Lean round-trip). */
const REWRITE_CAP = 10;
/** How many `unfold <def>` candidates to trial when a subterm is selected.
 *  Generous, because the list is now definitions only (lemmas filtered out) and
 *  the one you need is often deep in the file: the constants behind a displayed
 *  literal — `2` is `rtwo` — are invisible in the goal text, so there is nothing
 *  to rank them by. Validation drops whatever doesn't fire. */
const UNFOLD_CAP = 60;

/**
 * Rewrite candidates: equality hypotheses first (the induction hypothesis is
 * almost always the one you want), then the file's equality lemmas ranked by
 * overlap with the focus. With a subterm selected we offer the SCOPED form
 * (`conv in (sub) => rw [L]`) ahead of the whole-goal form; both carry the same
 * label so dedup keeps the scoped one and adopts the whole-goal preview.
 */
function rewriteCandidates(input: CandidateInput): LeanSuggestion[] {
  const { declarations, currentDeclName, goalText, hypotheses } = input;
  const selected = input.selectedSubtermText ?? '';
  const scopeText = selected || goalText;
  const hypEqNames = hypotheses.filter((h) => /\s=\s/.test(h.type)).map((h) => h.name);
  const fileLemmas = rankByGoalOverlap(
    equalityLemmas(declarations, currentDeclName),
    scopeText,
    REWRITE_CAP,
  ).map((c) => c.name);

  const out: LeanSuggestion[] = [];
  for (const name of [...hypEqNames, ...fileLemmas]) {
    if (selected) {
      out.push({
        id: `lean-convrw:${name}`,
        label: `rw [${name}]`,
        tactic: `conv in (${selected}) => rw [${name}]`,
        kind: 'rw',
      });
    }
    out.push({ id: `lean-rw:${name}`, label: `rw [${name}]`, tactic: `rw [${name}]`, kind: 'rw' });
  }
  return out;
}

/**
 * A clicked hypothesis contributes its own use-actions: close with it, apply it
 * backwards, destructure it, or USE one of its projections (TT's "Use <field>").
 */
function hypothesisCandidates(input: CandidateInput): LeanSuggestion[] {
  const hyp = input.selectedHypName;
  if (!hyp) return [];
  const out = hypothesisSuggestions(hyp);
  const hypType = input.hypotheses.find((h) => h.name === hyp)?.type ?? '';
  for (const expr of projectionCandidates(hyp, hypType, input.declarations)) {
    // The trial is a `have <probe> := <expr>` — it type-checks the projection
    // without committing to it. Clicking opens the slot builder.
    out.push({
      id: `hyp-use:${expr}`,
      label: `use ${expr}`,
      tactic: `have ${PROBE_NAME} := ${expr}`,
      kind: 'apply',
    });
  }
  return out;
}

/**
 * Whole-goal solvers, offered on every goal and cheapest-first.
 *
 * These are the reason the editor works for BOTH kinds of user without knowing
 * which one it has. The list deliberately spans core Lean (`rfl`, `trivial`,
 * `decide`, `omega`) and Mathlib (`norm_num`, `positivity`, `linarith`, `ring`,
 * `nlinarith`) — and nothing anywhere asks which is loaded.
 *
 * It doesn't need to ask, because every candidate is TRIALED before it is
 * shown: an unavailable tactic is an unknown identifier at its own line, so
 * validation drops it exactly the way it drops a lemma that fails to apply. In
 * a from-scratch axiomatisation the Mathlib half silently disappears and the
 * file's own lemmas carry the proof; with Mathlib imported these close in one
 * move what would otherwise be a lemma hunt (`0 < ε / 2` is `positivity`).
 *
 * So capability is DISCOVERED, never declared. Adding a tactic here costs one
 * failed trial where it doesn't exist, and adding a whole new library costs
 * nothing at all — which is what keeps the two audiences on one code path.
 */
export const SOLVER_TACTICS: readonly string[] = [
  'rfl',
  'trivial',
  'decide',
  'omega',
  'norm_num',
  'positivity',
  'linarith',
  'ring',
  'nlinarith',
];

/**
 * The full candidate list for the cursor, in trial-priority order and deduped
 * by id.
 *
 * Priority rationale: hypothesis actions and the subterm/goal heuristics are
 * few and directly requested by the user's click; `assumption` and
 * `constructor` are single cheap trials with high hit rates (`constructor` is
 * the way INTO every structure goal); apply-lemmas are the goal-shaped library
 * hits; the rewrite/unfold batches are the long tail; the `simp [everything]`
 * ring probe is one expensive trial, so it goes last.
 */
export function tacticCandidates(input: CandidateInput): LeanSuggestion[] {
  const { declarations, currentDeclName, goalText } = input;
  const selected = input.selectedSubtermText ?? '';

  // A value goal is a blank to fill, not a claim to prove. Offer the values —
  // and ONLY those: `omega`, `trivial` and `assumption` all "succeed" on `⊢ ℝ`
  // by picking something arbitrary, which is worse than no suggestion, because
  // the proof then contains a choice nobody made.
  if (input.isValueGoal) {
    const values = valueCandidates(declarations, goalText, input.hypotheses, currentDeclName);
    // Only when there IS something to choose. With nothing of that type in
    // scope the list would be empty, and an empty list reads as "nothing
    // applies" — so fall through to the ordinary candidates rather than leave
    // the user with no moves at all.
    if (values.length > 0) {
      return values.map((expr) => ({
        id: `lean-value:${expr}`,
        label: `use ${expr}`,
        tactic: `exact ${expr}`,
        kind: 'exact' as const,
      }));
    }
  }

  const heuristics: LeanSuggestion[] = [
    ...(selected ? targetedSuggestions(selected) : []),
    ...(goalText ? targetedSuggestions(goalText) : []),
  ];

  // "Compute": reduce the clicked subterm to normal form via plain `simp` —
  // the file's own @[simp] rules. This is the protocol that keeps domain
  // knowledge out of the engine: the preset tags what counts as computation
  // (literal bridges, `2 + -1 = 1`), the engine only offers the move; with
  // Mathlib loaded the default simp set plays the same role. Two forms share
  // one label: the scoped `conv` answers the user's click directly, but its
  // pattern is syntactic and misses goals whose displayed literal is a
  // constant underneath (`2` printed by an unexpander for `rtwo R`) — the
  // whole-goal twin still fires there, and dedupeByLabel keeps one pill.
  const compute: LeanSuggestion[] = selected
    ? [
        {
          id: 'lean-compute-conv',
          label: 'Compute',
          tactic: `conv in (${selected}) => simp`,
          kind: 'rw',
        },
        { id: 'lean-compute', label: 'Compute', tactic: 'simp', kind: 'rw' },
      ]
    : [];

  // A goal that starts with binders can't be worked on until they're
  // introduced, and naming them by hand is the first chore of every ε-δ proof.
  // Offered as ONE move that takes the whole telescope, with names derived from
  // the goal (see introBinderNames).
  const introNames = introBinderNames(goalText, input.hypotheses.map((h) => h.name));
  const intros: LeanSuggestion[] = introNames.length
    ? [
        {
          id: `lean-intros:${introNames.join(' ')}`,
          label: `intro ${introNames.join(' ')}`,
          tactic: `intro ${introNames.join(' ')}`,
          kind: 'apply',
        },
      ]
    : [];

  // "Compare these two" — split on how two values in scope relate. The move you
  // reach for when a proof has produced two of something (two deltas) and needs
  // one. Most-recent pair first; see comparisonCandidates.
  const comparisons: LeanSuggestion[] = comparisonCandidates(
    declarations,
    input.hypotheses,
    currentDeclName,
  ).map(({ lemma, left, right }) => ({
    id: `lean-compare:${lemma}:${left}:${right}`,
    label: `compare ${left} and ${right}`,
    tactic: `cases ${lemma} ${left} ${right}`,
    kind: 'apply' as const,
  }));

  const assumption: LeanSuggestion[] = [
    { id: 'lean-assumption', label: 'assumption', tactic: 'assumption', kind: 'exact' },
  ];
  const solvers: LeanSuggestion[] = SOLVER_TACTICS.map((tactic) => ({
    id: `lean-solver:${tactic}`,
    label: tactic,
    tactic,
    kind: 'exact' as const,
  }));
  const constructor: LeanSuggestion[] = [
    { id: 'lean-constructor', label: 'constructor', tactic: 'constructor', kind: 'apply' },
  ];

  const applyLemmas: LeanSuggestion[] = applyCandidates(declarations, goalText, currentDeclName).map(
    (name) => ({
      id: `lean-applylemma:${name}`,
      label: `apply ${name}`,
      tactic: `apply ${name}`,
      kind: 'apply' as const,
    }),
  );

  // `unfold` is offered only on a selection: it's a big batch of trials and,
  // unfocused, it clutters the default view.
  const unfolds: LeanSuggestion[] = selected
    ? unfoldableDefs(declarations, currentDeclName, UNFOLD_CAP).map((name) => ({
        id: `lean-unfold:${name}`,
        label: `unfold ${name}`,
        tactic: `unfold ${name}`,
        kind: 'unfold' as const,
      }))
    : [];

  // A poor-man's ring solver: `simp` with all the file's equality lemmas.
  // Validated, so it only shows when it actually closes the goal.
  const ringLemmas = equalityLemmas(declarations, currentDeclName).map((c) => c.name);
  const ring: LeanSuggestion[] = ringLemmas.length
    ? [
        {
          id: 'lean-simp-ring',
          label: 'simp [ring lemmas]',
          tactic: `simp [${ringLemmas.join(', ')}]`,
          kind: 'simp',
        },
      ]
    : [];

  const ordered = [
    ...hypothesisCandidates(input),
    ...heuristics,
    // Right after the click-driven heuristics: a selected subterm's most
    // common want is "what is this, reduced".
    ...compute,
    // Before anything else: when the goal is still wrapped in binders, opening
    // them is almost always the move, and nothing else can apply until it is.
    ...intros,
    ...assumption,
    // Before the lemma searches: when the proof has two of something and needs
    // one, comparing them is the structural move, and no lemma in the file is
    // shaped like the goal it leaves.
    ...comparisons,
    // "Close it outright" before "open it up": a solver that discharges the
    // goal beats `constructor`, which only splits it into more work.
    ...solvers,
    ...constructor,
    ...applyLemmas,
    ...rewriteCandidates(input),
    ...unfolds,
    ...ring,
  ];

  // Deduped by tactic as well as id: the same move reached two ways (a goal-shape
  // heuristic offering `rfl`, and `rfl` as a blanket solver) is one pill.
  const seen = new Set<string>();
  return ordered.filter((s) =>
    seen.has(s.id) || seen.has(`t:${s.tactic}`)
      ? false
      : (seen.add(s.id), seen.add(`t:${s.tactic}`), true),
  );
}
