/**
 * The shape of a suggestion offered at a goal.
 *
 * These types outlived the TT suggestion engine they were born in: the engine
 * ranked and trialled candidates against the in-process TT kernel, which M5
 * deleted, but the DATA a suggestion carries is backend-agnostic. The Lean
 * backend produces the same records from real `exact?`/`rw?`/validated-trial
 * round-trips (see `src/controller/candidates.ts` and `validate.ts`), and the
 * proof-tree view renders them without knowing which engine filled them in.
 */
import type { TacticCommand } from './tactic-command';

export interface TacticSuggestion {
  readonly id: string;
  readonly label: string;
  /** Optional LaTeX version of the label for rich rendering. */
  readonly labelLatex?: string;
  readonly description: string;
  /** For intro tactics: proposed variable names (editable by user). */
  readonly proposedNames?: readonly string[];
  /** For unfold tactics: which occurrence (1-based) of the head to unfold. */
  readonly unfoldOccurrence?: number;
  /** For fold tactics: which occurrence (1-based) of the definition body to fold. */
  readonly foldOccurrence?: number;
  /** For fold tactics: the definition name to fold. */
  readonly foldName?: string;
  /** LaTeX preview of the goal after this tactic is applied. */
  readonly resultGoalLatex?: string;
  /** For apply tactics: number of subgoals created. */
  readonly numSubgoals?: number;
  /** For construct suggestions: the constructor name to apply. */
  readonly applyCtorName?: string;
  /** Optional source-aligned tactic commands that directly implement this suggestion. */
  readonly tacticCommands?: readonly TacticCommand[];
  /** For apply suggestions: LaTeX preview of each subgoal created. */
  readonly subgoalPreviews?: readonly string[];
}

/** A suggestion that rewrites with a named equation. */
export interface RewriteSuggestion extends TacticSuggestion {
  readonly rewriteName: string;
  readonly reverse: boolean;
  readonly occurrences: readonly number[];
  /** Head constant name of the clicked subterm (for occurrence-targeted rewrites). */
  readonly targetHead?: string;
}

/** Progress of an incremental rewrite-candidate search. */
export interface RewriteProgress {
  readonly checked: number;
  readonly total: number;
  readonly suggestions: readonly RewriteSuggestion[];
  readonly done: boolean;
}
