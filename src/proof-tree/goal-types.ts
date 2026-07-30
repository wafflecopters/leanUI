/**
 * What the editor knows about a goal, node by node.
 *
 * These types were the OUTPUT of the TT replay engine (`goal-computation.ts`,
 * deleted in M5): the editor replayed the proof tree through the in-process TT
 * kernel and recorded, per node, the goal and hypotheses in scope. The Lean
 * backend answers the same question by asking Lean — `mapLeanGoalsToNodes`
 * matches Lean's reported goal states back onto proof-tree nodes — so the
 * records survive while the engine behind them does not.
 *
 * Everything here is presentation-ready text (LaTeX from Lean's tagged
 * pretty-print). Nothing carries a term representation: the proof tree deals in
 * Lean source and rendered output, and Lean owns the terms.
 */

export interface TypedHypothesis {
  readonly name: string;
  /** Rendered type, e.g. `0 < \varepsilon`. */
  readonly type: string;
}

export type ValidationResult =
  | { readonly status: 'solved' }
  | { readonly status: 'error'; readonly message: string };

/** The context and goal at the cursor. */
export interface TypedProofContext {
  readonly hypotheses: readonly TypedHypothesis[];
  readonly caseLabel?: string;
  readonly caseLabelLatex?: string;
  readonly inductionVar?: string;
  /** Rendered goal. */
  readonly goal: string;
  readonly validation?: ValidationResult;
}

/** Everything the view needs to narrate ONE proof step. */
export interface NodeGoalInfo {
  readonly goalLatex: string;
  readonly hypotheses: readonly TypedHypothesis[];
  readonly caseLabelLatex?: string;
  readonly validation?: ValidationResult;
  /** Rewrite nodes: the unified equation (lhs = rhs), implicit args filled in. */
  readonly unifiedEquationLatex?: string;
  /** Apply nodes: LaTeX of solved explicit args (e.g. `f` in `cong f`). */
  readonly appliedArgsLatex?: string[];
  /** Error message when this tactic failed. */
  readonly tacticError?: string;
  /** Suffices nodes: LaTeX of the `by` proof expression. */
  readonly sufficesByLatex?: string;
  /** Exact/have nodes: LaTeX of the proof expression. */
  readonly proofExprLatex?: string;
  /** Induction/cases nodes: LaTeX of the scrutinee. */
  readonly scrutineeLatex?: string;
  /** True when the goal is a VALUE to choose (`⊢ ℝ` — the midpoint of a
   *  transitivity) rather than a claim to prove. Switches the prose from
   *  "We must show …" to "We must choose a value of type …". */
  readonly isValueType?: boolean;
}

/** A constructor case, for generating case nodes. */
export interface ConstructorCaseInfo {
  readonly label: string;
  readonly constructorName: string;
  readonly paramNames: readonly string[];
}
