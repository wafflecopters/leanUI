/**
 * A goal you can click into.
 *
 * The goal is rendered as LaTeX with every subexpression wrapped in an
 * `\htmlId`, and `subtermMap` says what each of those ids refers to — so
 * clicking a rendered subterm identifies a specific piece of the goal, which is
 * what makes "rewrite HERE" and "compute THIS" possible.
 *
 * The TT renderer that used to produce these (`interactive-goal.ts`) is gone
 * with M5. Lean's tagged pretty-print already carries subexpression positions,
 * so `src/lean/leanInteractiveGoal.ts` builds the same record straight from it —
 * and the id now encodes a Lean `SubExpr.Pos`, which is a far better name for a
 * subterm than anything the TT path could construct.
 */

/** A selected subterm, identified by its `htmlId`. */
export type GoalPath = string;

/** A Pi binder in the goal's root spine — what `intro` would introduce. */
export interface GoalBinderInfo {
  readonly index: number;
  readonly name: string;
  readonly domainLatex: string;
  readonly isImplicit: boolean;
}

/** One annotated (clickable) subterm of the goal. */
export interface SubtermInfo {
  readonly htmlId: string;
  /** True when this subterm is an application whose head is a constant. */
  readonly isAppOfConst: boolean;
  /** The head constant's name, when there is one. */
  readonly headName?: string;
  /** The variable's name, when the subterm is a variable. */
  readonly varName?: string;
  /** 1-based occurrence index of `headName` in the goal, for targeted rewrites. */
  readonly occurrenceIndex?: number;
  /** The binder index, when this subterm sits inside a Pi binder's domain. */
  readonly binderIndex?: number;
}

export interface InteractiveGoal {
  /** Full LaTeX, with an `\htmlId` per subterm. */
  readonly latex: string;
  /** Pi-spine binders (for intro suggestions). */
  readonly binders: readonly GoalBinderInfo[];
  /** htmlId → what that subterm is. */
  readonly subtermMap: ReadonlyMap<string, SubtermInfo>;
  /** Variable name → its type's head name (for induction suggestions). */
  readonly contextVarTypes: ReadonlyMap<string, string>;
}
