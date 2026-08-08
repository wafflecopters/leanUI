/** Shared types for the Lean backend client (mirrors server/lean-bridge.ts). */

export type LeanSeverity = 'error' | 'warning' | 'information' | 'hint';

export interface LeanMessage {
  severity: LeanSeverity;
  /** 1-based line. */
  startLine: number;
  /** 0-based column. */
  startCol: number;
  endLine: number;
  endCol: number;
  text: string;
}

/** One hypothesis in a goal state (names share a type, e.g. `a b : Nat`). */
export interface LeanHyp {
  names: string[];
  /** Tagged pretty-print of the hypothesis type, for WYSIWYG rendering. */
  type: TaggedText;
}

/** A single open goal: optional case name, hypotheses, and a target. */
/**
 * What a hypothesis IS, according to the elaborator — not according to its
 * rendered type. The editor used to recover these by reading pretty-printed
 * text, which is written for a human and changes with notation: a binder named
 * `epsilon` shows as `ε`, an implication can print as prose, and an
 * abbreviation hides the structure it stands for. Every one of those broke a
 * suggestion. Lean knows them exactly, so it says so.
 */
export interface LeanHypFact {
  name: string;
  /** Head constant of the type after unfolding — `EpsDeltaWitness …` is `Pair`. */
  typeHead: string | null;
  /** Is it a function? (Then it can be USED: applied to arguments.) */
  isFun: boolean;
  /** Constructors of the (unfolded) type — branches a `cases` on it opens. */
  ctors?: number;
  /** Every leaf name a one-line `obtain ⟨…⟩ := h` binds — one-constructor
   *  structures flattened all the way down. Empty when there is nothing to
   *  destructure. Names may repeat (two nested pairs both have a `fst`); the
   *  caller uniquifies. */
  flatFields?: string[];
  /** Field names, when the type is a structure. */
  fields: string[];
}

export interface LeanGoalState {
  /** `case foo` name, if any. */
  case?: string;
  hyps: LeanHyp[];
  /** Tagged pretty-print of the target type (after ⊢). */
  targetTagged: TaggedText;
  /** Whether the target is a Prop (a claim to prove) as opposed to data (a
   *  value to choose, e.g. `⊢ ℝ` after `apply ltLeTrans`). Absent on output
   *  from an extractor built before this field existed. */
  isProp?: boolean;
  /** Head constant of the target, AS WRITTEN — `rlt` for `0 < x`. */
  targetHead?: string | null;
  /** Structural facts per hypothesis, from the elaborator. */
  hypFacts?: LeanHypFact[];
  /** Plain-text rendering (fallback / copy). */
  plain: string;
}

export interface LeanGoal {
  startLine: number;
  startCol: number;
  endLine: number;
  endCol: number;
  /** Case tags of goals whose metavariable occurs in a sibling goal's type —
   *  values to CHOOSE (e.g. the `b` midpoint of `apply ltLeTrans`). Recorded
   *  by the extractor at the split itself, so it survives later assignment. */
  valueCaseTags?: string[];
  /** The open goal states at this tactic position. */
  goals: LeanGoalState[];
}

/**
 * Tagged pretty-printed Lean expression (`CodeWithInfos`). Mirrors the bridge's
 * `TaggedText` and the converter's `TaggedJson`. See `codeWithInfos.ts`.
 */
export type TaggedText =
  | { t: 'text'; s: string }
  | { t: 'append'; kids: TaggedText[] }
  | { t: 'tag'; pos: string; child: TaggedText };

/** A top-level declaration the user wrote. */
export interface LeanDeclaration {
  name: string;
  kind: 'def' | 'theorem' | 'inductive' | 'axiom' | 'opaque';
  prettyType: string;
  /** Tagged pretty-print of the type, for the WYSIWYG math editor. */
  typeTagged?: TaggedText;
  /** Present for plain `def`s only. */
  prettyValue?: string;
  /** Tagged pretty-print of the value (defs only). */
  valueTagged?: TaggedText;
  /** Head constant of the conclusion, AS WRITTEN — `rlt` for `a < b`, however
   *  that prints. What "concludes something shaped like this goal?" compares. */
  conclHead?: string | null;
  /** Is that head an inductive type? (A case split can be done on it.) */
  conclIsInductive?: boolean;
  /** Constructors of that inductive — branches a `cases` on this lemma's
   *  result opens (`leTotal a b` concludes an `Either`, so two). */
  conclCtors?: number;
  /** Head constant of each EXPLICIT argument's type, in order. */
  argHeads?: (string | null)[];
  /** How many goals a backwards step leaves: the explicit arguments the
   *  conclusion does not mention, so unifying with the goal cannot solve them. */
  premises?: number;
  /** 1-based line, 0-based column of the declaration's start. */
  line: number;
  col: number;
}

export interface AnalyzeResult {
  success: boolean;
  messages: LeanMessage[];
  goals: LeanGoal[];
  declarations: LeanDeclaration[];
  bridgeError?: string;
  durationMs: number;
}
