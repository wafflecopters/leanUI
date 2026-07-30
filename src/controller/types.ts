/**
 * The proof session's vocabulary: a serializable description of WHERE the proof
 * is, WHAT Lean says about it, and WHAT THE USER CAN DO NEXT.
 *
 * Everything here is plain data — no React, no DOM, no Lean process. A
 * `SessionState` can be printed in a terminal, asserted on in a test, shipped
 * over MCP, or rendered as a UI. That is the point: the set of possible moves
 * is computed once, semantically, and every front end reads the same answer.
 */
import type { ProofNode, ProofNodeId } from '../proof-tree/proof-tree';
import type { LeanGoalState, LeanMessage, TaggedText } from '../lean/types';
import type { LeanSuggestion } from '../lean/leanSuggestions';

// ─── Goal ────────────────────────────────────────────────────────────────────

/** One hypothesis in the cursor's context. */
export interface HypothesisView {
  name: string;
  /** Plain Lean text of the type (`0 < ε`). */
  text: string;
  /** LaTeX, for the math renderer. */
  latex: string;
  /** True when this hypothesis is an equation — a rewrite candidate. */
  isEquation: boolean;
}

/** The Lean goal at the cursor. */
export interface GoalView {
  /** Lean's `case` tag, when the goal has one. */
  case?: string;
  hypotheses: HypothesisView[];
  /** Plain Lean text of the TARGET alone (never the hypothesis block — ranking
   *  and shape detection read this, and the whole-state form silently makes a
   *  `<` goal look like an `=` goal). */
  targetText: string;
  targetLatex: string;
  /** Tagged pretty-print, for the clickable-subterm renderer. */
  targetTagged: TaggedText;
  /** Every clickable subterm: Lean `SubExpr.Pos` → its plain text. */
  subterms: Array<{ pos: string; text: string }>;
}

/** A clicked subterm of the goal — narrows suggestions to that position. */
export interface SubtermSelection {
  /** The goal-path id used by the interactive renderer (`goal-1_0`). */
  path: string;
  /** Lean `SubExpr.Pos` (`/1/0`). */
  pos: string;
  text: string;
  latex: string;
}

// ─── Proof outline ───────────────────────────────────────────────────────────

export type NodeStatus = 'open' | 'solved' | 'error' | 'unknown';

/**
 * One step of the proof, flattened to plain data. `children` mirrors the tree's
 * branch structure, so the outline is a faithful (and printable) picture of the
 * proof — the REPL renders it as an indented list, the UI as prose.
 */
export interface OutlineNode {
  id: ProofNodeId;
  tag: ProofNode['tag'];
  /** One-line description: `intro ε epsPos`, `apply divPos`, `?` for a hole. */
  label: string;
  /** Branch name when this node hangs off a labelled branch (`case succ`,
   *  `side goal 1`, `proof of h1`). */
  branch?: string;
  status: NodeStatus;
  /** Lean's goal at this node, when it reported one. */
  goalText?: string;
  /** Lean's error at this node, when the tactic failed. */
  error?: string;
  isCursor: boolean;
  children: OutlineNode[];
}

// ─── Actions: the "what's possible" layer ────────────────────────────────────

/** What kind of value an action's parameter takes — enough for a UI to pick an
 *  input widget and for a REPL to prompt. */
export type ActionParamKind =
  | 'names' // space/comma-separated binder names: `ε epsPos`
  | 'identifier' // a single name: a variable, a definition
  | 'lemma' // a declaration name usable as a rewrite/apply
  | 'lemmas' // zero or more lemma names
  | 'expression' // a Lean term
  | 'binding'; // `name := expression`

export interface ActionParam {
  name: string;
  kind: ActionParamKind;
  /** Example input, shown as placeholder/prompt text. */
  placeholder?: string;
  /** Concrete values known to be valid here (hypothesis names, file lemmas).
   *  A UI renders these as a picker; a REPL tab-completes them. */
  choices?: string[];
  required: boolean;
}

export type ActionGroup =
  /** A validated tactic the engine found and vetted — one click, no typing. */
  | 'suggestion'
  /** A tactic the user drives by supplying arguments. */
  | 'tactic'
  /** Actions on the clicked hypothesis. */
  | 'hypothesis'
  /** Cursor / selection movement. */
  | 'navigate'
  /** Structural edits to an existing step. */
  | 'edit'
  | 'history';

/**
 * Something the user can do right now. `params` empty means it's ready to run
 * as-is; otherwise the caller must supply arguments. This list IS the answer to
 * "what's possible at this moment" — the UI renders it, tests assert on it, and
 * an agent picks from it.
 */
export interface ActionDescriptor {
  /** Stable id to pass back to `dispatch` — e.g. `tactic.intros`,
   *  `suggestion.lean-applylemma:divPos`, `history.undo`. */
  id: string;
  label: string;
  group: ActionGroup;
  /** Why this action is worth taking / what it does. */
  description?: string;
  params: ActionParam[];
  /** For suggestions: what Lean said would happen if you take it. */
  detail?: {
    /** The literal tactic that would be inserted. */
    tactic?: string;
    /** True when the tactic closes the goal outright. */
    closes?: boolean;
    /** Number of goals it leaves. */
    subgoals?: number;
    /** LaTeX of each resulting goal, in the order the branches will appear. */
    previews?: string[];
  };
}

// ─── Session state ───────────────────────────────────────────────────────────

/** A Lean diagnostic attributed to the proof (not the rest of the file). */
export interface ProofDiagnostic {
  severity: LeanMessage['severity'];
  text: string;
  /** The proof node it lands on, when we could attribute it. */
  nodeId?: ProofNodeId;
}

export interface SessionStatus {
  /** Holes with an open Lean goal. */
  openGoals: number;
  /** True when the proof has no open goals and no errors. */
  complete: boolean;
  diagnostics: ProofDiagnostic[];
}

export interface BusyState {
  /** A goal round-trip is in flight — the goal shown may be one step behind. */
  goals: boolean;
  /** Suggestion trials are still arriving. */
  suggestions: boolean;
}

/** The complete, serializable picture of a proof session. */
export interface SessionState {
  decl: {
    name: string;
    kind: string;
    /** 1-based line of the declaration in the source file. */
    line: number;
    /** The declaration's type as Lean prints it. */
    typeText: string;
  };
  outline: OutlineNode;
  cursor: {
    nodeId: ProofNodeId;
    tag: ProofNode['tag'];
    /** Only a hole takes tactics. */
    isHole: boolean;
  };
  /** Lean's goal at the cursor — null when the cursor isn't on an open goal. */
  goal: GoalView | null;
  selection: {
    subterm: SubtermSelection | null;
    hypothesis: string | null;
  };
  /** Validated suggestions at the cursor, best first. */
  suggestions: LeanSuggestion[];
  /** Everything the user could do right now. */
  actions: ActionDescriptor[];
  status: SessionStatus;
  busy: BusyState;
  history: { canUndo: boolean; canRedo: boolean };
  /** The proof block as it would be written back to the file. */
  proofSource: string;
  /** Set when the round-trip itself failed (bridge down, assembly error). */
  error?: string;
}

/** An action to perform, as dispatched. */
export interface SessionAction {
  id: string;
  /** Values for the action's `params`, keyed by param name. */
  args?: Record<string, string>;
}

export interface DispatchResult {
  ok: boolean;
  /** Why it failed — an unknown id, a missing required argument, or a tactic
   *  the tree wouldn't accept. */
  error?: string;
}

/** Internal: the raw Lean read-out a refresh produces, before it is shaped
 *  into a `SessionState`. Exported for tests. */
export interface GoalSnapshot {
  cursorGoal: LeanGoalState | null;
  messages: LeanMessage[];
}
