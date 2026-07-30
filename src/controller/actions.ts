/**
 * What the user can do right now — computed once, semantically, from the
 * session's state.
 *
 * This is the layer the whole refactor exists for. Before it, "what's possible"
 * was implicit in which buttons a component happened to render and which
 * handlers happened to be wired: unaskable from a test, invisible to a REPL,
 * and impossible to reason about as a whole. Here it is one pure function from
 * state to a list of moves, each with the arguments it needs and the choices
 * that are valid for them.
 *
 * A UI renders this list. A test asserts on it. An agent picks from it.
 */
import type { LeanSuggestion } from '../lean/leanSuggestions';
import type { ActionDescriptor, ActionParam, SessionState } from './types';

/** Action id prefixes — the stable vocabulary `dispatch` understands. */
export const ACTION = {
  suggestion: 'suggestion.',
  tactic: 'tactic.',
  hypothesis: 'hyp.',
  selectSubterm: 'select.subterm',
  selectHypothesis: 'select.hypothesis',
  clearSelection: 'select.clear',
  cursorGoto: 'cursor.goto',
  cursorNextHole: 'cursor.nextHole',
  cursorPrevHole: 'cursor.prevHole',
  clearNode: 'edit.clear',
  undo: 'history.undo',
  redo: 'history.redo',
} as const;

/** The manual tactics, with the argument each one needs. `kind` drives the
 *  input widget; `choices` are filled from the live context below. */
const TACTIC_FORMS: Array<{
  tactic: string;
  label: string;
  description: string;
  param: ActionParam;
}> = [
  {
    tactic: 'intros',
    label: 'Given…',
    description: 'Introduce the goal’s leading binders as named hypotheses',
    param: { name: 'names', kind: 'names', placeholder: 'ε epsPos', required: true },
  },
  {
    tactic: 'induction',
    label: 'Induct on…',
    description: 'Split the goal into one case per constructor',
    param: { name: 'scrutinee', kind: 'identifier', placeholder: 'n', required: true },
  },
  {
    tactic: 'exact',
    label: 'Exact…',
    description: 'Close the goal with a term',
    param: { name: 'expr', kind: 'expression', placeholder: 'h₁', required: true },
  },
  {
    tactic: 'unfold',
    label: 'Unfold…',
    description: 'Replace a definition by its body',
    param: { name: 'name', kind: 'identifier', placeholder: 'Carrier', required: true },
  },
  {
    tactic: 'fold',
    label: 'Fold…',
    description: 'Re-fold a definition’s body back into its name',
    param: { name: 'name', kind: 'identifier', placeholder: 'rhalf', required: true },
  },
  {
    tactic: 'rewrite',
    label: 'Rewrite…',
    description: 'Rewrite left-to-right with an equation',
    param: { name: 'lemma', kind: 'lemma', placeholder: 'halfEqDiv', required: true },
  },
  {
    tactic: 'rewrite_rev',
    label: 'Rewrite←…',
    description: 'Rewrite right-to-left with an equation',
    param: { name: 'lemma', kind: 'lemma', placeholder: 'halfEqDiv', required: true },
  },
  {
    tactic: 'apply',
    label: 'Apply…',
    description: 'Apply a lemma backwards, leaving its premises as goals',
    param: { name: 'lemma', kind: 'lemma', placeholder: 'divPos', required: true },
  },
  {
    tactic: 'simp',
    label: 'Simp…',
    description: 'Simplify with the given lemmas (empty = all @simp lemmas)',
    param: { name: 'lemmas', kind: 'lemmas', placeholder: 'addZero, mulOne', required: false },
  },
  {
    tactic: 'have',
    label: 'Have…',
    description:
      'Introduce an intermediate result: `h : 0 < ε / 2` states it and opens a goal, `h := proof` supplies the proof directly',
    param: { name: 'binding', kind: 'binding', placeholder: 'h : 0 < ε / 2', required: true },
  },
];

/** Names a tactic argument could sensibly take, by parameter kind. */
export interface ActionChoices {
  /** Hypotheses in scope — scrutinees, exact terms, rewrite equations. */
  hypotheses: readonly string[];
  /** File declarations usable as lemmas. */
  lemmas: readonly string[];
  /** File definitions that can be unfolded. */
  definitions: readonly string[];
}

const EMPTY_CHOICES: ActionChoices = { hypotheses: [], lemmas: [], definitions: [] };

function choicesFor(kind: ActionParam['kind'], c: ActionChoices): string[] | undefined {
  switch (kind) {
    case 'identifier':
      // A scrutinee or a definition name — both are plausible here.
      return dedupe([...c.hypotheses, ...c.definitions]);
    case 'lemma':
    case 'lemmas':
      return dedupe([...c.hypotheses, ...c.lemmas]);
    case 'expression':
    case 'names':
    case 'binding':
      return c.hypotheses.length ? [...c.hypotheses] : undefined;
  }
}

function dedupe(xs: string[]): string[] | undefined {
  const out = [...new Set(xs)];
  return out.length ? out : undefined;
}

/** The label a suggestion pill shows, and what it promises. */
function suggestionAction(s: LeanSuggestion): ActionDescriptor {
  const detail: NonNullable<ActionDescriptor['detail']> = { tactic: s.tactic };
  if (s.closes) detail.closes = true;
  if (s.subgoals !== undefined) detail.subgoals = s.subgoals;
  const previews = s.preview ? [s.preview] : s.previews;
  if (previews?.length) detail.previews = previews;
  return {
    id: `${ACTION.suggestion}${s.id}`,
    label: s.label,
    group: 'suggestion',
    description: s.closes
      ? 'Closes the goal'
      : detail.subgoals && detail.subgoals > 1
        ? `Leaves ${detail.subgoals} goals`
        : 'Transforms the goal',
    params: [],
    detail,
  };
}

/** The TT-style action tray for a clicked hypothesis, built from the VALIDATED
 *  results so only moves Lean accepts appear. */
function hypothesisActions(hyp: string, suggestions: readonly LeanSuggestion[]): ActionDescriptor[] {
  const out: ActionDescriptor[] = [];
  for (const s of suggestions) {
    if (s.id === `hyp-exact:${hyp}`) {
      out.push({ id: `${ACTION.hypothesis}exact:${hyp}`, label: `Exact ${hyp}`, group: 'hypothesis', description: `Close the goal with ${hyp}`, params: [], detail: { tactic: `exact ${hyp}`, closes: true } });
    } else if (s.id === `hyp-apply:${hyp}`) {
      out.push({ id: `${ACTION.hypothesis}apply:${hyp}`, label: `Apply ${hyp}`, group: 'hypothesis', description: `Apply ${hyp} to the goal`, params: [], detail: { tactic: `apply ${hyp}`, ...(s.subgoals ? { subgoals: s.subgoals } : {}) } });
    } else if (s.id === `hyp-cases:${hyp}`) {
      out.push({ id: `${ACTION.hypothesis}cases:${hyp}`, label: `Destructure ${hyp}`, group: 'hypothesis', description: `Pattern-match on ${hyp}`, params: [], detail: { tactic: `cases ${hyp}` } });
    } else if (s.id.startsWith('hyp-use:')) {
      const expr = s.id.slice('hyp-use:'.length);
      if (!expr.startsWith(`${hyp}.`)) continue;
      const field = expr.slice(hyp.length + 1);
      out.push({ id: `${ACTION.hypothesis}use:${expr}`, label: `Use ${field}`, group: 'hypothesis', description: `have h := ${expr} …`, params: [], detail: { tactic: `have h := ${expr}` } });
    }
  }
  return out;
}

/**
 * Every move available in this state, best-first: validated suggestions (one
 * click, already proven to work), then hypothesis actions, then the manual
 * tactics, then navigation and history.
 *
 * Tactics appear ONLY when the cursor sits on a hole with an open goal — a
 * tactic has nowhere to go otherwise, and offering it would be a lie.
 */
export function availableActions(
  state: Pick<SessionState, 'cursor' | 'goal' | 'suggestions' | 'selection' | 'history' | 'outline'>,
  choices: ActionChoices = EMPTY_CHOICES,
): ActionDescriptor[] {
  const out: ActionDescriptor[] = [];
  const atOpenGoal = state.cursor.isHole && state.goal !== null;

  if (atOpenGoal) {
    // Hypothesis actions render in their own tray; keep them out of the pills.
    for (const s of state.suggestions) {
      if (!s.id.startsWith('hyp-')) out.push(suggestionAction(s));
    }
    if (state.selection.hypothesis) {
      out.push(...hypothesisActions(state.selection.hypothesis, state.suggestions));
    }
    for (const form of TACTIC_FORMS) {
      out.push({
        id: `${ACTION.tactic}${form.tactic}`,
        label: form.label,
        group: 'tactic',
        description: form.description,
        params: [{ ...form.param, ...(choicesFor(form.param.kind, choices) ? { choices: choicesFor(form.param.kind, choices) } : {}) }],
      });
    }
  }

  // Selection: available whenever there is a goal to select within.
  if (state.goal) {
    if (state.goal.subterms.length > 0) {
      out.push({
        id: ACTION.selectSubterm,
        label: 'Focus a subterm',
        group: 'navigate',
        description: 'Narrow suggestions to one part of the goal',
        params: [{ name: 'pos', kind: 'identifier', placeholder: '/1/0', required: true, choices: state.goal.subterms.map((s) => s.pos) }],
      });
    }
    if (state.goal.hypotheses.length > 0) {
      out.push({
        id: ACTION.selectHypothesis,
        label: 'Use a hypothesis',
        group: 'navigate',
        description: 'Show the actions available on a hypothesis',
        params: [{ name: 'name', kind: 'identifier', required: true, choices: state.goal.hypotheses.map((h) => h.name) }],
      });
    }
    if (state.selection.subterm || state.selection.hypothesis) {
      out.push({ id: ACTION.clearSelection, label: 'Clear selection', group: 'navigate', params: [] });
    }
  }

  // Navigation is always available; the session resolves "next hole" itself.
  out.push({ id: ACTION.cursorNextHole, label: 'Next open goal', group: 'navigate', params: [] });
  out.push({ id: ACTION.cursorPrevHole, label: 'Previous open goal', group: 'navigate', params: [] });
  out.push({
    id: ACTION.cursorGoto,
    label: 'Go to step',
    group: 'navigate',
    params: [{ name: 'nodeId', kind: 'identifier', required: true }],
  });

  // A non-hole step can be reverted to a hole — the way to undo one branch of
  // the proof without unwinding the whole history.
  if (!state.cursor.isHole) {
    out.push({
      id: ACTION.clearNode,
      label: 'Clear this step',
      group: 'edit',
      description: 'Revert this tactic back to an open goal',
      params: [],
    });
  }

  if (state.history.canUndo) out.push({ id: ACTION.undo, label: 'Undo', group: 'history', params: [] });
  if (state.history.canRedo) out.push({ id: ACTION.redo, label: 'Redo', group: 'history', params: [] });

  return out;
}

/** Look up an action by id. */
export function findAction(actions: readonly ActionDescriptor[], id: string): ActionDescriptor | undefined {
  return actions.find((a) => a.id === id);
}

/** Validate dispatched args against an action's params. Returns an error
 *  message, or null when the call is well-formed. */
export function checkArgs(action: ActionDescriptor, args: Record<string, string> = {}): string | null {
  for (const p of action.params) {
    const v = args[p.name];
    if (p.required && (v === undefined || v.trim() === '')) {
      return `${action.id} needs a "${p.name}" argument${p.placeholder ? ` (e.g. ${p.placeholder})` : ''}`;
    }
  }
  return null;
}
