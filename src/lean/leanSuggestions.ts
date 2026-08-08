/**
 * Lean-backed tactic suggestions.
 *
 * Lean's discovery tactics (`exact?`, `apply?`, `rw?`, `simp?`) emit a message of
 * the form `Try this: <tactic>` when run at a goal. We run such a tactic at the
 * cursor's hole (via the same assemble→analyze round-trip used for goals), then
 * parse the `Try this:` messages into suggestions the WYSIWYG can offer — the
 * Lean equivalent of the old TT suggestion engine, sourced from Lean itself.
 *
 * A `LeanSuggestion` carries the literal tactic text; applying it replaces the
 * cursor hole's tactic with that text (parsed back into the proof tree).
 */
import type { LeanMessage } from './types';

export interface LeanSuggestion {
  /** Stable id (kind + tactic), for React keys / dedup. */
  id: string;
  /** Human label shown on the pill, e.g. "exact Nat.add_comm a b". */
  label: string;
  /** The raw Lean tactic to insert, e.g. "exact Nat.add_comm a b". */
  tactic: string;
  /** Which discovery tactic produced it. */
  kind: 'exact' | 'apply' | 'rw' | 'simp' | 'unfold';
  /** Single-line tactic to TRY when validating this suggestion (defaults to
   *  `tactic`). Differs for multi-line tactics like induction, whose applied
   *  form has `·` case bullets but whose validation form is the bare tactic. */
  validateTactic?: string;
  /** LaTeX of the goal AFTER applying this tactic — a preview of what it
   *  transforms the goal into (empty if it closes the goal). Filled by the
   *  validation round-trip. */
  preview?: string;
  /** LaTeX of EVERY goal the tactic leaves, in the order the editor will
   *  present them (see `orderGoalsForDisplay`) — so a pill for a goal-splitting
   *  tactic shows all its obligations (`apply divPos` → `0 < ε`, `0 < 2`), not
   *  just the first. Empty when the tactic closes the goal. `preview` still
   *  wins when set: for a subterm-scoped rewrite it's the smaller, more legible
   *  delta. */
  previews?: string[];
  /** True when applying this tactic CLOSES the goal (no goals remain). */
  closes?: boolean;
  /** Number of goals remaining after the tactic (from the validation trial).
   *  A multi-subgoal opener (e.g. `constructor` on DPair: body + witness)
   *  applies with this many child holes so every obligation is visible
   *  immediately instead of surfacing when the first one closes. */
  subgoals?: number;
  /** Lean goal tags for those subgoals, in DISPLAY order (witness-first, see
   *  orderedSubgoalTags). When present, applying prints `case <tag> =>` blocks
   *  so the proof presents goals in this order regardless of Lean's. */
  subgoalTags?: string[];
}

/**
 * Present subgoals witness-first: Lean's `apply`/`constructor` POSTPONES
 * dependent goals, so `DPair` yields [body-with-?fst, fst] — but a human gives
 * the witness first, then proves the property about it. Generic signal, no
 * domain names: a goal whose target mentions NO metavariable (`?m`) provides
 * data the metavariable-bearing goals depend on — put those first (stable
 * order otherwise). Returns null unless every goal is tagged (the `case`
 * selector needs names) — callers then fall back to Lean's order.
 */
export function orderedSubgoalTags(
  goals: ReadonlyArray<{ tag?: string; target: string }>,
): string[] | null {
  if (goals.length < 2) return null;
  if (goals.some((g) => !g.tag)) return null;
  const hasMeta = (g: { target: string }) => /\?/.test(g.target);
  const data = goals.filter((g) => !hasMeta(g));
  const dependent = goals.filter(hasMeta);
  if (data.length === 0 || dependent.length === 0) return goals.map((g) => g.tag!);
  return [...data, ...dependent].map((g) => g.tag!);
}

/**
 * The goals a tactic leaves, in the order the editor will PRESENT them: the
 * `subgoalTags` order when we have one (applying prints `case <tag> =>` blocks
 * in that order), else Lean's own. Keeping previews and bullets in a single
 * order means a pill's Nth preview line is the Nth branch you actually get.
 * Falls back to Lean's order if the tags don't cover the goals exactly.
 */
export function orderGoalsForDisplay<T extends { case?: string }>(
  goals: readonly T[],
  subgoalTags: readonly string[] | null | undefined,
): T[] {
  if (!subgoalTags) return [...goals];
  const byTag = new Map(goals.map((g) => [g.case, g] as const));
  const ordered = subgoalTags.map((t) => byTag.get(t)).filter((g): g is T => g !== undefined);
  return ordered.length === goals.length ? ordered : [...goals];
}

/** Discovery tactics we try at a hole, in priority order (cheapest/most-closing
 *  first). NOTE: `rw?` is Mathlib-only (absent in core Lean) — file rewrites are
 *  surfaced via the dedicated rewrite-candidate trials instead. */
export const DISCOVERY_TACTICS: ReadonlyArray<{ kind: LeanSuggestion['kind']; tactic: string }> = [
  { kind: 'exact', tactic: 'exact?' },
  { kind: 'simp', tactic: 'simp?' },
  // `rw?` exists only with Mathlib. It's listed anyway: where it's absent it
  // fails like any other candidate and yields nothing, and where it's present
  // it's the best rewrite search available — far better than ranking the
  // file's own lemmas by token overlap. Availability is trialed, not assumed.
  { kind: 'rw', tactic: 'rw?' },
  // `apply?` dropped: its `refine <lemma> ?_ ?_` results were mostly noise
  // (any lemma whose conclusion unifies, e.g. leqAntisym/succInj on an equality)
  // and don't carry their subgoals into the structured editor.
];

/**
 * Suggestions targeted at a clicked subterm, derived from its text — no Lean
 * round-trip needed. A bare identifier (a variable) offers `induction`/`cases`
 * on it; this mirrors the TT editor's "click n → induct on n" interaction.
 */
export function targetedSuggestions(subtermText: string): LeanSuggestion[] {
  const t = subtermText.trim();
  // Bare lowercase-ish identifier (a variable, not an application/operator).
  if (/^[a-zA-Z_][a-zA-Z0-9_']*$/.test(t)) {
    // Emit with two `·` case placeholders so the parser builds a real induction
    // node (bare `induction n` alone is incomplete Lean). Two cases cover the
    // common inductives (Nat/Bool/List/Either); extras/shortfall surface as a
    // Lean error the user can fix, and the goal round-trip shows the real cases.
    const withHoles = (kw: string) => `${kw} ${t}\n·\n  sorry\n·\n  sorry`;
    // validateTactic is the BARE form: `induction t` alone leaves goals (valid)
    // when t is a real local variable, but errors when t is a bound/unknown name
    // (e.g. clicking the `i` inside ∑) — so validation correctly rejects it.
    return [
      { id: `lean-induction:${t}`, label: `induction ${t}`, tactic: withHoles('induction'), validateTactic: `induction ${t}`, kind: 'apply' },
      { id: `lean-cases:${t}`, label: `cases ${t}`, tactic: withHoles('cases'), validateTactic: `cases ${t}`, kind: 'apply' },
    ];
  }
  // An equality goal offers `rfl` — the tactic reduces both sides (so it both
  // computes, e.g. ∑[i,0,0] i ↦ 0, AND closes goals that hold definitionally).
  // It's validated, so it only appears when it actually closes.
  if (/\s=\s/.test(t)) {
    return [{ id: 'lean-rfl', label: 'rfl', tactic: 'rfl', kind: 'exact' }];
  }
  return [];
}

/** A hypothesis name not already in scope: `h`, then `h1`, `h2`, … Used when
 *  committing a "use hypothesis with arguments" expression as a `have`. */
export function freshHypName(existing: readonly string[]): string {
  const taken = new Set(existing);
  if (!taken.has('h')) return 'h';
  for (let i = 1; ; i++) {
    const name = `h${i}`;
    if (!taken.has(name)) return name;
  }
}

/**
 * Validated action candidates for a CLICKED hypothesis — the Lean-path version
 * of the TT editor's "click a hypothesis to use it": close the goal with it,
 * apply it backwards, or destructure it. Each is trialed via the normal
 * validation round-trip, so only the ones that actually work surface.
 */
export function hypothesisSuggestions(
  hyp: string,
  /** Leaf names of the hypothesis's shape, from the extractor. When Lean knows
   *  them the destructure is an `obtain`, which names the pieces AS IT IS MADE.
   *  The `cases` form inserts an UNNAMED branch and waits a round-trip for Lean
   *  to name it; anything that disturbs that window (a stale render, a refresh
   *  that lands late) leaves "Case (case)" on screen and pieces the proof
   *  cannot refer to. `obtain` has no such window, and no branch to indent. */
  flatFields: readonly string[] = [],
): LeanSuggestion[] {
  const names = uniqueNames(flatFields);
  const destructure: LeanSuggestion = names.length > 0
    ? {
        id: `hyp-cases:${hyp}`,
        label: `obtain \u27e8${names.join(', ')}\u27e9 := ${hyp}`,
        tactic: `obtain \u27e8${names.join(', ')}\u27e9 := ${hyp}`,
        kind: 'apply',
      }
    // Nothing known about the shape (an older extractor, or a type with more
    // than one constructor): fall back to the branch form.
    : {
        id: `hyp-cases:${hyp}`,
        label: `cases ${hyp}`,
        tactic: `cases ${hyp}\n\u00b7\n  sorry`,
        validateTactic: `cases ${hyp}`,
        kind: 'apply',
      };
  return [
    { id: `hyp-exact:${hyp}`, label: `exact ${hyp}`, tactic: `exact ${hyp}`, kind: 'exact' },
    { id: `hyp-apply:${hyp}`, label: `apply ${hyp}`, tactic: `apply ${hyp}`, kind: 'apply' },
    destructure,
  ];
}

/** Lean rejects a repeated binder, and nested pairs genuinely repeat: a DPair
 *  of a Pair reports `fst, fst, snd`. Suffix the duplicates. */
function uniqueNames(names: readonly string[]): string[] {
  const used = new Set<string>();
  return names.map((n) => {
    let name = n;
    for (let i = 1; used.has(name); i++) name = `${n}${i}`;
    used.add(name);
    return name;
  });
}

/**
 * Parse `Try this:` suggestion text out of a Lean info message.
 *
 * Lean formats them as (note the leading tag in some versions):
 *   "Try this:\n  exact Nat.add_comm a b"
 *   "Try this:\n  [apply] exact Nat.add_comm a b"
 *   "Try this: rw [h]\n  -- no goals"     (rw? variant)
 * We extract the tactic line(s), stripping the `Try this:` prefix, a leading
 * `[apply]`/`[rw]` tag, and trailing `-- ...` comments.
 */
export function parseTryThis(text: string, kind: LeanSuggestion['kind']): LeanSuggestion[] {
  const marker = 'Try this:';
  const at = text.indexOf(marker);
  if (at === -1) return [];
  const after = text.slice(at + marker.length);

  const out: LeanSuggestion[] = [];
  const seen = new Set<string>();
  for (let raw of after.split('\n')) {
    let line = raw.trim();
    if (line.length === 0) continue;
    // Strip a leading bracket tag like `[apply]` / `[rw]`.
    line = line.replace(/^\[[a-zA-Z?]+\]\s*/, '');
    // Drop trailing `-- ...` comment (e.g. `-- no goals`).
    const cmt = line.indexOf('--');
    if (cmt !== -1) line = line.slice(0, cmt).trim();
    if (line.length === 0) continue;
    // Skip lines that are clearly not tactics (defensive).
    if (line.startsWith('Try this')) continue;
    if (seen.has(line)) continue;
    seen.add(line);
    out.push({
      id: `lean-${kind}:${line}`,
      label: line,
      tactic: line,
      kind,
      // `exact?` only returns terms that CLOSE the goal.
      closes: kind === 'exact',
    });
  }
  return out;
}

/** Parse all Try-this suggestions from a batch of messages for a given kind. */
export function suggestionsFromMessages(
  messages: LeanMessage[],
  kind: LeanSuggestion['kind'],
): LeanSuggestion[] {
  const out: LeanSuggestion[] = [];
  const seen = new Set<string>();
  for (const m of messages) {
    if (m.severity !== 'information') continue;
    for (const s of parseTryThis(m.text, kind)) {
      if (seen.has(s.tactic)) continue;
      seen.add(s.tactic);
      out.push(s);
    }
  }
  return out;
}
