/**
 * Pick the file's own equality lemmas as candidate rewrites and rank them by
 * relevance to a goal — the input to "try the file's rewrites at this goal"
 * (the core-Lean stand-in for `rw?`, which only exists in Mathlib).
 *
 * A declaration is a rewrite candidate when its type's CONCLUSION is an equality
 * (`… = …`). We rank by how many symbol tokens the equality's left-hand side
 * shares with the goal text, so the lemmas most likely to fire are tried first
 * under the candidate cap.
 */
import type { LeanDeclaration } from './types';

export interface RewriteCandidate {
  /** Declaration name to pass to `rw [name]`. */
  name: string;
  /** Text of the equality's left-hand side (for relevance ranking). */
  lhs: string;
}

/** Split a top-level (paren/bracket-depth 0) segment on the first ` <sep> `. */
function splitTopLevel(s: string, sep: string): [string, string] | null {
  let depth = 0;
  for (let i = 0; i + sep.length <= s.length; i++) {
    const c = s[i];
    if (c === '(' || c === '[' || c === '{') depth++;
    else if (c === ')' || c === ']' || c === '}') depth--;
    else if (depth === 0 && s.startsWith(sep, i)) {
      return [s.slice(0, i), s.slice(i + sep.length)];
    }
  }
  return null;
}

/** Strip a leading `∀ <binders>,` group at top level (repeatably). */
function stripForall(s: string): string {
  let rest = s.trim();
  while (rest.startsWith('∀')) {
    const comma = splitTopLevel(rest, ', ');
    if (!comma) break;
    rest = comma[1].trim();
  }
  return rest;
}

/** The conclusion of a (possibly dependent) function type: drop leading binders. */
function conclusionOf(prettyType: string): string {
  let rest = stripForall(prettyType);
  // Strip leading `→`-separated antecedents at top level (then any ∀ they expose).
  for (;;) {
    const split = splitTopLevel(rest, ' → ');
    if (!split) break;
    rest = stripForall(split[1]);
  }
  return rest.trim();
}

/** A binder group antecedent — `(a b : ℝ)`, `{R : Real}`, `[Inst α]`, `⦃x : T⦄`.
 *  Returns the bracket and the bound names, or null when the antecedent is an
 *  ordinary premise (`0 < a`) rather than a binder. */
function asBinderGroup(antecedent: string): { bracket: string; names: string[] } | null {
  const s = antecedent.trim();
  const pairs: Array<[string, string]> = [['(', ')'], ['{', '}'], ['[', ']'], ['⦃', '⦄']];
  const pair = pairs.find(([o, c]) => s.startsWith(o) && s.endsWith(c));
  if (!pair) return null;
  const inner = s.slice(pair[0].length, s.length - pair[1].length);
  const colon = splitTopLevel(inner, ' : ');
  if (!colon) return null; // `(0 < a)` — a parenthesized premise, not a binder
  const names = colon[0].trim().split(/\s+/).filter(Boolean);
  if (names.length === 0 || !names.every((n) => /^[A-Za-z_α-ωΑ-Ω][^\s]*$/.test(n))) return null;
  return { bracket: pair[0], names };
}

/** Is `name` used in `text` as a standalone token? */
function mentions(text: string, name: string): boolean {
  return text.split(/[^A-Za-z0-9_'α-ωΑ-Ω]+/).includes(name);
}

/**
 * How many GOALS a backwards step through this type leaves.
 *
 * `apply`/`rw` unify the lemma's CONCLUSION with the goal, which solves every
 * argument the conclusion mentions. What's left over becomes a goal. So:
 *
 *   - an ordinary premise (`0 < a`) is always a goal;
 *   - an explicit binder `(a b : ℝ)` contributes a goal per name the conclusion
 *     does NOT mention — `leLtTrans : (a b c : ℝ) → a ≤ b → b < c → a < c`
 *     leaves the middle point `b` open, which is exactly the `ℝ` goal Lean
 *     reports;
 *   - implicit `{…}` and instance `[…]` binders contribute nothing: Lean
 *     determines them from the types of the other arguments, which the printed
 *     conclusion doesn't show.
 *
 * An estimate — the trial-validated suggestions carry Lean's true count — but
 * one that matches Lean on the ordinary shapes, where counting every `→`
 * antecedent (the previous rule) turned each lemma's own binder list into
 * phantom goals.
 */
function premiseCount(prettyType: string): number {
  let rest = stripForall(prettyType);
  const antecedents: string[] = [];
  for (;;) {
    const split = splitTopLevel(rest, ' → ');
    if (!split) break;
    antecedents.push(split[0]);
    rest = stripForall(split[1]);
  }
  const conclusion = rest;
  let count = 0;
  for (const a of antecedents) {
    const binder = asBinderGroup(a);
    if (!binder) {
      count++;
    } else if (binder.bracket === '(') {
      count += binder.names.filter((n) => !mentions(conclusion, n)).length;
    }
  }
  return count;
}

/**
 * How many subgoals `apply <name>` is likely to produce. Floored at 1: an apply
 * node always has at least one child branch, even when the lemma closes the
 * goal outright. Returns 1 if the name is unknown.
 */
export function applySubgoalCount(declarations: readonly LeanDeclaration[], name: string): number {
  const d = declarations.find((x) => x.name === name);
  if (!d) return 1;
  return Math.max(1, premiseCount(d.prettyType));
}

/**
 * How many SIDE GOALS `rw [name]` is likely to leave — the lemma's premises.
 * The equality conclusion is unified with the goal by `rw`; each remaining
 * premise becomes a side goal (e.g. `summationSplit : ∀ i n, i ≤ n → ∀ f, … = …`
 * leaves the one `i ≤ n` premise). Unlike `applySubgoalCount` this is NOT
 * floored at 1: a premise-free lemma like `plusComm` leaves 0 side goals.
 */
export function rewriteSideGoalCount(declarations: readonly LeanDeclaration[], name: string): number {
  const d = declarations.find((x) => x.name === name);
  if (!d) return 0;
  return premiseCount(d.prettyType);
}

/** Does the type take an equality as a hypothesis? (congruence/symm/trans-style
 *  combinators — useless as plain rewrites, they'd just ask for the eq back.) */
function takesEqualityHypothesis(prettyType: string): boolean {
  let rest = stripForall(prettyType);
  for (;;) {
    const split = splitTopLevel(rest, ' → ');
    if (!split) return false; // reached conclusion
    if (splitTopLevel(split[0], ' = ')) return true; // an antecedent is an equality
    rest = stripForall(split[1]);
  }
}

/**
 * The TARGET of a goal, given text that may be a whole goal state.
 *
 * Lean's plain rendering of a goal is `<hyp>\n…\n⊢ <target>`. Ranking against
 * all of that is wrong — the hypotheses' operators drown out the target's (a
 * context carrying `limF : lim⟦x0⟧ f = L` made a `0 < ε / 2` goal read as an
 * EQUALITY, so every `<` lemma was filtered out). Everything after the last
 * `⊢` is the target; text without a `⊢` is already a bare expression.
 */
export function targetOfGoalText(text: string): string {
  const at = text.lastIndexOf('⊢');
  return (at === -1 ? text : text.slice(at + 1)).trim();
}

/**
 * Symbol tokens for overlap ranking; split on `.` so `a.succ`/`n.succ` share
 * `succ`.
 *
 * NUMERALS count. Without them `0 ≤ 1` tokenizes to just `{≤}` — the same as
 * every other ≤ statement in the file — so a lemma whose conclusion IS the goal
 * scores no better than an unrelated one and gets lost under the cap.
 */
function tokens(s: string): Set<string> {
  const out = new Set<string>();
  for (const m of s.matchAll(/[A-Za-z_][A-Za-z0-9_']*|\d+|[+\-*/≤<>∑∏·]/g)) out.add(m[0]);
  return out;
}

/** Binary operators, loosest-binding first. */
const OPS = [' = ', ' ≤ ', ' < ', ' + ', ' - ', ' * ', ' / '];

/**
 * The head operator of an expression: the loosest-binding binary operator at
 * paren depth 0 (e.g. `(1 + a) * a` → `*`, `a + b` → `+`). Null if none — used
 * to boost rewrite lemmas whose LHS is shaped like the focused subterm (a `*`
 * focus wants `mul*` lemmas even when they share few tokens).
 */
function headOp(s: string): string | null {
  let depth = 0;
  const found = new Set<string>();
  for (let i = 0; i < s.length; i++) {
    const c = s[i];
    if (c === '(' || c === '[' || c === '{') depth++;
    else if (c === ')' || c === ']' || c === '}') depth--;
    else if (depth === 0) {
      for (const op of OPS) if (s.startsWith(op, i)) { found.add(op.trim()); break; }
    }
  }
  for (const op of OPS) if (found.has(op.trim())) return op.trim();
  return null;
}

/**
 * Equality lemmas from the file (excluding `currentDeclName`, which can't rewrite
 * itself), each with its conclusion's LHS. Only `def`/`theorem` declarations
 * whose conclusion is a top-level equality qualify.
 */
export function equalityLemmas(
  declarations: readonly LeanDeclaration[],
  currentDeclName?: string,
): RewriteCandidate[] {
  const out: RewriteCandidate[] = [];
  for (const d of declarations) {
    if (d.name === currentDeclName) continue;
    if (d.kind !== 'def' && d.kind !== 'theorem') continue;
    // Skip congruence/symm/trans-style combinators (they consume an equality).
    if (takesEqualityHypothesis(d.prettyType)) continue;
    const concl = conclusionOf(d.prettyType);
    const eq = splitTopLevel(concl, ' = ');
    if (!eq) continue;
    out.push({ name: d.name, lhs: eq[0].trim() });
  }
  return out;
}

/**
 * The file's unfoldable definitions: `def`s whose conclusion is NOT an equality
 * (i.e. functions/data like `sum`, `plus`, not the equality lemmas). Each is a
 * candidate for `unfold <name>` — which targets the underlying constant, so it
 * works regardless of how the term is displayed (e.g. `unfold sum` fires on a
 * goal shown with ∑ notation). Validation drops the ones that don't appear.
 */
export function unfoldableDefs(
  declarations: readonly LeanDeclaration[],
  currentDeclName?: string,
  cap = 40,
): string[] {
  const out: string[] = [];
  for (const d of declarations) {
    if (d.name === currentDeclName) continue;
    if (d.kind !== 'def') continue;
    // Skip noise: auto-generated instances (instOfNat…) and structure
    // projections (Semiring.add) — not useful unfold targets.
    if (d.name.startsWith('inst') || d.name.includes('.')) continue;
    // A LEMMA is not an unfold target. Anything concluding in a relation
    // (`= `, `≤`, `<`) is a proof about terms, not a definition of one —
    // `unfold zeroLeOne` is meaningless, and before this filter the list was
    // mostly such lemmas, crowding out the actual definitions under the cap.
    if (headOp(conclusionOf(d.prettyType)) !== null) continue;
    out.push(d.name);
    if (out.length >= cap) break;
  }
  return out;
}

/** Every name a declaration binds in its own telescope (∀-groups and arrows). */
function binderNames(prettyType: string): Set<string> {
  const names = new Set<string>();
  let rest = prettyType.trim();
  for (;;) {
    while (rest.startsWith('∀')) {
      const comma = splitTopLevel(rest, ', ');
      if (!comma) break;
      for (const g of comma[0].slice(1).matchAll(/[({[⦃]([^:()[\]{}⦃⦄]*):/g)) {
        for (const n of g[1].trim().split(/\s+/)) if (n) names.add(n);
      }
      rest = comma[1].trim();
    }
    const split = splitTopLevel(rest, ' → ');
    if (!split) break;
    const binder = asBinderGroup(split[0]);
    if (binder) for (const n of binder.names) names.add(n);
    rest = split[1].trim();
  }
  return names;
}

/**
 * Is this lemma a STRUCTURAL move rather than a specific fact?
 *
 * `leLtTrans : (a b c : ℝ) → a ≤ b → b < c → a < c` concludes `a < c` — built
 * only from its own binders, so it fits ANY `<` goal. `zeroLtTwo : 0 < 2` fits
 * exactly one.
 *
 * The distinction matters because ranking by token overlap systematically
 * buries the general ones: a conclusion made of bound variables shares almost
 * nothing with a concrete goal, so transitivity loses to every lemma that
 * happens to mention a `0`. Those are the moves a user reaches for when the
 * direct lemma isn't what they want, so a few slots are held for them.
 */
function isStructural(prettyType: string): boolean {
  const conclusion = conclusionOf(prettyType);
  // A concrete NUMERAL makes the conclusion specific: `divPos`'s `0 < a / b` is
  // about zero, not about any two terms, even though its variables are bound.
  if (/\d/.test(conclusion)) return false;
  const binders = binderNames(prettyType);
  const idents = [...conclusion.matchAll(/[A-Za-z_α-ωΑ-Ω][A-Za-z0-9_'α-ωΑ-Ω]*/g)].map((m) => m[0]);
  return idents.length > 0 && idents.every((id) => binders.has(id));
}

/** Slots held for structural moves, so they are always reachable. */
const STRUCTURAL_SLOTS = 3;

/**
 * File lemmas whose CONCLUSION is shaped like the goal — candidates for
 * `apply <name>` (the core-Lean stand-in for `apply?`, which found nothing
 * useful here: Lean's built-in search struggles with the presets' Type-valued
 * relations). Same head operator as the goal, ranked by token overlap of the
 * conclusion, capped. Validation trials drop the ones that don't unify.
 */
export function applyCandidates(
  declarations: readonly LeanDeclaration[],
  goalText: string,
  currentDeclName?: string,
  cap = 8,
): string[] {
  const target = targetOfGoalText(goalText);
  const goalHead = headOp(target);
  if (!goalHead) return [];
  const goalTokens = tokens(target);
  const scored: Array<{ name: string; score: number; structural: boolean }> = [];
  for (const d of declarations) {
    if (d.name === currentDeclName) continue;
    if (d.kind !== 'def' && d.kind !== 'theorem') continue;
    const concl = conclusionOf(d.prettyType);
    if (headOp(concl) !== goalHead) continue;
    let score = 0;
    for (const t of tokens(concl)) if (goalTokens.has(t)) score++;
    scored.push({ name: d.name, score, structural: isStructural(d.prettyType) });
  }
  scored.sort((a, b) => b.score - a.score);

  // Best matches first — but keep a few slots for the structural moves, which
  // score near zero by construction and would otherwise never be offered.
  const picked = scored.slice(0, cap);
  const have = new Set(picked.map((p) => p.name));
  const missing = STRUCTURAL_SLOTS - picked.filter((p) => p.structural).length;
  if (missing > 0) {
    const extras = scored.filter((p) => p.structural && !have.has(p.name)).slice(0, missing);
    for (const extra of extras) {
      // Displace the lowest-scoring NON-structural pick, never another
      // structural one.
      for (let i = picked.length - 1; i >= 0; i--) {
        if (!picked[i].structural) {
          picked.splice(i, 1);
          break;
        }
      }
      picked.push(extra);
    }
    picked.sort((a, b) => b.score - a.score);
  }
  return picked.map((s) => s.name);
}

/**
 * Order candidates by descending token overlap between their LHS and the goal,
 * then cap. Candidates sharing more symbols with the goal are likelier to fire.
 */
export function rankByGoalOverlap(
  candidates: readonly RewriteCandidate[],
  goalText: string,
  cap = 12,
): RewriteCandidate[] {
  const target = targetOfGoalText(goalText);
  const goalTokens = tokens(target);
  const goalHead = headOp(target);
  const scored = candidates.map((c) => {
    const lt = tokens(c.lhs);
    let overlap = 0;
    for (const t of lt) if (goalTokens.has(t)) overlap++;
    // A lemma whose LHS is shaped like the goal/focus (same head operator) is
    // highly relevant even with little token overlap (e.g. `mulComm`'s `n * m`
    // vs a `*`-headed focus) — boost it well above token ties.
    const headMatch = goalHead !== null && headOp(c.lhs) === goalHead;
    return { c, score: overlap + (headMatch ? 100 : 0), keep: overlap > 0 || headMatch };
  });
  scored.sort((a, b) => b.score - a.score);
  return scored.filter((s) => s.keep).slice(0, cap).map((s) => s.c);
}
