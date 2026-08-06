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

/**
 * Slots held for structural moves, so they are always reachable.
 *
 * Five, not three. A structural lemma's conclusion is made only of ITS OWN
 * bound variables, so token overlap with the goal is close to meaningless —
 * `convertEps : v < ε/2 + ε/2 → v < epsilon` scored zero against a goal saying
 * `ε` rather than `epsilon`, because the only word they could have shared is a
 * name the lemma made up. These lemmas are therefore ranked almost arbitrarily
 * among themselves, and three slots meant the first three won and the rest were
 * unreachable: `convertEps` is the step that turns ε/2 + ε/2 back into ε, and
 * there was no way to reach it from the tray.
 */
const STRUCTURAL_SLOTS = 5;

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
  /** The goal's head CONSTANT, from the elaborator. When present it replaces
   *  the text-derived operator entirely: `0 < x` is `rlt 0 x` whatever notation
   *  renders it as, so `convertEps` — whose binder is spelled `epsilon` while
   *  the goal says `ε` — matches on the thing they actually share. */
  goalHeadConst?: string | null,
): string[] {
  const target = targetOfGoalText(goalText);
  const goalHead = headOp(target);
  const byConst = typeof goalHeadConst === 'string' && goalHeadConst.length > 0;
  if (!byConst && !goalHead) return [];
  const goalTokens = tokens(target);
  const scored: Array<{ name: string; score: number; structural: boolean; leaves: number }> = [];
  for (const d of declarations) {
    if (d.name === currentDeclName) continue;
    if (d.kind !== 'def' && d.kind !== 'theorem') continue;
    const concl = conclusionOf(d.prettyType);
    if (byConst) {
      if (d.conclHead !== goalHeadConst) continue;
    } else if (headOp(concl) !== goalHead) continue;
    let score = 0;
    for (const t of tokens(concl)) if (goalTokens.has(t)) score++;
    scored.push({
      name: d.name,
      score,
      structural: isStructural(d.prettyType),
      // From Lean when it said so; the text estimate only as a fallback.
      leaves: typeof d.premises === 'number' ? d.premises : premiseCount(d.prettyType),
    });
  }
  // NOTE: deliberately NOT tiebroken by `leaves` here. Tried it — preferring
  // the lemma that leaves least looks principled, but applied to the main sort
  // it pushed `ltMin` (two premises, and exactly the right move) off the tray
  // at `0 < rmin deltaF deltaG` to make room for one-premise lemmas that don't
  // apply. The tiebreak only pays off among the leftovers, below.
  scored.sort((a, b) => b.score - a.score);

  // Best matches first — but keep a few slots for the structural moves, which
  // score near zero by construction and would otherwise never be offered.
  const picked = scored.slice(0, cap);
  const have = new Set(picked.map((p) => p.name));
  const missing = STRUCTURAL_SLOTS - picked.filter((p) => p.structural).length;
  if (missing > 0) {
    // Among structural lemmas there is nothing to rank BY: their conclusions
    // are made of their own bound variables, so overlap with the goal is near
    // zero for all of them and the order is whatever the file happened to be
    // in. `convertEps` — the step that turns ε/2 + ε/2 back into ε — sat around
    // 25th and was unreachable for that reason alone.
    //
    // So prefer the one that LEAVES THE LEAST: a lemma with a single premise is
    // a better opening guess than one that also asks you to invent a midpoint.
    // It is a tiebreak, not a claim about which is right — validation still
    // decides, and the cheap ones are simply worth asking about first.
    const extras = scored
      .filter((p) => p.structural && !have.has(p.name))
      .sort((a, b) => a.leaves - b.leaves)
      .slice(0, missing);
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

// ── comparing two values ────────────────────────────────────────────────────

/** A "compare these two" move: `cases <lemma> <a> <b>`. */
export interface ComparisonSplit {
  readonly lemma: string;
  readonly left: string;
  readonly right: string;
}

/**
 * The explicit binder groups and ordinary premises of a function type, in order.
 */
function binderShape(prettyType: string): {
  explicitGroups: Array<{ names: string[]; type: string }>;
  hasPremise: boolean;
} {
  let rest = stripForall(prettyType);
  const explicitGroups: Array<{ names: string[]; type: string }> = [];
  let hasPremise = false;
  for (;;) {
    const split = splitTopLevel(rest, ' → ');
    if (!split) break;
    const antecedent = split[0].trim();
    const binder = asBinderGroup(antecedent);
    if (!binder) {
      hasPremise = true;
    } else if (binder.bracket === '(') {
      const inner = antecedent.slice(1, -1);
      const colon = splitTopLevel(inner, ' : ');
      explicitGroups.push({ names: binder.names, type: (colon?.[1] ?? '').trim() });
    }
    rest = stripForall(split[1]);
  }
  return { explicitGroups, hasPremise };
}

/** The head constant of an application — `Either (a ≤ b) (b ≤ a)` → `Either`. */
function headConst(s: string): string | null {
  const m = s.trim().match(/^([A-Za-z_][A-Za-z0-9_.'α-ωΑ-Ω]*)/);
  return m ? m[1] : null;
}

/**
 * "Compare these two values" — the move that turns two things in scope into a
 * case split on how they relate.
 *
 * The canonical instance is `leTotal : (a b : ℝ) → Either (a ≤ b) (b ≤ a)`,
 * which is how you get from two deltas to a single one: compare them, and in
 * each branch you know which is smaller. But nothing here knows about `leTotal`,
 * ordering, or the reals. The SHAPE is the signal — a lemma that takes exactly
 * two explicit arguments of one type, asks for nothing else, and returns a value
 * of an inductive type declared in the file. `cases`-ing that value splits the
 * proof into the ways those two can relate, whatever the relation is.
 *
 * Pairs are offered MOST-RECENT-FIRST, because the values you just introduced
 * are the ones you are working with: at the point where `deltaF` and `deltaG`
 * have both been destructured out, they are the last two reals in scope, and
 * `cases leTotal deltaF deltaG` is the first pill — ahead of the five other
 * reals (`x0`, `L`, `M`, `ε`) that have been sitting there since the statement.
 */
export function comparisonCandidates(
  declarations: readonly LeanDeclaration[],
  hypotheses: ReadonlyArray<{ name: string; type: string; typeHead?: string | null }>,
  currentDeclName?: string,
  cap = 3,
): ComparisonSplit[] {
  // The shape, stated as facts: exactly two explicit arguments of ONE type,
  // nothing else asked for, and an inductive result — `cases`-ing that splits
  // the proof into the ways those two can relate. `leTotal` is the instance
  // that matters here; nothing knows its name.
  const byType = new Map<string, string[]>();
  for (const d of declarations) {
    if (d.name === currentDeclName) continue;
    if (d.kind !== 'def' && d.kind !== 'theorem') continue;
    if (!d.conclIsInductive) continue;
    if (d.premises !== 0) continue;
    const args = d.argHeads;
    if (!args || args.length !== 2) continue;
    const [a, b] = args;
    if (!a || a !== b) continue;
    byType.set(a, [...(byType.get(a) ?? []), d.name]);
  }
  if (byType.size === 0) return [];

  const out: ComparisonSplit[] = [];
  for (const [type, lemmas] of byType) {
    const named = hypotheses
      .map((h, index) => ({ ...h, index }))
      .filter((h) => h.typeHead === type);
    const pairs: Array<{ left: string; right: string; rank: number }> = [];
    for (let j2 = 1; j2 < named.length; j2++) {
      for (let i2 = 0; i2 < j2; i2++) {
        // Rank by how recently the LATER of the two appeared: the values you
        // just introduced are the ones the proof is about.
        pairs.push({ left: named[i2].name, right: named[j2].name, rank: named[j2].index * 1000 + named[i2].index });
      }
    }
    pairs.sort((a, b) => b.rank - a.rank);
    for (const p of pairs) for (const lemma of lemmas) out.push({ lemma, left: p.left, right: p.right });
  }
  return out.slice(0, cap);
}

// ── choosing a value ────────────────────────────────────────────────────────

/**
 * The EXPLICIT argument types of a function type, in order, plus its conclusion.
 *
 * Handles both spellings Lean prints: named groups (`(a b : ℝ) → …`) and bare
 * arrows (`ℝ → ℝ → ℝ`, which is how `rmin` prints). Implicit `{…}` and instance
 * `[…]` binders are skipped — Lean infers them.
 */
function explicitArgTypes(prettyType: string): { args: string[]; conclusion: string } {
  let rest = stripForall(prettyType);
  const args: string[] = [];
  for (;;) {
    const split = splitTopLevel(rest, ' → ');
    if (!split) break;
    const antecedent = split[0].trim();
    const binder = asBinderGroup(antecedent);
    if (!binder) {
      args.push(antecedent); // bare arrow argument
    } else if (binder.bracket === '(') {
      const colon = splitTopLevel(antecedent.slice(1, -1), ' : ');
      const type = (colon?.[1] ?? '').trim();
      for (let i = 0; i < binder.names.length; i++) args.push(type);
    }
    rest = stripForall(split[1]);
  }
  return { args, conclusion: rest.trim() };
}

/**
 * What you could PUT in a value goal.
 *
 * `⊢ ℝ` is not a claim to prove, it's a blank to fill — the δ of an ε-δ proof,
 * the midpoint of a transitivity. Lean's own search is no help here: every real
 * number type-checks, so `exact?` answers with whatever it finds first (it
 * offered `f (f (f (f x0))) / f (f (f (f x0)))`) and `assumption` silently
 * grabs an arbitrary hypothesis. Neither is a choice the reader can follow.
 *
 * So offer the choices explicitly: the values of that type already in scope,
 * and the one-step ways to COMBINE them using the file's own operations on that
 * type — which is where `rmin deltaF deltaG` comes from, the δ that makes an
 * ε-δ sum proof work. Most-recent-first, because the values you just introduced
 * are the ones the proof is about.
 *
 * Validation can't rank these: they all type-check, and which one works depends
 * on a SIBLING goal. That's the point — this is the step where the human
 * chooses, and the editor's job is to lay out the options, not to guess.
 */
export function valueCandidates(
  declarations: readonly LeanDeclaration[],
  goalTypeHead: string | null | undefined,
  hypotheses: ReadonlyArray<{ name: string; type: string; typeHead?: string | null }>,
  currentDeclName?: string,
  cap = 10,
): string[] {
  if (!goalTypeHead) return [];

  // In-scope values of the goal's type, most recent first.
  const inScope = hypotheses
    .map((h, index) => ({ ...h, index }))
    .filter((h) => h.typeHead === goalTypeHead)
    .sort((a, b) => b.index - a.index)
    .map((h) => h.name);
  if (inScope.length === 0) return [];
  // The two most recent, back in SCOPE order — `rmin deltaF deltaG` reads the
  // way the context does, not backwards.
  const recent = inScope.slice(0, 2).reverse();

  // The file's own operations ON this type: every explicit argument and the
  // result are the goal's type. `rmin`, `radd`, `rneg` qualify; `rlt` (returns
  // a proposition) and `realOfRat` (takes something else) do not — decided by
  // comparing CONSTANTS, not by comparing rendered type text.
  const ops: Array<{ name: string; arity: number }> = [];
  for (const d of declarations) {
    if (d.name === currentDeclName) continue;
    if (d.kind !== 'def' && d.kind !== 'theorem') continue;
    if (d.conclHead !== goalTypeHead) continue;
    const args = d.argHeads;
    if (!args || args.length < 1 || args.length > 2) continue;
    if (!args.every((a) => a === goalTypeHead)) continue;
    ops.push({ name: d.name, arity: args.length });
  }

  // Bare values are capped so the COMBINATIONS get room: a context can hold a
  // half-dozen reals, and listing all of them would crowd out `rmin deltaF
  // deltaG` — the answer here, and never a bare hypothesis.
  const BARE_CAP = 4;
  const binary = ops.filter((o) => o.arity === 2);
  const unary = ops.filter((o) => o.arity === 1);
  const [a, b] = recent;
  return [
    ...inScope.slice(0, BARE_CAP),
    ...(b !== undefined ? binary.map((o) => `${o.name} ${a} ${b}`) : []),
    ...unary.map((o) => `${o.name} ${inScope[0]}`),
  ].slice(0, cap);
}
