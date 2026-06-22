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

/** Symbol tokens for overlap ranking; split on `.` so `a.succ`/`n.succ` share `succ`. */
function tokens(s: string): Set<string> {
  const out = new Set<string>();
  for (const m of s.matchAll(/[A-Za-z_][A-Za-z0-9_']*|[+\-*/≤<>∑∏·]/g)) out.add(m[0]);
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
  cap = 20,
): string[] {
  const out: string[] = [];
  for (const d of declarations) {
    if (d.name === currentDeclName) continue;
    if (d.kind !== 'def') continue;
    // Skip noise: auto-generated instances (instOfNat…) and structure
    // projections (Semiring.add) — not useful unfold targets.
    if (d.name.startsWith('inst') || d.name.includes('.')) continue;
    if (splitTopLevel(conclusionOf(d.prettyType), ' = ')) continue; // equality lemma, not an unfold target
    out.push(d.name);
    if (out.length >= cap) break;
  }
  return out;
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
  const goalTokens = tokens(goalText);
  const goalHead = headOp(goalText);
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
