/**
 * "Introduce everything at the front of the goal, with names I can use."
 *
 * A goal like
 *
 *     (epsilon : ℝ) → 0 < epsilon → ∃ δ ∈ ℝ, …
 *
 * can't be worked on until its binders are introduced, and typing the names by
 * hand is the first thing a user has to do on every ε-δ proof. This derives
 * them from the goal itself.
 *
 * Naming, and why:
 *
 *   - A NAMED binder keeps its own name. Lean already chose `epsilon`, the math
 *     renderer already shows that as ε, and the proof then reads in the same
 *     letters as the statement.
 *   - An ANONYMOUS antecedent (`0 < epsilon →`) gets `h`, `h1`, `h2`, … Naming
 *     it after its subject (`hepsilon`) reads better in source but renders as
 *     `\operatorname{hepsilon}` — an unreadable blob — whereas `h`/`h1` render
 *     as h, h₁.
 *   - Everything is freshened against the context, so nothing shadows a
 *     hypothesis that is already in scope.
 */
import { parseSlots } from './termSlots';
import { normalizeBinderNameInput } from '../proof-tree/name-latex';

/** Lean's inaccessible-name marker. */
const DAGGER = '✝';

/**
 * A binder Lean spelled out (`epsilon`) written as the letter the editor shows
 * (ε).
 *
 * The renderer displays `epsilon` as ε either way, so the difference only shows
 * up when the user TYPES: after `intro epsilon`, writing `have h : 0 < ε / 2`
 * fails on an unknown identifier, because the thing on screen and the thing in
 * scope have different names. Introducing it as ε makes what you read and what
 * you type the same string. (Greek letters are valid Lean identifiers.)
 */
function preferGreekLetter(name: string): string {
  const letter = normalizeBinderNameInput(`\\${name}`);
  return [...letter].length === 1 ? letter : name;
}

/** A binder name we can actually use: a plain identifier, not `_` or a
 *  dagger-marked inaccessible one. */
function usableName(name: string | undefined): string | null {
  if (!name) return null;
  const cleaned = name.split(DAGGER)[0].trim();
  if (!cleaned || cleaned === '_') return null;
  return /^[A-Za-z_α-ωΑ-Ω][A-Za-z0-9_'α-ωΑ-Ω]*$/.test(cleaned) ? cleaned : null;
}

/** `base`, else `base1`, `base2`, … — whichever is free. */
function fresh(base: string, used: Set<string>): string {
  if (!used.has(base)) {
    used.add(base);
    return base;
  }
  for (let i = 1; ; i++) {
    const candidate = `${base}${i}`;
    if (!used.has(candidate)) {
      used.add(candidate);
      return candidate;
    }
  }
}

/**
 * Names for every binder at the front of `goalText`, in order. Empty when the
 * goal has no leading binders (nothing to introduce).
 *
 * `taken` is the names already in scope — the result never shadows one.
 */
export function introBinderNames(goalText: string, taken: readonly string[] = []): string[] {
  const { slots } = parseSlots(goalText);
  if (slots.length === 0) return [];
  const used = new Set(taken);
  return slots.map((slot) => {
    const named = usableName(slot.name);
    return fresh(named ? preferGreekLetter(named) : 'h', used);
  });
}
