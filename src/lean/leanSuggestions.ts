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
  kind: 'exact' | 'apply' | 'rw' | 'simp';
}

/** Discovery tactics we try at a hole, in priority order (cheapest/most-closing first). */
export const DISCOVERY_TACTICS: ReadonlyArray<{ kind: LeanSuggestion['kind']; tactic: string }> = [
  { kind: 'exact', tactic: 'exact?' },
  { kind: 'simp', tactic: 'simp?' },
  { kind: 'apply', tactic: 'apply?' },
  { kind: 'rw', tactic: 'rw?' },
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
    return [
      { id: `lean-induction:${t}`, label: `induction ${t}`, tactic: withHoles('induction'), kind: 'apply' },
      { id: `lean-cases:${t}`, label: `cases ${t}`, tactic: withHoles('cases'), kind: 'apply' },
    ];
  }
  return [];
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
