/**
 * A lemma's doc comment IS its citation.
 *
 * The prose renders justifications as "by <doc>" — "This holds by transitivity.",
 * "Observe that h by the triangle inequality." So a doc has to be a short noun
 * phrase that reads after the word "by". The rule was written at the top of
 * presets.ts and then not followed: the Group Theory preset shipped with
 * "in a saturated set, the part lying in gH is ALL of gH — order H many",
 * which rendered as the ungrammatical "by in a saturated set, …", and
 * "a list is empty or has a member" → "by a list is empty or has a member".
 *
 * Explanatory sentences are not banned — they just belong in an ordinary `--`
 * comment above the declaration, where they cost the reader nothing. This test
 * is the enforcement the comment lacked.
 */
import { describe, expect, test } from 'vitest';
import { LEAN_PRESETS } from './presets';

interface Doc {
  readonly preset: string;
  readonly text: string;
}

function allDocs(): Doc[] {
  const out: Doc[] = [];
  for (const p of LEAN_PRESETS) {
    for (const m of p.code.matchAll(/\/--([\s\S]*?)-\//g)) {
      out.push({ preset: p.name, text: m[1].trim().replace(/\s+/g, ' ') });
    }
  }
  return out;
}

/** Why this doc would read badly after "by", or null when it reads fine. */
function styleComplaint(text: string): string | null {
  if (/[,;:]/.test(text)) return 'contains , ; or : — the sentence shatters after "by"';
  if (/\b(is|are|was|were|has|have|does|do|will|can|it)\b/.test(text)) {
    return 'reads as a sentence, not a noun phrase';
  }
  if (text.length > 60) return `too long to sit inline (${text.length} chars)`;
  if (/^[A-Z]{2,}/.test(text)) return 'SHOUTS — it is prose in the document, not a banner';
  return null;
}

describe('preset doc comments read as citations', () => {
  test('there are docs to check', () => {
    expect(allDocs().length).toBeGreaterThan(50);
  });

  test('every doc is a noun phrase that reads after "by"', () => {
    const bad = allDocs()
      .map((d) => ({ ...d, why: styleComplaint(d.text) }))
      .filter((d) => d.why !== null)
      .map((d) => `[${d.preset}] "${d.text}" — ${d.why}`);
    expect(bad).toEqual([]);
  });

  test('the complaint function actually catches the shapes that shipped', () => {
    // Guard against the check silently going toothless.
    expect(styleComplaint('in a saturated set, the part lying in gH is ALL of gH')).toBeTruthy();
    expect(styleComplaint('a list is empty or has a member')).toBeTruthy();
    expect(styleComplaint('LAGRANGE: the order of a subgroup divides the order')).toBeTruthy();
    // …and passes the ones that read correctly.
    expect(styleComplaint('totality of ≤')).toBeNull();
    expect(styleComplaint('the triangle inequality')).toBeNull();
    expect(styleComplaint('the empty-or-inhabited dichotomy')).toBeNull();
  });
});
