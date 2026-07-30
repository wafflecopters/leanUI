import type { LeanDeclaration } from './types';

/**
 * Slice a declaration's PROOF/body for the structured editor — the text after
 * `:= by` as a tactic block.
 *
 * A declaration spans from its start line to the next declaration's; within that
 * window we find `:= by` and return the dedented tactic block.
 *
 * Returns null when there's no `by` block. (Callers that want to prove a
 * `:= <term>` / `:= sorry` body interactively should fall back to a `sorry`
 * seed — see `bodyIsProvable`.)
 * Lines are 1-based (matching LeanDeclaration.line).
 */
export function extractTacticBlock(
  source: string,
  decl: LeanDeclaration,
  nextDeclLine: number | undefined,
): string | null {
  const lines = source.split('\n');
  const startIdx = Math.max(0, decl.line - 1);
  const endIdx = nextDeclLine !== undefined ? Math.min(lines.length, nextDeclLine - 1) : lines.length;
  if (startIdx >= lines.length) return null;

  const region = lines.slice(startIdx, endIdx);
  const joined = region.join('\n');

  // Find `:= by` (the tactic-mode marker). Accept `by` at end of a line or
  // inline followed by tactics.
  const byMatch = joined.match(/:=\s*by\b/);
  if (!byMatch || byMatch.index === undefined) return null;

  const afterBy = joined.slice(byMatch.index + byMatch[0].length);

  // Inline form: `:= by <tactic>` on one line (no newline before tactics).
  // Return just the tactic, trimmed of the leading space after `by`.
  const firstNl = afterBy.indexOf('\n');
  const firstSegment = (firstNl === -1 ? afterBy : afterBy.slice(0, firstNl)).trim();
  if (firstSegment.length > 0) {
    // There may also be following indented lines; include them verbatim.
    const rest = firstNl === -1 ? '' : afterBy.slice(firstNl);
    const combined = (firstSegment + rest).replace(/\s+$/, '');
    return combined.length > 0 ? combined : null;
  }

  // Block form: tactics start on the next line(s); keep them verbatim
  // (indentation matters for the parser).
  const block = afterBy.replace(/^\n+/, '').replace(/\s+$/, '');
  return block.trim().length === 0 ? null : block;
}

/** Does the declaration's body region literally contain `:= sorry`? */
function bodyIsSorry(source: string, decl: LeanDeclaration, nextDeclLine: number | undefined): boolean {
  const lines = source.split('\n');
  const startIdx = Math.max(0, decl.line - 1);
  const endIdx = nextDeclLine !== undefined ? Math.min(lines.length, nextDeclLine - 1) : lines.length;
  const region = lines.slice(startIdx, endIdx).join('\n');
  return /:=\s*sorry\b/.test(region);
}

/**
 * The proof block to seed the structured editor with, or null if the decl has no
 * interactive proof body. Rules:
 *   - has a `:= by` block  → that block (theorem OR def written in tactic mode)
 *   - `theorem … := <term>` → seed `sorry` (build the proof structurally)
 *   - any `… := sorry`      → seed `sorry` (clearly wants a proof)
 *   - computational `def := <term>` (no sorry) → null (use the value editor)
 *   - inductive/axiom/opaque → null
 */
export function proofSeedBlock(
  source: string,
  decl: LeanDeclaration,
  nextDeclLine: number | undefined,
): string | null {
  const block = extractTacticBlock(source, decl, nextDeclLine);
  if (block !== null) return block;
  if (decl.kind === 'theorem') return 'sorry';
  if (decl.kind === 'def' && bodyIsSorry(source, decl, nextDeclLine)) return 'sorry';
  return null;
}
