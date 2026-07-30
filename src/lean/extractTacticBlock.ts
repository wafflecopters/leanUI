import type { LeanDeclaration } from './types';

/**
 * Where a declaration's BODY stops, inside the window that runs to the next
 * declaration's line.
 *
 * The window is not the body: a top-level comment introducing the NEXT
 * declaration sits inside it, and so does any blank space between the two. A
 * tactic block is always indented under its `by`, so the first non-blank line
 * back at column 0 is where this declaration ends and the next one's preamble
 * begins.
 *
 * Both directions need the same answer, or they corrupt each other: reading too
 * far seeds the editor with a comment as if it were a tactic, and WRITING too
 * far deletes that comment on the first structural edit.
 *
 * `lines` are the whole file; `searchFrom` is the index of the line holding the
 * `:=` marker (its own indentation is the declaration's, so scanning starts
 * after it). Returns an exclusive end index.
 */
export function declarationBodyEnd(
  lines: readonly string[],
  searchFrom: number,
  windowEnd: number,
): number {
  let end = windowEnd;
  for (let i = searchFrom + 1; i < windowEnd; i++) {
    const line = lines[i];
    if (line.trim().length === 0) continue;
    if (!/^\s/.test(line)) {
      end = i;
      break;
    }
  }
  // Trailing blank lines belong to the gap between declarations, not the body.
  while (end > searchFrom + 1 && lines[end - 1].trim().length === 0) end--;
  return end;
}

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
  const windowEnd = nextDeclLine !== undefined ? Math.min(lines.length, nextDeclLine - 1) : lines.length;
  if (startIdx >= lines.length) return null;

  // Locate `:= by` first, so the body scan can start from the line holding it.
  const windowText = lines.slice(startIdx, windowEnd).join('\n');
  const byIdx = windowText.match(/:=\s*by\b/)?.index;
  if (byIdx === undefined) return null;
  const markerLine = startIdx + windowText.slice(0, byIdx).split('\n').length - 1;
  const endIdx = declarationBodyEnd(lines, markerLine, windowEnd);

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
