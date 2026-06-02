import type { LeanDeclaration } from './types';

/**
 * Slice a declaration's tactic block (the text after `:= by`) out of the source.
 *
 * Used to seed the structured editor from the user's actual proof. A declaration
 * spans from its start line up to the next declaration's start line; within that
 * window we find `:= by` and return the dedented remainder (the tactic block).
 *
 * Returns null when the declaration has no `by` block (term-mode def, inductive).
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
