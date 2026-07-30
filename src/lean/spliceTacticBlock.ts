import type { LeanDeclaration } from './types';
import { declarationBodyEnd } from './extractTacticBlock';

/**
 * Replace a declaration's tactic block (the text after `:= by`) in the source
 * with a new printed block. The inverse of `extractTacticBlock` — used for
 * write-back: when the user edits a proof structurally in the WYSIWYG, we
 * reprint the proof tree and splice it back into the Monaco source so source and
 * WYSIWYG stay in sync.
 *
 * `newBlock` is the printed tactic block WITHOUT a leading `by` (as produced by
 * proofTreeToLean) — its own indentation is preserved. Returns the full updated
 * source, or the original source unchanged if the declaration has no `by` block.
 *
 * Lines are 1-based (matching LeanDeclaration.line).
 */
export function spliceTacticBlock(
  source: string,
  decl: LeanDeclaration,
  nextDeclLine: number | undefined,
  newBlock: string,
): string {
  const lines = source.split('\n');
  const startIdx = Math.max(0, decl.line - 1);
  const windowEnd = nextDeclLine !== undefined ? Math.min(lines.length, nextDeclLine - 1) : lines.length;
  if (startIdx >= lines.length) return source;

  // Find the `:=` marker within the window, then stop at the END OF THIS
  // DECLARATION rather than at the next one — anything after (a comment
  // introducing the next declaration, blank lines) is not ours to overwrite.
  const windowText = lines.slice(startIdx, windowEnd).join('\n');
  const marker = windowText.match(/:=\s*by\b/) ?? windowText.match(/:=/);
  if (!marker || marker.index === undefined) return source;
  const markerLine = startIdx + windowText.slice(0, marker.index).split('\n').length - 1;
  const endIdx = declarationBodyEnd(lines, markerLine, windowEnd);

  const before = lines.slice(0, startIdx);
  const region = lines.slice(startIdx, endIdx);
  const after = lines.slice(endIdx);

  const joined = region.join('\n');

  // Prefer an existing `:= by` (keep through `by`). Otherwise, for a term body
  // `:= <term>` (e.g. `:= sorry`), splice at `:=` and introduce a `by` block —
  // so a def/example built into a proof writes back as `:= by <block>`.
  const byMatch = joined.match(/:=\s*by\b/);
  let head: string;
  if (byMatch && byMatch.index !== undefined) {
    head = joined.slice(0, byMatch.index + byMatch[0].length);
  } else {
    const assignMatch = joined.match(/:=/);
    if (!assignMatch || assignMatch.index === undefined) return source;
    head = joined.slice(0, assignMatch.index + assignMatch[0].length) + ' by';
  }

  const rebuiltRegion = `${head}\n${newBlock}`;
  return [...before, rebuiltRegion, ...after].join('\n');
}
