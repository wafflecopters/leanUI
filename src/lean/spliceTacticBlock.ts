import type { LeanDeclaration } from './types';

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
  const endIdx = nextDeclLine !== undefined ? Math.min(lines.length, nextDeclLine - 1) : lines.length;
  if (startIdx >= lines.length) return source;

  const before = lines.slice(0, startIdx);
  const region = lines.slice(startIdx, endIdx);
  const after = lines.slice(endIdx);

  const joined = region.join('\n');
  const byMatch = joined.match(/:=\s*by\b/);
  if (!byMatch || byMatch.index === undefined) return source;

  // Keep everything up to and including `by`; drop a trailing inline tactic on
  // that line and everything after, then append the new block on fresh lines.
  const head = joined.slice(0, byMatch.index + byMatch[0].length);
  // `head` ends at `by`; ensure the inline-proof remainder of that line is gone.
  const headFirstLineEnd = head.length;
  // (head already stops right after `by`, so the rest of that physical line is
  // part of `joined` after byMatch — which we intentionally discard.)
  void headFirstLineEnd;

  const rebuiltRegion = `${head}\n${newBlock}`;
  return [...before, rebuiltRegion, ...after].join('\n');
}
