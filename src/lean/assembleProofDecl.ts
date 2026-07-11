/**
 * Assemble a complete Lean declaration from a proof tree, for goal computation.
 *
 * The structured editor owns a declaration's type and its proof tree. To get
 * Lean's goal state at each proof step, we emit a self-contained theorem:
 *
 *     <preamble>            -- imports + any context decls the proof references
 *     theorem <name> : <type> := by
 *       <printed proof block>
 *
 * The type is written WITHOUT signature binders, so the proof tree's leading
 * `intros` are valid tactics (avoids Lean's "introN failed: no additional
 * binders"; see LEAN_WYSIWYG_PORT.md). We compute the absolute base line of the
 * first tactic so `proofTreeToLean`'s node ranges line up with what Lean reports.
 */
import type { ProofNode, ProofNodeId } from '../proof-tree/proof-tree';
import { proofTreeToLean, type ProofTreeLean } from './proofTreeToLean';

export interface AssembleInput {
  /** Theorem name (defaults to a safe placeholder). */
  name?: string;
  /** The declaration's type as Lean source (e.g. "∀ (a b : Nat), a + b = b + a"). */
  typeSource: string;
  /** The proof tree to elaborate. */
  proof: ProofNode;
  /**
   * Lines prepended before the theorem (imports, supporting declarations the
   * proof references). Each entry is a source line. The proof block's line
   * numbers are offset past these.
   */
  preamble?: string[];
  /**
   * For suggestion discovery: emit this tactic in place of the given hole's
   * `sorry` (e.g. `exact?`), so Lean reports its `Try this:` at that range.
   */
  holeOverrideId?: ProofNodeId;
  holeOverrideTactic?: string;
}

export interface AssembledProof {
  /** Full Lean source to send to the analyzer. */
  source: string;
  /** Node ranges + holes, with line numbers absolute in `source`. */
  lean: ProofTreeLean;
  /** Prefix/body split for the server's prefix-olean fast path: `prefixSource`
   *  is the UNCHANGED text before the decl (compiled once server-side),
   *  `bodySource` the decl with the spliced proof. `source` === prefix+\n+body.
   *  Absent for the standalone (assembleProofDecl) form. */
  prefixSource?: string;
  bodySource?: string;
}

/** Default theorem name when none supplied (kept identifier-safe). */
const DEFAULT_NAME = '_leanui_goal';

export function assembleProofDecl(input: AssembleInput): AssembledProof {
  const name = sanitizeName(input.name);
  const preamble = input.preamble ?? [];
  const header = `theorem ${name} : ${input.typeSource.trim()} := by`;

  // The first tactic line sits right after the preamble + header.
  // Lines are 1-based: preamble occupies lines 1..N, header is N+1,
  // so the first tactic is at N+2.
  const baseLine = preamble.length + 2;
  const lean = proofTreeToLean(input.proof, baseLine, /* baseDepth */ 1, {
    holeOverrideId: input.holeOverrideId,
    holeOverrideTactic: input.holeOverrideTactic,
  });

  const source = [...preamble, header, lean.source, ''].join('\n');
  return { source, lean };
}

/**
 * Assemble the proof IN the real source file — the correct way to compute goals
 * for a declaration whose type references earlier defs (so they're in scope).
 *
 * Splices the printed proof block into `decl`'s `:= by` (replacing its body) in
 * the full `source`, keeping every other declaration intact as context. Returns
 * the spliced full source plus per-node ranges with ABSOLUTE line numbers (so
 * `mapLeanGoalsToNodes` matches Lean's reported goal ranges).
 */
export interface AssembleInSourceInput {
  source: string;
  decl: { line: number };
  nextDeclLine: number | undefined;
  proof: ProofNode;
  holeOverrideId?: ProofNodeId;
  holeOverrideTactic?: string;
}

export function assembleProofInSource(input: AssembleInSourceInput): AssembledProof {
  const { source, decl, nextDeclLine } = input;
  const lines = source.split('\n');
  const startIdx = Math.max(0, decl.line - 1);
  const endIdx = nextDeclLine !== undefined ? Math.min(lines.length, nextDeclLine - 1) : lines.length;

  // Find `:=` within the declaration's region to locate where the body begins.
  const region = lines.slice(startIdx, endIdx).join('\n');
  const byMatch = region.match(/:=\s*by\b/);
  const assignMatch = region.match(/:=/);
  // Header text (everything up to and including `by`), and which physical line
  // the `by` sits on so we can compute the first tactic's absolute line.
  let headEnd: number;
  if (byMatch && byMatch.index !== undefined) headEnd = byMatch.index + byMatch[0].length;
  else if (assignMatch && assignMatch.index !== undefined) headEnd = assignMatch.index + assignMatch[0].length;
  else {
    // No `:=` — can't host a proof; fall back to standalone (shouldn't happen for provable decls).
    return assembleProofDecl({ typeSource: 'True', proof: input.proof });
  }
  const head = byMatch ? region.slice(0, headEnd) : region.slice(0, headEnd) + ' by';

  // Lines occupied by `head` within the region → first tactic is on the next line.
  const headLineCount = head.split('\n').length; // 1-based count
  const baseLine = startIdx + headLineCount + 1; // absolute 1-based line of first tactic

  const lean = proofTreeToLean(input.proof, baseLine, /* baseDepth */ 1, {
    holeOverrideId: input.holeOverrideId,
    holeOverrideTactic: input.holeOverrideTactic,
  });

  const before = lines.slice(0, startIdx);
  const rebuiltRegion = `${head}\n${lean.source}`;
  // Everything AFTER the declaration's block is dropped: Lean is strictly
  // forward-referencing, so later declarations cannot affect this proof — and
  // every goal/suggestion round-trip re-elaborates the whole file, so a
  // shorter file is directly faster (the heavyweight sections after the
  // current decl never run). Node ranges are unaffected (only later lines go).
  const prefixSource = before.join('\n');
  const bodySource = `${rebuiltRegion}\n`;

  // The prefix/body split lets the server compile the unchanged prefix ONCE
  // (to a .olean) and elaborate only the decl per request. Only offered when
  // there IS a prefix (decl not at the top of the file).
  if (before.length > 0) {
    return { source: `${prefixSource}\n${bodySource}`, lean, prefixSource, bodySource };
  }
  return { source: bodySource, lean };
}

/** Keep only identifier-safe characters; fall back to the default name. */
function sanitizeName(name: string | undefined): string {
  if (!name) return DEFAULT_NAME;
  const cleaned = name.replace(/[^A-Za-z0-9_']/g, '_');
  return /^[A-Za-z_]/.test(cleaned) ? cleaned : DEFAULT_NAME;
}
