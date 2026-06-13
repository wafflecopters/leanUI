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

/** Keep only identifier-safe characters; fall back to the default name. */
function sanitizeName(name: string | undefined): string {
  if (!name) return DEFAULT_NAME;
  const cleaned = name.replace(/[^A-Za-z0-9_']/g, '_');
  return /^[A-Za-z_]/.test(cleaned) ? cleaned : DEFAULT_NAME;
}
