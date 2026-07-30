/**
 * The term builder's view model and its engine seam.
 *
 * "Building a term" is filling in a function's argument slots one at a time —
 * `limF.eps_delta □ □` — with the editor showing each slot's type and which
 * hypotheses fit it. That interaction is engine-agnostic; only the thing that
 * ANSWERS "what are the slots, and does this value fit?" is backend-specific.
 *
 * M5 deleted the TT implementation of that answer. The Lean one lives in
 * `src/controller/termBuilder.ts`, which probes `have leanuiProbe := <fn> <args>`
 * round-trips. The view (`TermBuilderView`) never knew the difference.
 */

export interface TermBuilderDisplaySlot {
  readonly index: number;
  readonly name: string;
  readonly typeLatex: string;
  readonly implicit: boolean;
  /** Filled marker — any non-null value means this slot is supplied. */
  value: unknown | null;
  sourceExpr?: string;
  valueLatex?: string;
  error?: string;
  /** Plain type text, for slot-suggestion matching. */
  typePlain?: string;
}

export interface TermBuilderDisplay {
  readonly fnDisplayName: string;
  readonly slots: TermBuilderDisplaySlot[];
  readonly slotSuggestions: Map<number, string[]>;
  readonly returnTypeLatex?: string;
}

/**
 * Async engine seam. `fill`/`clear` return the updated display plus the
 * have-expression to write into the proof tree — unfilled slots print as `?_`,
 * which Lean treats as goals, so the have updates live on every fill.
 */
export interface TermBuilderProvider {
  open(haveExpr: string): Promise<TermBuilderDisplay | null>;
  fill(
    display: TermBuilderDisplay,
    slotIndex: number,
    sourceExpr: string,
  ): Promise<{ display: TermBuilderDisplay; expr: string } | null>;
  clear(
    display: TermBuilderDisplay,
    slotIndex: number,
  ): Promise<{ display: TermBuilderDisplay; expr: string } | null>;
  /** Hoist an unfilled slot's obligation into a `have <haveName> : <type>` with
   *  its own proof subtree ABOVE the builder's have, filling the slot with the
   *  name. Synchronous — correct by construction (the new have's type IS the
   *  slot's type), and validated by the normal goal round-trip. */
  hoist?(
    display: TermBuilderDisplay,
    slotIndex: number,
  ): { display: TermBuilderDisplay; expr: string; haveName: string; haveTypeExpr: string } | null;
}
