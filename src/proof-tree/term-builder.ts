/**
 * Term Builder — compute argument slots for interactive term construction.
 *
 * Given a function name and pre-filled args, determines which arguments
 * remain as holes, what their expected types are, and which context
 * hypotheses could fill each slot.
 */

import { TTKTerm, TTKContext } from '../compiler/kernel';
import { DefinitionsMap, createNamedArgLookup } from '../compiler/term';
import { whnf } from '../compiler/whnf';
import { subst } from '../compiler/subst';
import { TacticEngine } from '../tactics/tacticsEngine';
import { ReverseRegistry } from '../math-editor/tt-to-math';
import { renderSubtermLatex } from './goal-computation';

// ============================================================================
// Types
// ============================================================================

export interface TermSlot {
  /** 0-based index in the full arg list (including implicits). */
  readonly index: number;
  /** Binder name from the Pi type (e.g., "ε", "h"). */
  readonly name: string;
  /** Expected type for this slot (kernel term). */
  readonly type: TTKTerm;
  /** LaTeX rendering of the expected type. */
  readonly typeLatex: string;
  /** Whether this arg is implicit ({} braces in the definition). */
  readonly implicit: boolean;
  /** Filled value, or null = hole. */
  value: TTKTerm | null;
  /** LaTeX rendering of the filled value. */
  valueLatex?: string;
}

export interface TermBuilderState {
  /** The function being applied (Const name). */
  readonly fnName: string;
  /** Display name for the function. */
  readonly fnDisplayName: string;
  /** All argument slots (implicit + explicit). */
  readonly slots: TermSlot[];
  /** Context hypotheses that could fill each slot. */
  readonly slotSuggestions: Map<number, string[]>;
  /** The return type after all args are applied. */
  readonly returnTypeLatex?: string;
}

// ============================================================================
// Slot computation
// ============================================================================

/**
 * Compute argument slots for a function application.
 *
 * @param fnName - The function name (e.g., "Limit.eps_delta")
 * @param prefilled - Map from arg index to pre-filled kernel term
 * @param engine - Tactic engine for type inference context
 * @param goal - Current goal (provides context)
 * @param definitions - For looking up the function's type
 * @param rev - For LaTeX rendering
 */
export function computeTermSlots(
  fnName: string,
  prefilled: Map<number, TTKTerm>,
  _engine: TacticEngine,
  goal: { ctx: TTKContext; type: TTKTerm },
  definitions: DefinitionsMap,
  rev?: ReverseRegistry,
): TermBuilderState | null {
  // Look up the function's type
  const termDef = definitions.terms.get(fnName);
  const inductiveCtors = definitions.inductiveTypes;
  let fnType: TTKTerm | undefined;

  if (termDef?.type) {
    fnType = termDef.type;
  } else {
    // Check constructors
    for (const [, indDef] of inductiveCtors) {
      for (const ctor of indDef.constructors) {
        if (ctor.name === fnName) { fnType = ctor.type; break; }
      }
      if (fnType) break;
    }
  }

  if (!fnType) return null;

  // Determine implicit args
  const namedArgLookup = createNamedArgLookup(definitions);
  const namedArgMap = namedArgLookup(fnName);
  const numImplicit = namedArgMap?.size ?? 0;

  // Unwrap Pi types to get each arg's name, type, and implicit status
  const slots: TermSlot[] = [];
  let currentType = fnType;
  let argIndex = 0;

  while (currentType.tag === 'Binder' && currentType.binderKind.tag === 'BPi') {
    const isImplicit = argIndex < numImplicit;
    const name = currentType.name || `_arg${argIndex}`;
    const domain = currentType.domain;

    // Render the domain type as LaTeX
    const typeLatex = rev
      ? renderSubtermLatex(domain, goal.ctx, definitions, rev)
      : name;

    const prefilledValue = prefilled.get(argIndex) ?? null;

    // Render the pre-filled value as LaTeX
    let valueLatex: string | undefined;
    if (prefilledValue && rev) {
      try {
        valueLatex = renderSubtermLatex(prefilledValue, goal.ctx, definitions, rev);
      } catch { /* ignore render errors */ }
    }

    slots.push({
      index: argIndex,
      name,
      type: domain,
      typeLatex,
      implicit: isImplicit,
      value: prefilledValue,
      valueLatex,
    });

    // Substitute the arg (or a placeholder) into the body for subsequent arg types
    const argTerm = prefilledValue ?? { tag: 'Hole' as const, id: `_slot_${argIndex}` };
    currentType = subst(0, argTerm, currentType.body);
    argIndex++;
  }

  // Compute return type
  let returnTypeLatex: string | undefined;
  if (rev) {
    try {
      returnTypeLatex = renderSubtermLatex(currentType, goal.ctx, definitions, rev);
    } catch { /* ignore */ }
  }

  // Compute slot suggestions: for each unfilled explicit slot, find matching hypotheses
  const slotSuggestions = new Map<number, string[]>();
  for (const slot of slots) {
    if (slot.implicit || slot.value !== null) continue;
    const matches: string[] = [];
    // Simple heuristic: check if hypothesis type head matches slot type head
    for (let i = 0; i < goal.ctx.length; i++) {
      const entry = goal.ctx[i];
      if (entry.name.startsWith('_')) continue; // skip internal names
      // Rough match: just offer all hypotheses for now
      // A proper implementation would unify, but that's expensive
      matches.push(entry.name);
    }
    if (matches.length > 0) {
      slotSuggestions.set(slot.index, matches);
    }
  }

  // Display name: strip type prefix for projections
  const dotIdx = fnName.lastIndexOf('.');
  const fnDisplayName = dotIdx >= 0 ? fnName : fnName;

  return {
    fnName,
    fnDisplayName,
    slots,
    slotSuggestions,
    returnTypeLatex,
  };
}

/**
 * Build the final TTKTerm from filled slots.
 * Returns null if any explicit slot is unfilled.
 */
export function buildTermFromSlots(
  fnName: string,
  slots: readonly TermSlot[],
): TTKTerm | null {
  let term: TTKTerm = { tag: 'Const', name: fnName };
  for (const slot of slots) {
    if (slot.value === null) {
      if (!slot.implicit) return null; // unfilled explicit slot
      // Unfilled implicit → insert hole
      term = { tag: 'App', fn: term, arg: { tag: 'Hole', id: `_implicit_${slot.name}` } };
    } else {
      term = { tag: 'App', fn: term, arg: slot.value };
    }
  }
  return term;
}
