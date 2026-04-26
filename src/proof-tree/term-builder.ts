/**
 * Term Builder — kernel-backed interactive term construction.
 *
 * Uses the tactic engine to create real metavariables for each argument
 * slot, so type checking and inference work correctly. Filling a slot
 * type-checks the value against the slot's expected type.
 */

import { TTKTerm, TTKContext } from '../compiler/kernel';
import { DefinitionsMap, MetaVar, createNamedArgLookup, TCEnv } from '../compiler/term';
import { whnf } from '../compiler/whnf';
import { subst } from '../compiler/subst';
import { inferType, checkType } from '../compiler/checker';
import { TacticEngine } from '../tactics/tacticsEngine';
import { freshMetaName } from '../tactics/tactic';
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
  /** Meta ID for this slot (used to track solutions). */
  readonly metaId: string;
  /** Filled value, or null = hole. */
  value: TTKTerm | null;
  /** Source expression string (for serializing back to have expression). */
  sourceExpr?: string;
  /** LaTeX rendering of the filled value. */
  valueLatex?: string;
  /** Error message if the filled value doesn't type-check. */
  error?: string;
}

export interface TermBuilderState {
  /** The function being applied (Const name). */
  readonly fnName: string;
  /** Display name for the function. */
  readonly fnDisplayName: string;
  /** All argument slots (implicit + explicit). */
  readonly slots: TermSlot[];
  /** Context hypotheses that ACTUALLY type-check for each slot. */
  readonly slotSuggestions: Map<number, string[]>;
  /** The return type after all args are applied. */
  readonly returnTypeLatex?: string;
  /** The engine state with metas for unfilled slots. */
  readonly engine: TacticEngine;
  /** The goal context (for name resolution). */
  readonly goalCtx: TTKContext;
}

// ============================================================================
// Slot computation
// ============================================================================

/**
 * Compute argument slots for a function application using the tactic engine.
 *
 * Creates real metavariables for each argument, so type checking works
 * correctly. Pre-filled args are type-checked against their expected types.
 */
export function computeTermSlots(
  fnName: string,
  prefilled: Map<number, TTKTerm>,
  engine: TacticEngine,
  goal: MetaVar,
  definitions: DefinitionsMap,
  rev?: ReverseRegistry,
  /** Slot indices that were filled by the user (type-check these). */
  userFilledIndices?: Set<number>,
): TermBuilderState | null {
  // Look up the function's type
  let fnType: TTKTerm | undefined;
  const termDef = definitions.terms.get(fnName);
  if (termDef?.type) {
    fnType = termDef.type;
  } else {
    for (const [, indDef] of definitions.inductiveTypes) {
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

  // Auto-fill implicits from the first explicit arg's type
  const firstExplicitVal = prefilled.get(numImplicit);
  if (firstExplicitVal && firstExplicitVal.tag === 'Var') {
    const entryIdx = goal.ctx.length - 1 - firstExplicitVal.index;
    if (entryIdx >= 0 && entryIdx < goal.ctx.length) {
      const hypType = goal.ctx[entryIdx].type;
      const hypTypeWhnf = whnf(hypType, { definitions, typingContext: goal.ctx });
      const typeArgs: TTKTerm[] = [];
      let cur = hypTypeWhnf;
      while (cur.tag === 'App') { typeArgs.unshift(cur.arg); cur = cur.fn; }
      for (let i = 0; i < numImplicit && i < typeArgs.length; i++) {
        if (!prefilled.has(i)) prefilled.set(i, typeArgs[i]);
      }
    }
  }

  // Unwrap Pi types, creating metas for each arg
  const slots: TermSlot[] = [];
  let currentType = fnType;
  let argIndex = 0;
  let currentEngine = engine;

  while (currentType.tag === 'Binder' && currentType.binderKind.tag === 'BPi') {
    const isImplicit = argIndex < numImplicit;
    const name = currentType.name || `_arg${argIndex}`;
    const domain = currentType.domain;

    // Create a meta for this arg
    const metaId = freshMetaName();
    const argMeta: MetaVar = {
      ctx: goal.ctx,
      type: domain,
      solution: undefined,
    };

    // Check if this slot has a pre-filled value
    const prefilledValue = prefilled.get(argIndex) ?? null;
    let value: TTKTerm | null = prefilledValue;
    let error: string | undefined;

    if (prefilledValue) {
      // Type-check user-filled SIMPLE values (Var, Const) against the
      // expected domain. Skip complex expressions (App chains) — the Pi
      // spine's domain types have de Bruijn indices that don't align with
      // goal.ctx after implicit substitution, causing false type errors
      // for complex terms. The have tactic catches real errors at replay.
      if (userFilledIndices?.has(argIndex) && (prefilledValue.tag === 'Var' || prefilledValue.tag === 'Const')) {
        try {
          const checkEnv = new TCEnv(
            goal.ctx, definitions, currentEngine.metaVars,
            currentEngine.constraints, [], [], prefilledValue,
            new Map(), { mode: 'check' },
          );
          checkType(checkEnv, domain);
        } catch (e) {
          error = e instanceof Error
            ? e.message
            : (e && typeof e === 'object' && 'message' in e)
              ? String((e as any).message)
              : String(e);
        }
      }
      const newMetaVars = new Map(currentEngine.metaVars);
      newMetaVars.set(metaId, { ...argMeta, solution: prefilledValue });
      currentEngine = currentEngine.withUpdates({ metaVars: newMetaVars });
    } else {
      // Unfilled — register the unsolved meta
      const newMetaVars = new Map(currentEngine.metaVars);
      newMetaVars.set(metaId, argMeta);
      currentEngine = currentEngine.withUpdates({ metaVars: newMetaVars });
    }

    // Render type and value as LaTeX
    const typeLatex = rev
      ? (() => { try { return renderSubtermLatex(domain, goal.ctx, definitions, rev); } catch { return name; } })()
      : name;

    let valueLatex: string | undefined;
    if (prefilledValue && rev) {
      try { valueLatex = renderSubtermLatex(prefilledValue, goal.ctx, definitions, rev); }
      catch { /* ignore */ }
    }

    slots.push({
      index: argIndex, name, type: domain, typeLatex,
      implicit: isImplicit, metaId,
      value, valueLatex, error,
    });

    // Substitute for next arg's type
    const argTerm = prefilledValue ?? { tag: 'Meta' as const, id: metaId };
    currentType = subst(0, argTerm, currentType.body);
    currentType = whnf(currentType, { definitions, typingContext: goal.ctx });
    argIndex++;
  }

  // Compute return type
  let returnTypeLatex: string | undefined;
  if (rev) {
    try { returnTypeLatex = renderSubtermLatex(currentType, goal.ctx, definitions, rev); }
    catch { /* ignore */ }
  }

  // Compute slot suggestions: for each unfilled explicit slot,
  // find context hypotheses and definitions that could fill it.
  const slotSuggestions = new Map<number, string[]>();
  for (const slot of slots) {
    if (slot.implicit || slot.value !== null) continue;
    const matches: string[] = [];

    // Get the slot type's head for matching
    let slotHead = slot.type;
    while (slotHead.tag === 'App') slotHead = slotHead.fn;
    const slotHeadName = slotHead.tag === 'Const' ? slotHead.name : undefined;

    // 1. Context hypotheses: exact type match (head matches)
    for (let i = 0; i < goal.ctx.length; i++) {
      const entry = goal.ctx[i];
      if (entry.name.startsWith('_')) continue;
      let hypHead = entry.type;
      while (hypHead.tag === 'App') hypHead = hypHead.fn;
      if (slotHeadName && hypHead.tag === 'Const' && hypHead.name === slotHeadName) {
        matches.push(entry.name);
      } else if (!slotHeadName) {
        matches.push(entry.name);
      }
    }

    // 2. Definitions whose RETURN TYPE head matches the slot type.
    // Walk the Pi spine to find the final return type and check its head.
    // This finds things like `divTwoPos : ... -> rlt (rzero R) (rdiv ε ...)`.
    if (slotHeadName) {
      for (const [defName, def] of definitions.terms) {
        if (defName.includes('.') || defName === fnName) continue; // skip projections & self
        if (!def.type) continue;
        // Walk to the return type of this definition
        let retType = def.type;
        while (retType.tag === 'Binder' && retType.binderKind.tag === 'BPi') {
          retType = retType.body;
        }
        let retHead = retType;
        while (retHead.tag === 'App') retHead = retHead.fn;
        if (retHead.tag === 'Const' && retHead.name === slotHeadName) {
          // Return type head matches — this definition could produce the right type
          if (!matches.includes(defName)) {
            matches.push(defName);
          }
        }
      }
    }

    if (matches.length > 0) slotSuggestions.set(slot.index, matches);
  }

  const dotIdx = fnName.lastIndexOf('.');
  const fnDisplayName = dotIdx >= 0 ? fnName : fnName;

  return {
    fnName, fnDisplayName, slots, slotSuggestions, returnTypeLatex,
    engine: currentEngine, goalCtx: goal.ctx,
  };
}

/**
 * Build the expression string from filled slots for creating a have node.
 */
export function buildExprFromSlots(
  fnName: string,
  slots: readonly TermSlot[],
  ctx: TTKContext,
): string | null {
  const parts = [fnName];
  for (const slot of slots) {
    if (slot.implicit) continue;
    if (!slot.value) {
      parts.push('?'); // unfilled slot → hole
      continue;
    }
    // Use the stored source expression if available (handles complex terms like rdiv ε (rtwo R))
    if (slot.sourceExpr) {
      parts.push(`(${slot.sourceExpr})`);
    } else if (slot.value.tag === 'Var') {
      const name = ctx[ctx.length - 1 - slot.value.index]?.name ?? '?';
      parts.push(`(${name})`);
    } else if (slot.value.tag === 'Const') {
      parts.push(`(${slot.value.name})`);
    } else {
      parts.push('(?)');
    }
  }
  return parts.join(' ');
}
