/**
 * The term builder, backed by a `ProofSession`.
 *
 * "Use limF" opens a slot form: the function's remaining arguments, one box
 * each, filled in and type-checked as you go. Every answer here comes from
 * Lean — each fill re-probes the whole application, so a wrong argument is
 * reported where it was typed instead of surfacing later as a mystery error.
 *
 * Framework-free: it implements `TermBuilderProvider`, which the React
 * `TermBuilderView` consumes, but it holds no React itself.
 */
import type { TermBuilderDisplay, TermBuilderProvider } from '../proof-tree/term-builder';
import {
  appliedExpr,
  appliedExprWithHoles,
  parseApplied,
  resolveGreekToHypNames,
  slotSuggestionNames,
  type TermSlot,
} from '../lean/termSlots';
import { mathTextToLatex } from '../lean/codeWithInfos';
import type { ProofSession } from './session';

/** Values array from a display: the source text of each filled slot, else null. */
function valuesOf(d: TermBuilderDisplay): Array<string | null> {
  return d.slots.map((sl) => (sl.value !== null && sl.sourceExpr ? sl.sourceExpr : null));
}

export function createTermBuilderProvider(session: ProofSession): TermBuilderProvider {
  /** Build a display from probed slots + the current fill values. */
  const displayFrom = (
    fn: string,
    baseSlots: TermSlot[],
    returnType: string,
    values: Array<string | null>,
  ): TermBuilderDisplay => {
    const hyps = session.hypothesesWithTypes();
    const slots = baseSlots.map((sl, i) => ({
      index: i,
      name: sl.name ?? `arg${i + 1}`,
      typeLatex: mathTextToLatex(sl.type),
      typePlain: sl.type,
      implicit: false,
      value: values[i] ?? null,
      sourceExpr: values[i] ?? undefined,
      valueLatex: values[i] ? mathTextToLatex(values[i]!) : undefined,
    }));
    const slotSuggestions = new Map<number, string[]>(
      slots.map((sl, i) => [i, sl.value === null ? slotSuggestionNames(sl.typePlain ?? '', hyps) : []]),
    );
    return { fnDisplayName: fn, slots, slotSuggestions, returnTypeLatex: mathTextToLatex(returnType) };
  };

  return {
    open: async (haveExpr) => {
      const { fn, values } = parseApplied(haveExpr);
      if (!fn) return null;
      const probed = await session.probeTerm(fn);
      if ('error' in probed) return null;
      return displayFrom(fn, probed.slots, probed.returnType, probed.slots.map((_, i) => values[i] ?? null));
    },

    fill: async (display, slotIndex, sourceExpr) => {
      const fn = display.fnDisplayName;
      const values = valuesOf(display);
      values[slotIndex] = sourceExpr;
      let expr = appliedExprWithHoles(fn, values);
      let check = await session.probeTerm(expr);

      if ('error' in check) {
        // Typed a Greek letter (ε) against an ASCII-named hypothesis (eps)?
        // Resolve against the context and retry once, so the display shows what
        // the user meant rather than an error about a name that doesn't exist.
        const resolved = resolveGreekToHypNames(sourceExpr, session.hypothesisNames());
        if (resolved) {
          const retryValues = [...values];
          retryValues[slotIndex] = resolved;
          const retryExpr = appliedExprWithHoles(fn, retryValues);
          const retry = await session.probeTerm(retryExpr);
          if (!('error' in retry)) {
            values[slotIndex] = resolved;
            expr = retryExpr;
            check = retry;
          }
        }
      }

      if ('error' in check) {
        // Report the failure ON the slot that caused it.
        const slots = display.slots.map((sl, i) => (i === slotIndex ? { ...sl, error: check.error } : sl));
        return { display: { ...display, slots }, expr: appliedExprWithHoles(fn, valuesOf(display)) };
      }

      // Specialize the REMAINING slot types when the fills form a pure prefix
      // (the common flow): probing the applied prefix tells us what the later
      // arguments must now be, e.g. after choosing ε the next slot's type is
      // `0 < ε` rather than `0 < ?e`.
      const firstHole = values.findIndex((v) => v === null);
      const isPrefix = firstHole === -1 || values.slice(firstHole).every((v) => v === null);
      let baseSlots: TermSlot[] = display.slots.map((sl) => ({ name: sl.name, type: sl.typePlain ?? '' }));
      let returnPlain = '';
      if (isPrefix) {
        const spec = await session.probeTerm(
          appliedExpr(fn, values.filter((v): v is string => v !== null)),
        );
        if (!('error' in spec)) {
          const filled = firstHole === -1 ? values.length : firstHole;
          baseSlots = [...baseSlots.slice(0, filled), ...spec.slots].slice(0, values.length);
          returnPlain = spec.returnType;
        }
      }
      return { display: displayFrom(fn, baseSlots, returnPlain, values), expr };
    },

    clear: async (display, slotIndex) => {
      const fn = display.fnDisplayName;
      const values = valuesOf(display);
      values[slotIndex] = null;
      const baseSlots: TermSlot[] = display.slots.map((sl) => ({ name: sl.name, type: sl.typePlain ?? '' }));
      return { display: displayFrom(fn, baseSlots, '', values), expr: appliedExprWithHoles(fn, values) };
    },

    /**
     * Hoist: eject an unfilled slot's obligation into a `have hN : <type>` above
     * (with its own proof subtree) and fill the slot with `hN` — the obligation
     * gets USED here and PROVED there. Synchronous and correct by construction:
     * the new have's ascribed type IS the slot's probed type.
     */
    hoist: (display, slotIndex) => {
      const slot = display.slots[slotIndex];
      if (!slot || slot.value !== null || !slot.typePlain) return null;
      const inScope = session.hypothesisNames();
      // TT's naming: h<slotName>, falling back to the index for defaulted names.
      const base = /^arg\d+$/.test(slot.name) ? `${slotIndex}` : slot.name;
      let haveName = `h${base}`;
      if (inScope.includes(haveName)) haveName = session.freshHypName();
      const values = valuesOf(display);
      values[slotIndex] = haveName;
      const slots = display.slots.map((sl, i) =>
        i === slotIndex
          ? { ...sl, value: haveName, sourceExpr: haveName, valueLatex: mathTextToLatex(haveName), error: undefined }
          : sl,
      );
      const suggestions = new Map(display.slotSuggestions);
      suggestions.set(slotIndex, []);
      return {
        display: { ...display, slots, slotSuggestions: suggestions },
        expr: appliedExprWithHoles(display.fnDisplayName, values),
        haveName,
        haveTypeExpr: slot.typePlain,
      };
    },
  };
}
