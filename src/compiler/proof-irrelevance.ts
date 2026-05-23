import { TTKContext, TTKTerm, mkLIMax, mkLSucc, mkULit, simplifyLevel } from "./kernel";
import { minFreeVarIndex, shiftTerm, subst } from "./subst";
import { DefinitionsMap, getTypeDefinition } from "./term";

/**
 * Minimal type classifier used solely by the proof-irrelevance shortcut in
 * definitional equality.
 *
 * This is intentionally not a general-purpose inferer. It returns `undefined`
 * for terms it cannot classify without invoking the full checker. Keeping it
 * isolated makes the boundary explicit while defeq still needs a side-effect
 * free way to recognize already-typed proof terms.
 */
export function inferTypeForProofIrrelevance(
  term: TTKTerm,
  ctx: TTKContext,
  definitions: DefinitionsMap | undefined,
  reduce: (term: TTKTerm, ctx: TTKContext) => TTKTerm,
): TTKTerm | undefined {
  switch (term.tag) {
    case 'Var': {
      const i = term.index;
      if (i < 0 || i >= ctx.length) return undefined;
      const entry = ctx[ctx.length - 1 - i];
      // Shift to bring the stored type into the current scope's de Bruijn frame.
      return shiftTerm(entry.type, i + 1, 0);
    }
    case 'Const':
      return definitions ? getTypeDefinition(definitions, term.name) : undefined;
    case 'App': {
      const fnType = inferTypeForProofIrrelevance(term.fn, ctx, definitions, reduce);
      if (!fnType) return undefined;
      const wfn = reduce(fnType, ctx);
      if (wfn.tag !== 'Binder' || wfn.binderKind.tag !== 'BPi') return undefined;
      return subst(0, term.arg, wfn.body);
    }
    case 'Sort':
      return { tag: 'Sort', level: mkLSucc(term.level) };
    case 'Binder': {
      const bodyCtx: TTKContext = [
        ...ctx,
        {
          name: term.name,
          type: term.domain,
          value: term.binderKind.tag === 'BLet' ? term.binderKind.defVal : undefined,
        },
      ];
      if (term.binderKind.tag === 'BLam') {
        const bodyType = inferTypeForProofIrrelevance(term.body, bodyCtx, definitions, reduce);
        if (!bodyType) return undefined;
        return { tag: 'Binder', name: term.name, binderKind: { tag: 'BPi' }, domain: term.domain, body: bodyType };
      }
      if (term.binderKind.tag === 'BPi') {
        const domType = inferTypeForProofIrrelevance(term.domain, ctx, definitions, reduce);
        if (!domType) return undefined;
        const wdom = reduce(domType, ctx);
        if (wdom.tag !== 'Sort') return undefined;
        const bodyType = inferTypeForProofIrrelevance(term.body, bodyCtx, definitions, reduce);
        if (!bodyType) return undefined;
        const wbody = reduce(bodyType, bodyCtx);
        if (wbody.tag !== 'Sort') return undefined;
        return { tag: 'Sort', level: simplifyLevel(mkLIMax(wdom.level, wbody.level)) };
      }
      if (term.binderKind.tag === 'BLet') {
        const bodyType = inferTypeForProofIrrelevance(term.body, bodyCtx, definitions, reduce);
        if (!bodyType) return undefined;
        const letValue = term.binderKind.defVal;
        const minIdx = minFreeVarIndex(bodyType);
        if (minIdx === 0) return subst(0, letValue, bodyType);
        return shiftTerm(bodyType, -1, 0);
      }
      return undefined;
    }
    case 'Annot':
      return term.type;
    case 'ULevel':
      // Match checker.ts: ULevel : Sort 1 (= Type 0).
      return { tag: 'Sort', level: mkULit(1) };
    case 'ULit':
    case 'UOmega':
      return { tag: 'ULevel' };
    default:
      // Hole, Meta, Match, NatLit, RatLit: caller falls back to structural defeq.
      return undefined;
  }
}
