import { mkVar } from "../types/tt-core";
import { TTKTerm } from "../types/tt-kernel";
import { whnf } from "./whnf";

export type Substitutions = Map<number, TTKTerm>

export type UnifyResult = {
  success: true,
  substitutions: Substitutions,
  metaConstraints: unknown[],
} | {
  success: false,
  reason: 'conflict' | 'cycle',
}

export function unifyTerms(lhs: TTKTerm, rhs: TTKTerm): UnifyResult {
  const a = whnf(lhs)
  const b = whnf(rhs)

  if (a.tag === 'Const' && b.tag === 'Const') {
    if (a.name !== b.name) {
      return {
        success: false,
        reason: 'conflict',
      }
    }
    return { success: true, substitutions: new Map(), metaConstraints: [] }
  }

  if (a.tag === 'App' && b.tag === 'App') {
    const unifyResultFn = unifyTerms(a.fn, b.fn)
    if (!unifyResultFn.success) {
      return unifyResultFn
    }
    const unifyResultArg = unifyTerms(a.arg, b.arg)
    if (!unifyResultArg.success) {
      return unifyResultArg
    }
    return { success: true, substitutions: new Map([...unifyResultFn.substitutions, ...unifyResultArg.substitutions]), metaConstraints: [...unifyResultFn.metaConstraints, ...unifyResultArg.metaConstraints] }
  }

  if (a.tag === 'Var' && b.tag === 'Var') {
    const higherIndex = Math.max(a.index, b.index)
    const lowerIndex = Math.min(a.index, b.index)
    return {
      success: true, substitutions: new Map([[lowerIndex, mkVar(higherIndex)]]), metaConstraints: []
    }
  }

  if (a.tag === 'Var') {
    return { success: true, substitutions: new Map([[a.index, b]]), metaConstraints: [] }
  }

  if (b.tag === 'Var') {
    return { success: true, substitutions: new Map([[b.index, a]]), metaConstraints: [] }
  }

  debugger
  return { success: false, reason: 'conflict' }
}
