export class TypeCheckError extends Error {
  constructor(message: string, public term?: TTKTerm, public signature?: Signature, public termPath?: IndexPath, public definitions?: DefinitionsMap) {
    super(message);
    this.name = 'TypeCheckError';
  }
}

// INFERENCE

import { arraySeg, IndexPath } from "../types/source-position"
import { prettyPrint, shiftTerm, subst, TTKTerm } from "../types/tt-kernel"
import { DefinitionsMap, extendSignatureInTCEnv, getTypeDefinition, Signature, TCEnv } from "./term";
import { areTypesDefEq } from "./whnf";

type InferResult = {
  success: true,
  type: TTKTerm
} | {
  success: false,
  error: string
}

function inferBinderType(term: TTKTerm & { tag: 'Binder' }, path: IndexPath, env: TCEnv): InferResult {
  if (term.binderKind.tag === 'BPi') {
    const domResult = inferType(term.domain, [...path, arraySeg(0)], env)

    if (!domResult.success) {
      return domResult
    }

    const bodyResult = inferType(term.body, [...path, arraySeg(1)], extendSignatureInTCEnv(env, term.name, term.domain))

    if (!bodyResult.success) {
      return bodyResult
    }

    return { success: true, type: maxSort(domResult.type, bodyResult.type) }
  }
  debugger
  throw new Error('Not implemented')
}

export function inferType(term: TTKTerm, path: IndexPath, env: TCEnv): InferResult {
  if (term.tag === 'Const') {
    const type = getTypeDefinition(env.definitions, term.name)
    if (!type) {
      throw new TypeCheckError(`Constant '${term.name}' not found in definitions`, term, env.signature, path, env.definitions)
    }
    return { success: true, type }
  } else if (term.tag === 'Binder') {
    return inferBinderType(term, path, env)
  } else if (term.tag === 'Sort') {
    return { success: true, type: { tag: 'Sort', level: term.level + 1 } }
  } else if (term.tag === 'Var') {
    return { success: true, type: lookupTypeAtIndexSignature(env.signature, term.index) }
  } else if (term.tag === 'App') {
    const fnResult = inferType(term.fn, path, env)

    if (!fnResult.success) {
      return fnResult
    }

    // Function type must be a Pi
    if (fnResult.type.tag !== 'Binder' || fnResult.type.binderKind.tag !== 'BPi') {
      return { success: false, error: `App function is not a Pi type: ${prettyPrint(fnResult.type)}` };
    }

    const argResult = inferType(term.arg, path, env)

    if (!argResult.success) {
      return argResult
    }

    // Check argument against domain
    const checkResult = checkType(term.arg, fnResult.type.domain, path, env);
    if (!checkResult.success) {
      debugger
      return { success: false, error: new TypeCheckError(`App argument type mismatch: ${checkResult.error}`, term.arg, env.signature, path, env.definitions).message };
    }

    return { success: true, type: subst(0, term.arg, fnResult.type.body) };
  }
  debugger
  throw new Error('Not implemented')
}

// CHECKING

export function checkType(term: TTKTerm, expectedType: TTKTerm, path: IndexPath, env: TCEnv): {
  success: true,
  type: TTKTerm
} | {
  success: false,
  error: string
} {
  // Special case: Lambda checking
  if (term.tag === 'Binder' && term.binderKind.tag === 'BLam') {
    // ────────────────────────────────────────────────────────────────
    // (LAM) - Lambda abstraction
    // 
    //   Γ ⊢ Π x : A, B
    //   Γ, x : A ⊢ t ⇐ B
    //   ───────────────────────────────
    //   Γ ⊢ λ x : A => t ⇐ Π x : A, B
    // ────────────────────────────────────────────────────────────────
    if (expectedType.tag !== 'Binder' || expectedType.binderKind.tag !== 'BPi') {
      return { success: false, error: `Lambda expected Pi type, got: ${prettyPrint(expectedType)}` };
    }

    const piType = expectedType;

    // Check that domains match
    if (!areTypesDefEq(term.domain, piType.domain)) {
      return { success: false, error: `Lambda domain mismatch: ${prettyPrint(term.domain)} vs ${prettyPrint(piType.domain)}` };
    }

    // Check body in extended context
    return checkType(term.body, piType.body, [...path, arraySeg(1)], extendSignatureInTCEnv(env, term.name, term.domain));
  }

  // ────────────────────────────────────────────────────────────────
  // (CONV) - Type conversion
  // 
  //   Γ ⊢ t ⇒ T
  //   T ≃ T′
  //   ─────────────
  //   Γ ⊢ t ⇐ T′
  // ────────────────────────────────────────────────────────────────
  const inferResult = inferType(term, path, env);
  if (!inferResult.success) {
    return { success: false, error: inferResult.error };
  }

  if (!areTypesDefEq(inferResult.type, expectedType)) {
    return {
      success: false,
      error: `Type mismatch:\n  Expected: ${prettyPrint(expectedType)}\n  Got:      ${prettyPrint(inferResult.type)}`
    };
  }

  return { success: true, type: inferResult.type };
}

// Helpers

function maxSort(lhs: TTKTerm, rhs: TTKTerm): TTKTerm {
  if (lhs.tag === 'Sort' && rhs.tag === 'Sort') {
    return { tag: 'Sort', level: Math.max(lhs.level, rhs.level) }
  }
  debugger
  throw new Error('Not implemented')
}

export function lookupTypeAtIndexSignature(signature: Signature, index: number): TTKTerm {
  const sigIndex = signature.length - 1 - index
  const binder = signature[sigIndex];
  if (!binder) {
    debugger
    throw new TypeCheckError(`Type index ${index} not found in signature`)
  }
  const type = binder.type;

  // Shift indices to be at tail of signature
  const shiftAmount = signature.length - sigIndex;
  return shiftAmount > 0 ? shiftTerm(type, shiftAmount, 0) : type;
}