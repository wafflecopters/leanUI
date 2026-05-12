import type { ElabDeclaration } from './compile-types';
import { elabPatternToKernel, reorderPatterns, type NamedArgMap } from './elab';
import type { TTKPattern, TTKTerm } from './kernel';
import { arePatternsAbsurd } from './patterns';
import type { TCEnv, TermDefinition } from './term';
import { extractPiSpine, TCEnvError } from './term';
import { whnf } from './whnf';
import { countPiBinders } from './term';
import { tryCaseSplitsInSearchOfAbsurdity } from './compile-term-value';

export function validateAnnotatedAbsurdClauses(
  decl: ElabDeclaration,
  termEnv: TCEnv<TermDefinition>,
  zonkedKernelType: TTKTerm,
  namedArgMap?: NamedArgMap,
): { success: true; annotatedAbsurdClauses: number[] } | { success: false; errors: TCEnvError[] } {
  const errors: TCEnvError[] = [];
  const annotatedAbsurdClauses: number[] = [];

  if (decl.surfaceValue?.tag !== 'Match') {
    return { success: true, annotatedAbsurdClauses };
  }

  for (let i = 0; i < decl.surfaceValue.clauses.length; i++) {
    const clause = decl.surfaceValue.clauses[i];
    if (clause.rhs.tag !== 'AbsurdMarker') {
      continue;
    }

    const piSpine = extractPiSpine(zonkedKernelType);
    const normalizedReturnType = whnf(piSpine.body, { definitions: termEnv.definitions, fuel: 100 });
    let normalizedType = normalizedReturnType;
    for (let binderIndex = piSpine.binders.length - 1; binderIndex >= 0; binderIndex--) {
      const binder = piSpine.binders[binderIndex];
      normalizedType = {
        tag: 'Binder',
        name: binder.name,
        binderKind: { tag: 'BPi' },
        domain: binder.type,
        body: normalizedType,
      };
    }

    const normalizedArity = countPiBinders(normalizedType);
    if (namedArgMap && namedArgMap.size > 0) {
      const reorderResult = reorderPatterns(clause.patterns, namedArgMap, clause.namedPatterns, normalizedArity);
      if ('error' in reorderResult && reorderResult.error !== undefined) {
        errors.push(TCEnvError.create(reorderResult.error, termEnv));
        continue;
      }
    }

    const kernelPatterns: TTKPattern[] = clause.patterns.map(pattern => elabPatternToKernel(pattern));
    const patternsEnv = termEnv.withValue(kernelPatterns);
    let isAbsurd = arePatternsAbsurd(decl.name ?? 'anonymous', patternsEnv, normalizedType);

    if (!isAbsurd) {
      isAbsurd = tryCaseSplitsInSearchOfAbsurdity(
        decl.name ?? 'anonymous',
        kernelPatterns,
        normalizedType,
        termEnv.definitions,
        termEnv,
      );
    }

    if (isAbsurd) {
      annotatedAbsurdClauses.push(i);
    } else {
      errors.push(TCEnvError.create('#absurd used but case is not absurd: patterns can be inhabited', termEnv));
    }
  }

  if (errors.length > 0) {
    return { success: false, errors };
  }

  return { success: true, annotatedAbsurdClauses };
}
