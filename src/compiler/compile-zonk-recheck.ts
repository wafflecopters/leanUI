import { inferType } from './checker';
import type { TTKTerm } from './kernel';
import { createTCEnv, type DefinitionsMap, TCEnvError } from './term';

export type RecheckZonkedTermFn = (
  term: TTKTerm,
  definitions: DefinitionsMap,
  label: string,
) => string | undefined;

/**
 * Check that a zonked term contains no leftover Meta or Hole nodes and
 * still type-checks from scratch in a fresh environment.
 *
 * Match terms are intentionally skipped because they are trusted compiler
 * output rather than user-facing kernel syntax we expect to re-infer.
 */
export const recheckZonkedTerm: RecheckZonkedTermFn = (
  term,
  definitions,
  label,
) => {
  if (term.tag === 'Match') return undefined;

  const leftoverMetas: string[] = [];
  const leftoverHoles: string[] = [];

  function walk(t: TTKTerm): void {
    switch (t.tag) {
      case 'Meta':
        leftoverMetas.push(t.id);
        break;
      case 'Hole':
        if (!t.id.startsWith('?')) {
          leftoverHoles.push(t.id);
        }
        break;
      case 'App':
        walk(t.fn);
        walk(t.arg);
        break;
      case 'Binder':
        walk(t.domain);
        walk(t.body);
        break;
      case 'Sort':
        walk(t.level);
        break;
      case 'Annot':
        walk(t.term);
        walk(t.type);
        break;
      case 'Match':
        break;
      default:
        break;
    }
  }

  walk(term);

  if (leftoverMetas.length > 0) {
    return `Zonk recheck failed for ${label}: ${leftoverMetas.length} unsolved meta(s) remaining: ${leftoverMetas.join(', ')}`;
  }
  if (leftoverHoles.length > 0) {
    return `Zonk recheck failed for ${label}: ${leftoverHoles.length} unresolved hole(s) remaining: ${leftoverHoles.join(', ')}`;
  }

  try {
    const freshEnv = createTCEnv({ definitions, options: { mode: 'check' } });
    const resultEnv = inferType(freshEnv.withValue(term));
    const solvedEnv = resultEnv.solveMetasAndConstraints({ liftMetasToFullContext: false });

    const unsolvedIds: string[] = [];
    for (const [id, meta] of solvedEnv.metaVars) {
      if (!meta.solution && !meta.isHole) unsolvedIds.push(id);
    }
    if (unsolvedIds.length > 0) {
      return `Zonk recheck failed for ${label}: re-type-check generated ${unsolvedIds.length} unsolved meta(s): ${unsolvedIds.join(', ')}`;
    }
  } catch (error) {
    const message = error instanceof TCEnvError
      ? error.fullMessage
      : error instanceof Error
        ? error.message
        : String(error);
    return `Zonk recheck (re-type-check) failed for ${label}: ${message}`;
  }

  return undefined;
};
