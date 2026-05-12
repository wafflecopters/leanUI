import type { DefinitionsMap } from './term';
import type { TClause, TTerm } from './surface';
import type { TTKTerm } from './kernel';
import { countPiBindersWhnf } from './whnf';

export interface PreparedMatchSurfaceClauses {
  surfaceClauses: TClause[];
  surfaceClauseIndices: number[];
}

/**
 * Filter out annotated absurd clauses while preserving their original surface
 * indices so kernel↔surface path mapping stays stable for the remaining clauses.
 */
export function prepareMatchSurfaceClauses(surfaceValue?: TTerm): PreparedMatchSurfaceClauses {
  if (!surfaceValue || surfaceValue.tag !== 'Match') {
    return {
      surfaceClauses: [],
      surfaceClauseIndices: [],
    };
  }

  const surfaceClausesWithIndices = surfaceValue.clauses
    .map((clause, index) => ({ clause, originalIndex: index }))
    .filter(({ clause }) => clause.rhs.tag !== 'AbsurdMarker');

  return {
    surfaceClauses: surfaceClausesWithIndices.map(({ clause }) => clause),
    surfaceClauseIndices: surfaceClausesWithIndices.map(({ originalIndex }) => originalIndex),
  };
}

/**
 * Surface arity can undercount when the declaration type is a reducible alias
 * like `Not A` that WHNF-unfolds to additional Pi binders. Recompute arity from
 * the zonked kernel type whenever the declaration had an explicit surface type.
 */
export function computeEffectiveTotalArity(
  zonkedKernelType: TTKTerm,
  totalArity: number | undefined,
  definitions: DefinitionsMap,
): number | undefined {
  if (totalArity === undefined) {
    return undefined;
  }
  return countPiBindersWhnf(zonkedKernelType, definitions);
}
