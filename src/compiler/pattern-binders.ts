import type { TTKClause, TTKNamedPatternArg, TTKPattern } from './kernel';
import type { TClause, TNamedPatternArg, TPattern } from './surface';

export function countKernelPatternBindings(pattern: TTKPattern): number {
  switch (pattern.tag) {
    case 'PVar':
    case 'PWild':
      return 1;
    case 'PCtor':
      return countKernelPatternsBindings(pattern.args) + countKernelNamedPatternBindings(pattern.namedArgs);
  }
}

export function countKernelPatternsBindings(patterns: readonly TTKPattern[]): number {
  return patterns.reduce((sum, pattern) => sum + countKernelPatternBindings(pattern), 0);
}

export function countKernelNamedPatternBindings(namedPatterns?: readonly TTKNamedPatternArg[]): number {
  return (namedPatterns ?? []).reduce((sum, namedPattern) => sum + countKernelPatternBindings(namedPattern.pattern), 0);
}

export function countKernelClauseBindings(clause: Pick<TTKClause, 'patterns' | 'namedPatterns'>): number {
  return countKernelPatternsBindings(clause.patterns) + countKernelNamedPatternBindings(clause.namedPatterns);
}

export function countSurfacePatternBindings(pattern: TPattern): number {
  switch (pattern.tag) {
    case 'PVar':
    case 'PWild':
      return 1;
    case 'PCtor':
      return countSurfacePatternsBindings(pattern.args) + countSurfaceNamedPatternBindings(pattern.namedArgs);
  }
}

export function countSurfacePatternsBindings(patterns: readonly TPattern[]): number {
  return patterns.reduce((sum, pattern) => sum + countSurfacePatternBindings(pattern), 0);
}

export function countSurfaceNamedPatternBindings(namedPatterns?: readonly TNamedPatternArg[]): number {
  return (namedPatterns ?? []).reduce((sum, namedPattern) => sum + countSurfacePatternBindings(namedPattern.pattern), 0);
}

export function countSurfaceClauseBindings(clause: Pick<TClause, 'patterns' | 'namedPatterns'>): number {
  return countSurfacePatternsBindings(clause.patterns) + countSurfaceNamedPatternBindings(clause.namedPatterns);
}
