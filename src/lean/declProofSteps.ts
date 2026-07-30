import type { LeanDeclaration, LeanGoal } from './types';

/**
 * Group tactic goal-states under the declaration that contains them.
 *
 * Each declaration starts at a known line; a declaration owns every goal whose
 * range starts at or after its own start and before the next declaration's start
 * (declarations are in source order). This lets the WYSIWYG show, per
 * declaration, the sequence of proof steps (goal states) the way the structured
 * proof editor did — sorted by position, deduplicated by range.
 */
export interface ProofStep {
  startLine: number;
  startCol: number;
  endLine: number;
  endCol: number;
  goal: LeanGoal;
}

export function groupGoalsByDeclaration(
  declarations: LeanDeclaration[],
  goals: LeanGoal[],
): Map<string, ProofStep[]> {
  const result = new Map<string, ProofStep[]>();
  if (declarations.length === 0) return result;

  // Declarations sorted by start position, with their key.
  const sorted = declarations
    .map((d, i) => ({ d, key: declKey(d), origIndex: i }))
    .sort((a, b) => a.d.line - b.d.line || a.d.col - b.d.col);

  for (let i = 0; i < sorted.length; i++) {
    const { d, key } = sorted[i];
    const next = sorted[i + 1]?.d;
    const startLine = d.line;
    const endLine = next ? next.line : Number.POSITIVE_INFINITY;

    const steps: ProofStep[] = goals
      .filter((g) => g.startLine >= startLine && g.startLine < endLine)
      .map((g) => ({
        startLine: g.startLine,
        startCol: g.startCol,
        endLine: g.endLine,
        endCol: g.endCol,
        goal: g,
      }))
      .sort((a, b) => a.startLine - b.startLine || a.startCol - b.startCol);

    result.set(key, steps);
  }
  return result;
}

/** Stable per-declaration key (name + position; positions disambiguate dup names). */
export function declKey(d: LeanDeclaration): string {
  return `${d.name}@${d.line}:${d.col}`;
}
