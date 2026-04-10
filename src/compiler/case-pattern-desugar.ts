/**
 * Desugar nested case patterns into sequential `cases` tactic calls.
 *
 * Example:
 *   | MkDPair a (MkPair x y) => tactics
 * becomes:
 *   | MkDPair a _nested0 =>
 *     cases _nested0 with
 *     | MkPair x y => tactics
 *
 * This lets the existing tactic engine (which expects flat patterns)
 * handle nested destructuring without modification.
 */

import { CaseBranch, CasePattern, TacticCommand, mkConstTT } from './surface';

let nestedFreshCounter = 0;

/** Generate a fresh name for a nested sub-pattern. */
function freshNestedName(): string {
  return `_nested${nestedFreshCounter++}`;
}

/**
 * Desugar a single case branch. If the branch has nested patterns,
 * returns a new branch with flat params plus inner `cases` tactics
 * that destructure the remaining layers.
 *
 * If the branch has no nested patterns, returns it unchanged.
 */
export function desugarNestedCaseBranch(branch: CaseBranch): CaseBranch {
  const flatParams: CasePattern[] = [];
  const nestedSubs: Array<{ freshName: string; pattern: CasePattern & { tag: 'ctor' } }> = [];

  for (const param of branch.params) {
    if (param.tag === 'var') {
      flatParams.push(param);
    } else {
      // Nested constructor pattern — generate a fresh name, queue for inner cases
      const freshName = freshNestedName();
      flatParams.push({ tag: 'var' as const, name: freshName });
      nestedSubs.push({ freshName, pattern: param });
    }
  }

  if (nestedSubs.length === 0) return branch;

  // Build inner tactics: chain cases commands from inside-out
  let innerTactics = branch.tactics;
  for (let i = nestedSubs.length - 1; i >= 0; i--) {
    const { freshName, pattern } = nestedSubs[i];
    // Recursively desugar the nested pattern's branch
    const innerBranch = desugarNestedCaseBranch({
      constructor: pattern.constructor,
      params: pattern.params,
      tactics: innerTactics,
    });
    const innerCases: TacticCommand = {
      name: 'cases',
      args: [mkConstTT(freshName)],
      caseBranches: [innerBranch],
    };
    innerTactics = [innerCases];
  }

  return {
    constructor: branch.constructor,
    params: flatParams,
    tactics: innerTactics,
  };
}
