/**
 * The proof-tree editor's internal tactic-command vocabulary.
 *
 * These types used to live in the TT surface layer (`compiler/surface.ts`) and
 * carried TT terms as arguments — but the proof tree only ever turned those
 * terms straight back into strings (`extractName` / `surfaceTermToString`), so
 * parsing an argument into a term and re-printing it was a lossy round-trip
 * around a string. Arguments are now the strings they always effectively were,
 * which is also what the Lean backend needs: an argument is a fragment of Lean
 * source, and Lean is the only thing that should be parsing Lean.
 */

/**
 * A pattern bound by a case branch. Nested because a constructor's argument can
 * itself be destructured — `| MkDPair x (MkPair y z) =>` binds x, y and z.
 */
export type CasePattern =
  | { tag: 'var'; name: string }
  | { tag: 'ctor'; constructor: string; params: CasePattern[] };

/** Treat a flat list of parameter names as (unnested) binding patterns. */
export function flatParamsToCasePatterns(names: readonly string[]): CasePattern[] {
  return names.map((name) => ({ tag: 'var' as const, name }));
}

/** Every variable name a single pattern binds (recursively). */
export function patternVarNames(pattern: CasePattern): string[] {
  if (pattern.tag === 'var') return [pattern.name];
  const names: string[] = [];
  for (const sub of pattern.params) names.push(...patternVarNames(sub));
  return names;
}

/** Every variable name a list of patterns binds. */
export function allPatternVarNames(patterns: readonly CasePattern[]): string[] {
  const names: string[] = [];
  for (const p of patterns) names.push(...patternVarNames(p));
  return names;
}

/** One branch of a structured `cases`/`induction`. */
export interface CaseBranch {
  constructor: string;
  params: CasePattern[];
  tactics: TacticCommand[];
}

/**
 * A single tactic with its arguments, e.g. `{ name: 'apply', args: ['divPos'] }`.
 * An argument is source text — an identifier or a whole expression.
 */
export interface TacticCommand {
  name: string;
  args: string[];
  /** Structured `cases` syntax. */
  caseBranches?: CaseBranch[];
  /** Bullet syntax (subgoal focusing). */
  focusedTactics?: TacticCommand[];
  /** Rewrite metadata the structured editor attaches to `rewrite`/`rw`/`erw`. */
  rewriteOptions?: {
    reverse?: boolean;
    occurrences?: readonly number[];
    targetHead?: string;
    enhanced?: boolean;
  };
}

// ── nested case-pattern desugaring ──────────────────────────────────────────
// `| MkDPair a (MkPair x y) => tactics` becomes
// `| MkDPair a _nested0 => cases _nested0 with | MkPair x y => tactics`,
// so a tactic engine that expects FLAT patterns can still handle nested
// destructuring. Relocated here from the deleted TT layer: it is pure pattern
// shuffling with no dependency on any term representation.

let nestedFreshCounter = 0;

/** A fresh binder name for a nested sub-pattern. */
function freshNestedName(): string {
  return `_nested${nestedFreshCounter++}`;
}

/**
 * Flatten one case branch's nested patterns, pushing the extra layers into
 * inner `cases` tactics. Returns the branch unchanged when nothing is nested.
 */
export function desugarNestedCaseBranch(branch: CaseBranch): CaseBranch {
  const flatParams: CasePattern[] = [];
  const nestedSubs: Array<{ freshName: string; pattern: CasePattern & { tag: 'ctor' } }> = [];

  for (const param of branch.params) {
    if (param.tag === 'var') {
      flatParams.push(param);
    } else {
      const freshName = freshNestedName();
      flatParams.push({ tag: 'var' as const, name: freshName });
      nestedSubs.push({ freshName, pattern: param });
    }
  }

  if (nestedSubs.length === 0) return branch;

  // Chain the `cases` commands from the inside out.
  let innerTactics = branch.tactics;
  for (let i = nestedSubs.length - 1; i >= 0; i--) {
    const { freshName, pattern } = nestedSubs[i];
    const innerBranch = desugarNestedCaseBranch({
      constructor: pattern.constructor,
      params: pattern.params,
      tactics: innerTactics,
    });
    innerTactics = [{ name: 'cases', args: [freshName], caseBranches: [innerBranch] }];
  }

  return { constructor: branch.constructor, params: flatParams, tactics: innerTactics };
}
