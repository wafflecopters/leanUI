import { ProseItemKind } from './proof-prose';
import { renderNameLatex } from './name-latex';

type ApplyKind = Extract<ProseItemKind, { tag: 'apply' }>;
type ExactKind = Extract<ProseItemKind, { tag: 'exact' }>;
type InductionHeaderKind = Extract<ProseItemKind, { tag: 'inductionHeader' }>;
type RewriteKind = Extract<ProseItemKind, { tag: 'rewrite' }>;

export interface ExtractedLemmaAndArgs {
  readonly lemma: string;
  readonly simpleArgs: readonly string[];
}

export interface RewriteReferenceDescription {
  readonly mode: 'equation' | 'lemma';
  readonly theoremName: string;
  readonly arrowSuffix: string;
  readonly equationLatex?: string;
}

export type ApplyProseDescription =
  | {
      readonly mode: 'proofExprs';
      readonly proofExprs: readonly string[];
    }
  | {
      readonly mode: 'singleSubgoal' | 'multiSubgoals';
      readonly phrase: 'constructor' | 'theorem';
      readonly theoremName?: string;
      readonly constructorPhrase?: string;
      readonly appliedArgs: readonly string[];
      readonly subgoals: readonly string[];
    };

export interface InductionHeaderDescription {
  readonly lead: string;
  readonly punctuation: ':' | '.';
}

export interface ExactProseDescription {
  readonly mode: 'solved' | 'error' | 'pending';
  readonly lead: string;
  readonly displayLatex: string;
  readonly error?: string;
}

function texNameForProse(name: string): string {
  return renderNameLatex(name, 'textsf');
}

/**
 * Extract lemma name + meaningful simple args from a proof expression.
 * "limitExt (\x => ...) (diffQuot ...) x0 (rmul Lg Lf) (chainAlgId g f x0 Lg) h"
 *  → { lemma: "limitExt", simpleArgs: ["chainAlgId", "h"] }
 * Filters out: lambdas, parenthesized sub-expressions, single-char structural vars.
 */
export function extractLemmaAndArgs(expr: string): ExtractedLemmaAndArgs {
  const trimmed = expr.trim();
  const tokens: string[] = [];
  let depth = 0;
  let current = '';

  for (const ch of trimmed) {
    if (ch === '(' || ch === ')') {
      depth += ch === '(' ? 1 : -1;
      current += ch;
    } else if (ch === ' ' && depth === 0) {
      if (current) tokens.push(current);
      current = '';
    } else {
      current += ch;
    }
  }

  if (current) tokens.push(current);

  const raw0 = (tokens[0] ?? '').replace(/^\(+/, '');
  const parenIdx = raw0.indexOf('(');
  const lemma = parenIdx >= 0 ? raw0.slice(0, parenIdx) : raw0.replace(/\)+$/, '');
  const simpleArgs: string[] = [];

  for (let i = 1; i < tokens.length; i++) {
    const token = tokens[i];
    if (token.startsWith('(') || token.startsWith('\\') || token.includes('=>')) continue;
    if (/^[a-zA-Z][a-zA-Z0-9_]*$/.test(token) && (token.length >= 3 || token.startsWith('h'))) {
      simpleArgs.push(token);
    }
  }

  return { lemma, simpleArgs };
}

export function describeRewriteReference(kind: RewriteKind): RewriteReferenceDescription {
  const arrowSuffix = kind.reverse ? ' (←)' : '';
  if (kind.equationLatex) {
    return {
      mode: 'equation',
      theoremName: kind.name,
      arrowSuffix,
      equationLatex: kind.equationLatex,
    };
  }

  return {
    mode: 'lemma',
    theoremName: extractLemmaAndArgs(kind.name).lemma,
    arrowSuffix,
  };
}

export function describeApplyProse(kind: ApplyKind): ApplyProseDescription {
  const proofExprs = kind.proofExprs ?? [];
  if (proofExprs.length > 0) {
    return {
      mode: 'proofExprs',
      proofExprs,
    };
  }

  const subgoals = kind.subgoalLatex ?? [];
  const appliedArgs = kind.appliedArgsLatex ?? [];
  const isConstructor = kind.name === 'constructor';

  if (isConstructor) {
    return {
      mode: subgoals.length <= 1 ? 'singleSubgoal' : 'multiSubgoals',
      phrase: 'constructor',
      constructorPhrase: subgoals.length <= 1 ? 'by definition' : 'by construction',
      appliedArgs,
      subgoals,
    };
  }

  return {
    mode: subgoals.length <= 1 ? 'singleSubgoal' : 'multiSubgoals',
    phrase: 'theorem',
    theoremName: kind.name,
    appliedArgs,
    subgoals,
  };
}

export function describeInductionHeader(kind: InductionHeaderKind): InductionHeaderDescription {
  return kind.isCases
    ? { lead: 'By cases on', punctuation: ':' }
    : { lead: 'We proceed by induction on', punctuation: '.' };
}

export function describeExactProse(kind: ExactKind): ExactProseDescription {
  const proofLatex = kind.proofExprLatex;
  const fallbackName = kind.exprLatex.trim().replace(/^\(+/, '').split(/[\s(]/)[0] ?? '';
  const displayLatex = proofLatex ?? texNameForProse(fallbackName.replace(/\)+$/, ''));

  if (kind.solved) {
    return {
      mode: 'solved',
      lead: kind.isValueType ? 'Take' : 'The result follows from',
      displayLatex,
    };
  }

  if (kind.error) {
    return {
      mode: 'error',
      lead: 'By',
      displayLatex,
      error: kind.error,
    };
  }

  return {
    mode: 'pending',
    lead: 'By',
    displayLatex,
  };
}
