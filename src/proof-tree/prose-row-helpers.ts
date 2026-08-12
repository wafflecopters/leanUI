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
      // An anonymous-constructor tuple ⟨w, …⟩ supplies a WITNESS with its
      // proofs — a choice, not a derivation — so it reads "Take", like any
      // other value.
      lead: kind.isValueType || kind.exprLatex.trim().startsWith('⟨')
        ? 'Take'
        : 'The result follows from',
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

/**
 * The sentence Lean's PRIMITIVE closers deserve. "By rfl." is tactic-speak
 * for something a paper states outright, and the reader has no use for the
 * tactic's name. Keyed on Lean's own primitives — generic, not domain
 * knowledge — and null for anything else, which keeps its term on screen.
 */
export function primitiveClosingPhrase(expr: string): string | null {
  switch (expr.trim()) {
    case 'rfl':
    case 'Eq.refl _':
      return 'Both sides are identical';
    case 'trivial':
      return 'This is immediate';
    case 'decide':
      return 'This is decidable, and decides true';
    case 'assumption':
      return 'This is one of our assumptions';
    default:
      return null;
  }
}

/** Top-level components of an anonymous-constructor tuple `⟨a, b, c⟩`, or
 *  null when the text isn't one. Splits on depth-0 commas only. */
export function splitAnonTuple(expr: string): string[] | null {
  const t = expr.trim();
  if (!t.startsWith('⟨') || !t.endsWith('⟩')) return null;
  const inner = t.slice(1, -1);
  const parts: string[] = [];
  let depth = 0;
  let cur = '';
  for (const ch of inner) {
    if ('⟨([{'.includes(ch)) depth++;
    else if ('⟩)]}'.includes(ch)) depth--;
    if (ch === ',' && depth === 0) {
      parts.push(cur.trim());
      cur = '';
      continue;
    }
    cur += ch;
  }
  parts.push(cur.trim());
  return parts.length >= 2 && parts.every((p) => p.length > 0) ? parts : null;
}

/** The first argument of an application expression — what a citation is
 *  "applied to". `ih (pre ++ post) h1 h2` → `pre ++ post`; a bare name has
 *  none. Textual and display-only; used so "by the induction hypothesis"
 *  can say WHICH instance, which is the whole content of the step. */
export function firstExplicitArg(expr: string): string | null {
  const m = expr.trim().match(/^[A-Za-z_][A-Za-z0-9_.']*\s+(.*)$/s);
  if (!m) return null;
  const rest = m[1].trim();
  if (!rest) return null;
  if (rest.startsWith('(')) {
    let depth = 0;
    for (let i = 0; i < rest.length; i++) {
      if (rest[i] === '(') depth++;
      else if (rest[i] === ')') {
        depth--;
        if (depth === 0) return rest.slice(1, i).trim() || null;
      }
    }
    return null;
  }
  return rest.split(/\s/)[0] || null;
}

/** The ∃-binder's name out of a rendered goal — `\exists {\operatorname{bs}}, …`
 *  → `bs`. Display-only; null when the goal isn't a simple ∃. */
export function existsBinderFromLatex(goalLatex: string): string | null {
  const m = goalLatex.match(/\\exists\s*\{*(?:\\operatorname\{)?([A-Za-z_][A-Za-z0-9_']*)/);
  return m ? m[1] : null;
}
