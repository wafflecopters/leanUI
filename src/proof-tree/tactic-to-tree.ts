/**
 * Convert parsed TacticCommand[] to ProofNode tree.
 *
 * This enables pre-populating the proof tree editor when a declaration
 * uses tactic mode (`:= by ...`).
 */

import { TacticCommand, TTerm, CasePattern, allPatternVarNames } from '../compiler/surface';
import { desugarNestedCaseBranch } from '../compiler/case-pattern-desugar';
import {
  ProofNode,
  mkHole,
  mkIntros,
  mkInduction,
  mkExact,
  mkUnfold,
  mkFold,
  mkRewrite,
  mkApply,
  mkCase,
  mkHave,
  mkSuffices,
} from './proof-tree';

/**
 * Render a surface TTerm to a string for display in proof tree nodes.
 * Handles the common cases seen in tactic arguments.
 * Uses "fun name =>" for lambdas (not "\name =>") to avoid KaTeX
 * interpreting \name as a LaTeX command.
 * Tracks binder context so Var nodes render as their binder name.
 */
export function surfaceTermToString(term: TTerm, ctx: string[] = []): string {
  switch (term.tag) {
    case 'Const':
      return term.name;
    case 'App': {
      // Collect spine: f a1 a2 a3 → "f a1 a2 a3" or "(f a1 a2 a3)"
      const parts: string[] = [];
      let cur: TTerm = term;
      while (cur.tag === 'App') {
        parts.unshift(surfaceTermToString(cur.arg, ctx));
        cur = cur.fn;
      }
      parts.unshift(surfaceTermToString(cur, ctx));
      return `(${parts.join(' ')})`;
    }
    case 'Binder':
      if (term.binderKind.tag === 'BLamTT') {
        const newCtx = [term.name, ...ctx];
        return `(fun ${term.name} => ${surfaceTermToString(term.body, newCtx)})`;
      }
      return '?';
    case 'Var':
      return ctx[term.index] ?? `v${term.index}`;
    case 'Hole':
      return '_';
    default:
      return '?';
  }
}

/** Extract a name from a TTerm that should be an identifier (Const node). */
function extractName(term: TTerm | undefined): string | undefined {
  if (!term) return undefined;
  if (term.tag === 'Const') return term.name;
  return undefined;
}

/**
 * Convert a list of TacticCommands to a ProofNode tree.
 *
 * Each tactic wraps around the tree built from the remaining commands,
 * producing a nested structure matching the proof tree editor's model.
 */
export function tacticCommandsToProofTree(commands: readonly TacticCommand[]): ProofNode {
  if (commands.length === 0) return mkHole();

  const cmd = commands[0];
  const rest = commands.slice(1);

  switch (cmd.name) {
    case 'intro': {
      const name = extractName(cmd.args[0]) ?? '_';
      return mkIntros([name], tacticCommandsToProofTree(rest));
    }

    case 'intros': {
      const names = cmd.args.length > 0
        ? cmd.args.map(a => extractName(a) ?? '_')
        : ['_'];
      return mkIntros(names, tacticCommandsToProofTree(rest));
    }

    case 'exact':
      // Terminal — ignore remaining commands
      return mkExact(cmd.args.length > 0 ? surfaceTermToString(cmd.args[0]) : '?');

    case 'apply': {
      const name = cmd.args.length > 0 ? surfaceTermToString(cmd.args[0]) : '?';
      return mkApply(name, [tacticCommandsToProofTree(rest)]);
    }

    case 'cases':
    case 'induction':
      return buildInductionNode(cmd);

    case 'rewrite': {
      const name = cmd.args.length > 0 ? surfaceTermToString(cmd.args[0]) : '?';
      return mkRewrite(name, tacticCommandsToProofTree(rest));
    }

    case 'rw': {
      // rw/erw auto-close with refl when they're the last tactic
      const rwCont = rest.length > 0 ? tacticCommandsToProofTree(rest) : mkExact('refl');
      return buildRewriteChain(cmd.args, rwCont, false);
    }

    case 'erw': {
      const erwCont = rest.length > 0 ? tacticCommandsToProofTree(rest) : mkExact('refl');
      return buildRewriteChain(cmd.args, erwCont, true);
    }

    case 'unfold':
      return buildUnfoldChain(cmd.args, tacticCommandsToProofTree(rest));

    case 'fold':
      return buildFoldChain(cmd.args, tacticCommandsToProofTree(rest));

    case 'constructor': {
      // constructor is like apply with the single constructor of the goal type.
      // Subgoals can come from:
      // 1. Inline focusedTactics on the constructor command itself
      // 2. Separate `focus` commands that follow in `rest`
      // 3. Neither (single child from remaining commands)
      let children: ProofNode[];
      if (cmd.focusedTactics && cmd.focusedTactics.length > 0) {
        children = cmd.focusedTactics.map(ft => tacticCommandsToProofTree([ft]));
      } else {
        // Collect consecutive `focus` commands from rest — these are the
        // · bullet subgoals parsed as separate tactic commands.
        const focusCommands: TacticCommand[] = [];
        let i = 0;
        while (i < rest.length && rest[i].name === 'focus') {
          focusCommands.push(rest[i]);
          i++;
        }
        if (focusCommands.length > 0) {
          const afterFocus = rest.slice(focusCommands.length);
          children = focusCommands.map(fc => {
            const inner = fc.focusedTactics ?? [];
            return tacticCommandsToProofTree([...inner, ...afterFocus]);
          });
        } else {
          children = [tacticCommandsToProofTree(rest)];
        }
      }
      return mkApply('constructor', children);
    }

    case 'suffices': {
      // suffices h : T by proof → args[0]=name, args[1]=type
      // The "by proof" is in focusedTactics — the proof that original goal follows from h
      const suffName = cmd.args.length > 0 ? extractName(cmd.args[0]) ?? 'h' : 'h';
      const suffType = cmd.args.length > 1 ? surfaceTermToString(cmd.args[1]) : '?';
      const byProof = cmd.focusedTactics && cmd.focusedTactics.length > 0
        ? tacticCommandsToProofTree(cmd.focusedTactics)
        : undefined;
      return mkSuffices(suffName, suffType, tacticCommandsToProofTree(rest), byProof);
    }

    case 'have': {
      // have name : type := proof → args[0]=name, args[1]=type, args[2]=proof
      const haveName = cmd.args.length > 0 ? extractName(cmd.args[0]) ?? '_' : '_';
      // args[2] is the proof expression
      const haveExpr = cmd.args.length > 2 ? surfaceTermToString(cmd.args[2]) : '?';
      return mkHave(haveName, haveExpr, tacticCommandsToProofTree(rest));
    }

    default:
      // Unsupported tactics (obtain, suffices, symmetry, reflexivity, etc.)
      // Skip and continue with remaining commands
      return tacticCommandsToProofTree(rest);
  }
}

/** Map Unicode Greek → LaTeX for case label rendering. */
const LABEL_GREEK: Record<string, string> = {
  'α': '\\alpha', 'β': '\\beta', 'γ': '\\gamma', 'δ': '\\delta',
  'ε': '\\varepsilon', 'ζ': '\\zeta', 'η': '\\eta', 'θ': '\\theta',
  'λ': '\\lambda', 'μ': '\\mu', 'π': '\\pi', 'σ': '\\sigma',
  'φ': '\\varphi', 'ψ': '\\psi', 'ω': '\\omega',
};

/** Render a variable name for a case label, matching texNameForProse conventions. */
function labelVarName(name: string): string {
  if (name.length === 1 && LABEL_GREEK[name]) return LABEL_GREEK[name];
  if (name.length >= 2 && LABEL_GREEK[name[0]] && /^[a-zA-Z0-9]+$/.test(name.slice(1))) {
    return `${LABEL_GREEK[name[0]]}_{${name.slice(1)}}`;
  }
  if (name.length === 1) return name;
  if (/^[a-zA-Z]\d+$/.test(name)) return `{${name[0]}}_{${name.slice(1)}}`;
  // Escape underscores so KaTeX doesn't read them as subscript
  return `\\textsf{${name.replace(/_/g, '\\_')}}`;
}

/** Recursively render a CasePattern to LaTeX. Nested constructor patterns get parenthesized. */
function formatPatternLatex(p: CasePattern): string {
  if (p.tag === 'var') return labelVarName(p.name);
  const ctor = `\\text{${p.constructor}}`;
  if (p.params.length === 0) return ctor;
  const inner = p.params.map(formatPatternLatex).join('\\,');
  return `(${ctor}\\,${inner})`;
}

/** Format the label for a case branch that has at least one nested constructor pattern. */
function formatNestedCaseLabelLatex(ctorName: string, patterns: readonly CasePattern[]): string {
  const ctor = `\\text{${ctorName}}`;
  if (patterns.length === 0) return ctor;
  const inner = patterns.map(formatPatternLatex).join('\\,');
  return `${ctor}\\,${inner}`;
}

/** Does this case branch contain any nested constructor patterns? */
function hasNestedPattern(params: readonly CasePattern[]): boolean {
  return params.some(p => p.tag === 'ctor');
}

/** Build an InductionNode from a cases/induction command with case branches. */
function buildInductionNode(cmd: TacticCommand): ProofNode {
  // Use full expression string for complex scrutinees (e.g., cases (leTotal ...))
  const scrutinee = cmd.args.length > 0
    ? (extractName(cmd.args[0]) ?? surfaceTermToString(cmd.args[0]))
    : '_';

  const isCases = cmd.name === 'cases';

  if (!cmd.caseBranches || cmd.caseBranches.length === 0) {
    // No structured cases — just a hole
    return mkInduction(scrutinee, [mkCase('?', mkHole())], isCases);
  }

  const cases = cmd.caseBranches.map(rawBranch => {
    const branch = desugarNestedCaseBranch(rawBranch);
    const body = tacticCommandsToProofTree(branch.tactics);
    if (hasNestedPattern(rawBranch.params)) {
      // Nested pattern — show the user's original nesting in the label and skip
      // flat paramNames (which would leak synthetic `_nested*` names into the UI).
      // The static `nestedLabel` is a fallback for contexts without a registry;
      // goal-computation replaces it with a @syntax-aware version when replaying.
      const nestedLabel = formatNestedCaseLabelLatex(rawBranch.constructor, rawBranch.params);
      return mkCase(
        rawBranch.constructor, body,
        rawBranch.constructor, undefined,
        nestedLabel, rawBranch.params,
      );
    }
    const flatParams = allPatternVarNames(branch.params);
    // Generate a labelLatex so the case header and right-panel CASE section
    // always have a properly rendered label (not raw text).
    const flatLabel = formatNestedCaseLabelLatex(rawBranch.constructor, rawBranch.params);
    return mkCase(rawBranch.constructor, body, rawBranch.constructor, flatParams, flatLabel);
  });

  return mkInduction(scrutinee, cases, isCases);
}

/** Build a chain of RewriteNodes from multiple rw/erw arguments. */
function buildRewriteChain(args: readonly TTerm[], continuation: ProofNode, enhanced: boolean): ProofNode {
  if (args.length === 0) return continuation;
  let result = continuation;
  for (let i = args.length - 1; i >= 0; i--) {
    result = mkRewrite(surfaceTermToString(args[i]), result, false, undefined, undefined, enhanced);
  }
  return result;
}

/** Build a chain of UnfoldNodes from multiple unfold arguments. */
function buildUnfoldChain(args: readonly TTerm[], continuation: ProofNode): ProofNode {
  if (args.length === 0) return continuation;
  let result = continuation;
  for (let i = args.length - 1; i >= 0; i--) {
    result = mkUnfold(extractName(args[i]) ?? '?', result);
  }
  return result;
}

/** Build a chain of FoldNodes from multiple fold arguments. */
function buildFoldChain(args: readonly TTerm[], continuation: ProofNode): ProofNode {
  if (args.length === 0) return continuation;
  let result = continuation;
  for (let i = args.length - 1; i >= 0; i--) {
    result = mkFold(extractName(args[i]) ?? '?', result);
  }
  return result;
}

/** Find the first HoleNode in a tree (depth-first). */
export function findFirstHole(node: ProofNode): ProofNode | null {
  if (node.tag === 'hole') return node;

  switch (node.tag) {
    case 'exact':
      return null;
    case 'intros':
    case 'unfold':
    case 'fold':
    case 'rewrite':
    case 'have':
    case 'suffices':
      return findFirstHole(node.child);
    case 'simp':
      return findFirstHole(node.child);
    case 'induction':
      for (const c of node.cases) {
        const found = findFirstHole(c.body);
        if (found) return found;
      }
      return null;
    case 'apply':
      for (const child of node.children) {
        const found = findFirstHole(child);
        if (found) return found;
      }
      return null;
  }
}
