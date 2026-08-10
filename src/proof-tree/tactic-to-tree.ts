/**
 * Convert parsed TacticCommand[] to ProofNode tree.
 *
 * This enables pre-populating the proof tree editor when a declaration
 * uses tactic mode (`:= by ...`).
 */

import { TacticCommand, CasePattern, allPatternVarNames, desugarNestedCaseBranch } from './tactic-command';
import {
  ProofNode,
  mkDestructure,
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
  mkSimp,
  mkSuffices,
} from './proof-tree';
import { renderNameLatex } from './name-latex';

/**
 * A tactic argument IS its source text — see ./tactic-command. These two
 * helpers remain as named seams because call sites read better for it: one
 * means "this argument should be a bare identifier", the other "render this
 * argument for display".
 */
export function surfaceTermToString(arg: string): string {
  return arg;
}

function extractName(arg: string | undefined): string | undefined {
  return arg;
}

function buildFocusedChildren(
  cmd: TacticCommand,
  rest: readonly TacticCommand[],
): ProofNode[] | null {
  if (cmd.focusedTactics !== undefined) {
    return cmd.focusedTactics.map(ft => tacticCommandsToProofTree([ft]));
  }

  // Collect consecutive `focus` commands from rest — these are the
  // · bullet subgoals parsed as separate tactic commands.
  const focusCommands: TacticCommand[] = [];
  let i = 0;
  while (i < rest.length && rest[i].name === 'focus') {
    focusCommands.push(rest[i]);
    i++;
  }
  if (focusCommands.length === 0) return null;

  const afterFocus = rest.slice(focusCommands.length);
  return focusCommands.map(fc => {
    const inner = fc.focusedTactics ?? [];
    return tacticCommandsToProofTree([...inner, ...afterFocus]);
  });
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
      const children = buildFocusedChildren(cmd, rest) ?? [tacticCommandsToProofTree(rest)];
      return mkApply(name, children);
    }

    case 'cases':
    case 'induction':
      return buildInductionNode(cmd);

    case 'rewrite': {
      const name = cmd.args.length > 0 ? surfaceTermToString(cmd.args[0]) : '?';
      return mkRewrite(
        name,
        tacticCommandsToProofTree(rest),
        cmd.rewriteOptions?.reverse ?? false,
        cmd.rewriteOptions?.occurrences,
        cmd.rewriteOptions?.targetHead,
        cmd.rewriteOptions?.enhanced,
      );
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

    case 'obtain': {
      // One arg, shaped `⟨a, b⟩ := scrutinee` (built by the command bridge).
      // Falling through to default would DROP the destructure silently.
      const m = (cmd.args[0] ?? '').match(/^⟨([^⟩]*)⟩\s*:=\s*(.+)$/);
      if (m) {
        const names = m[1].split(',').map((x) => x.trim()).filter(Boolean);
        if (names.length > 0) {
          return mkDestructure(m[2].trim(), names, tacticCommandsToProofTree(rest));
        }
      }
      return tacticCommandsToProofTree(rest);
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
      const children = buildFocusedChildren(cmd, rest) ?? [tacticCommandsToProofTree(rest)];
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
      const haveName = cmd.args.length > 0 ? extractName(cmd.args[0]) ?? '_' : '_';
      if (cmd.focusedTactics && cmd.focusedTactics.length > 0) {
        const haveType = cmd.args.length > 1 ? surfaceTermToString(cmd.args[1]) : '?';
        const proofTree = tacticCommandsToProofTree(cmd.focusedTactics);
        return mkHave(haveName, '?', tacticCommandsToProofTree(rest), haveType, proofTree);
      }
      const haveExpr = cmd.args.length > 2 ? surfaceTermToString(cmd.args[2]) : '?';
      return mkHave(haveName, haveExpr, tacticCommandsToProofTree(rest));
    }

    case 'simp': {
      const lemmas = cmd.args.map(arg => extractName(arg) ?? surfaceTermToString(arg));
      return mkSimp(lemmas, [], tacticCommandsToProofTree(rest));
    }

    default:
      // Unsupported tactics (obtain, suffices, symmetry, reflexivity, etc.)
      // Skip and continue with remaining commands
      return tacticCommandsToProofTree(rest);
  }
}

/** Render a variable name for a case label. */
function labelVarName(name: string): string {
  return renderNameLatex(name, 'textsf');
}

/** Render a constructor name (Greek-safe). */
function ctorNameLatex(name: string): string {
  return renderNameLatex(name, 'text');
}

/** Recursively render a CasePattern to LaTeX. Nested constructor patterns get parenthesized. */
function formatPatternLatex(p: CasePattern): string {
  if (p.tag === 'var') return labelVarName(p.name);
  const ctor = ctorNameLatex(p.constructor);
  if (p.params.length === 0) return ctor;
  const inner = p.params.map(formatPatternLatex).join('\\,');
  return `(${ctor}\\,${inner})`;
}

/** Format the label for a case branch that has at least one nested constructor pattern. */
function formatNestedCaseLabelLatex(ctorName: string, patterns: readonly CasePattern[]): string {
  const ctor = ctorNameLatex(ctorName);
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
function buildRewriteChain(args: readonly string[], continuation: ProofNode, enhanced: boolean): ProofNode {
  if (args.length === 0) return continuation;
  let result = continuation;
  for (let i = args.length - 1; i >= 0; i--) {
    result = mkRewrite(surfaceTermToString(args[i]), result, false, undefined, undefined, enhanced);
  }
  return result;
}

/** Build a chain of UnfoldNodes from multiple unfold arguments. */
function buildUnfoldChain(args: readonly string[], continuation: ProofNode): ProofNode {
  if (args.length === 0) return continuation;
  let result = continuation;
  for (let i = args.length - 1; i >= 0; i--) {
    result = mkUnfold(extractName(args[i]) ?? '?', result);
  }
  return result;
}

/** Build a chain of FoldNodes from multiple fold arguments. */
function buildFoldChain(args: readonly string[], continuation: ProofNode): ProofNode {
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
    case 'destructure':
    case 'unfold':
    case 'fold':
      return findFirstHole(node.child);
    case 'rewrite': {
      // Main continuation first, then any conditional side-goal branches.
      const inChild = findFirstHole(node.child);
      if (inChild) return inChild;
      for (const sg of node.sideGoals ?? []) {
        const found = findFirstHole(sg);
        if (found) return found;
      }
      return null;
    }
    case 'have': {
      // A have's own proof subtree (e.g. a hoisted obligation) comes BEFORE
      // its continuation — proof order, and where the cursor should land.
      if (node.proofTree) {
        const found = findFirstHole(node.proofTree);
        if (found) return found;
      }
      return findFirstHole(node.child);
    }
    case 'suffices': {
      if (node.byProof) {
        const found = findFirstHole(node.byProof);
        if (found) return found;
      }
      return findFirstHole(node.child);
    }
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
