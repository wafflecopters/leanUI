/**
 * Convert parsed TacticCommand[] to ProofNode tree.
 *
 * This enables pre-populating the proof tree editor when a declaration
 * uses tactic mode (`:= by ...`).
 */

import { TacticCommand, TTerm } from '../compiler/surface';
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
} from './proof-tree';

/**
 * Render a surface TTerm to a string for display in proof tree nodes.
 * Handles the common cases seen in tactic arguments.
 */
export function surfaceTermToString(term: TTerm): string {
  switch (term.tag) {
    case 'Const':
      return term.name;
    case 'App': {
      // Collect spine: f a1 a2 a3 → "f a1 a2 a3" or "(f a1 a2 a3)"
      const parts: string[] = [];
      let cur: TTerm = term;
      while (cur.tag === 'App') {
        parts.unshift(surfaceTermToString(cur.arg));
        cur = cur.fn;
      }
      parts.unshift(surfaceTermToString(cur));
      return `(${parts.join(' ')})`;
    }
    case 'Binder':
      if (term.binderKind.tag === 'BLamTT') {
        return `(\\${term.name} => ${surfaceTermToString(term.body)})`;
      }
      return '?';
    case 'Var':
      return `#${term.index}`;
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

    case 'rw':
    case 'erw':
      return buildRewriteChain(cmd.args, tacticCommandsToProofTree(rest));

    case 'unfold':
      return buildUnfoldChain(cmd.args, tacticCommandsToProofTree(rest));

    case 'fold':
      return buildFoldChain(cmd.args, tacticCommandsToProofTree(rest));

    default:
      // Unsupported tactics (have, obtain, suffices, symmetry, reflexivity, etc.)
      // Skip and continue with remaining commands
      return tacticCommandsToProofTree(rest);
  }
}

/** Build an InductionNode from a cases/induction command with case branches. */
function buildInductionNode(cmd: TacticCommand): ProofNode {
  const scrutinee = extractName(cmd.args[0]) ?? '_';

  if (!cmd.caseBranches || cmd.caseBranches.length === 0) {
    // No structured cases — just a hole
    return mkInduction(scrutinee, [mkCase('?', mkHole())]);
  }

  const cases = cmd.caseBranches.map(branch => {
    const body = tacticCommandsToProofTree(branch.tactics);
    return mkCase(branch.constructor, body, branch.constructor, branch.params);
  });

  return mkInduction(scrutinee, cases);
}

/** Build a chain of RewriteNodes from multiple rw arguments. */
function buildRewriteChain(args: readonly TTerm[], continuation: ProofNode): ProofNode {
  if (args.length === 0) return continuation;
  let result = continuation;
  for (let i = args.length - 1; i >= 0; i--) {
    result = mkRewrite(surfaceTermToString(args[i]), result);
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
