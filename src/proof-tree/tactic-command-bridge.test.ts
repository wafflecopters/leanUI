import { beforeEach, describe, expect, test } from 'vitest';
import {
  mkConstTT,
  flatParamsToCasePatterns,
  type TacticCommand,
  type TTerm,
} from '../compiler/surface';
import {
  createInitialState,
  mkApply,
  mkCase,
  mkExact,
  mkHave,
  mkHole,
  mkInduction,
  mkIntros,
  mkRewrite,
  mkSuffices,
  resetProofIds,
  type ProofNode,
} from './proof-tree';
import { tacticCommandsToProofTree } from './tactic-to-tree';
import {
  applyTacticCommandsAtCursor,
  buildApplyTacticCommands,
  proofTreeToTacticCommands,
} from './tactic-command-bridge';

const cst = (name: string): TTerm => ({ tag: 'Const', name });
const app = (fn: TTerm, arg: TTerm): TTerm => ({ tag: 'App', fn, arg });

function tc(name: string, args: TTerm[] = [], opts?: Partial<TacticCommand>): TacticCommand {
  return { name, args, ...opts };
}

function stripIds(node: any): any {
  if (Array.isArray(node)) return node.map(stripIds);
  if (!node || typeof node !== 'object') return node;
  const out: Record<string, unknown> = {};
  for (const [k, v] of Object.entries(node)) {
    if (k === 'id') continue;
    if (k === 'labelLatex') continue;
    out[k] = stripIds(v);
  }
  if (out.isCases === false) delete out.isCases;
  if (typeof out.typeExpr === 'string') {
    out.typeExpr = (out.typeExpr as string).replace(/^\((.*)\)$/s, '$1');
  }
  return out;
}

beforeEach(() => resetProofIds());

describe('applyTacticCommandsAtCursor', () => {
  test('applies source-aligned intros command at the cursor', () => {
    const state = createInitialState();
    const next = applyTacticCommandsAtCursor(state, [
      tc('intros', [cst('n'), cst('m')]),
    ]);

    expect(next).not.toBeNull();
    expect(next?.root.tag).toBe('intros');
    if (!next || next.root.tag !== 'intros') return;
    expect(next.root.names).toEqual(['n', 'm']);
    expect(next.root.child.tag).toBe('hole');
    expect(next.cursor.nodeId).toBe(next.root.child.id);
  });

  test('apply with explicit subgoal placeholders creates matching child holes', () => {
    const state = createInitialState();
    const next = applyTacticCommandsAtCursor(
      state,
      buildApplyTacticCommands('sym', 2),
    );

    expect(next).not.toBeNull();
    expect(next?.root.tag).toBe('apply');
    if (!next || next.root.tag !== 'apply') return;
    expect(next.root.name).toBe('sym');
    expect(next.root.children).toHaveLength(2);
    expect(next.root.children.every(child => child.tag === 'hole')).toBe(true);
    expect(next.cursor.nodeId).toBe(next.root.children[0].id);
  });

  test('apply with zero subgoals produces a closed apply node', () => {
    const state = createInitialState();
    const next = applyTacticCommandsAtCursor(
      state,
      buildApplyTacticCommands('zeroLeOne', 0),
    );

    expect(next).not.toBeNull();
    expect(next?.root.tag).toBe('apply');
    if (!next || next.root.tag !== 'apply') return;
    expect(next.root.children).toHaveLength(0);
    expect(next.cursor.nodeId).toBe(next.root.id);
  });
});

describe('proofTreeToTacticCommands', () => {
  test('roundtrips intros + apply + focused children through shared command bridge', () => {
    const tree: ProofNode = mkIntros(['n'], mkApply('sym', [
      mkExact('refl'),
      mkHole(),
    ]));

    const commands = proofTreeToTacticCommands(tree);
    const reparsed = tacticCommandsToProofTree(commands);

    expect(stripIds(reparsed)).toEqual(stripIds(tree));
  });

  test('roundtrips induction case branches through shared command bridge', () => {
    const tree: ProofNode = mkInduction('n', [
      mkCase('Zero', mkExact('refl'), 'Zero', []),
      mkCase('Succ', mkIntros(['k', 'IH'], mkHole()), 'Succ', ['k', 'IH']),
    ]);

    const commands = proofTreeToTacticCommands(tree);
    const reparsed = tacticCommandsToProofTree(commands);

    expect(stripIds(reparsed)).toEqual(stripIds(tree));
  });

  test('roundtrips rewrite metadata needed by structured suggestions', () => {
    const tree = mkRewrite('mulOneRight', mkExact('refl'), true, [1], 'two', true);

    const commands = proofTreeToTacticCommands(tree);
    expect(commands[0].rewriteOptions).toEqual({
      reverse: true,
      occurrences: [1],
      targetHead: 'two',
      enhanced: true,
    });

    const reparsed = tacticCommandsToProofTree(commands);
    expect(stripIds(reparsed)).toEqual(stripIds(tree));
  });

  test('serializes suffices closing proof and continuation', () => {
    const tree = mkSuffices('h', 'Equal n n', mkExact('h'), mkExact('refl'));
    const commands = proofTreeToTacticCommands(tree);

    expect(commands).toHaveLength(2);
    expect(commands[0].name).toBe('suffices');
    expect(commands[0].focusedTactics?.[0]?.name).toBe('exact');

    const reparsed = tacticCommandsToProofTree(commands);
    expect(stripIds(reparsed)).toEqual(stripIds(tree));
  });

  test('serializes interactive have proof and continuation', () => {
    const tree = mkHave('h', '?', mkExact('h'), 'Equal Zero Zero', mkExact('refl'));
    const commands = proofTreeToTacticCommands(tree);

    expect(commands).toHaveLength(2);
    expect(commands[0].name).toBe('have');
    expect(commands[0].args).toHaveLength(2);
    expect(commands[0].focusedTactics?.[0]?.name).toBe('exact');

    const reparsed = tacticCommandsToProofTree(commands);
    expect(stripIds(reparsed)).toEqual(stripIds(tree));
  });

  test('preserves parser-shaped focus children emitted after apply', () => {
    const commands: TacticCommand[] = [
      tc('apply', [cst('sym')]),
      { name: 'focus', args: [], focusedTactics: [tc('exact', [cst('refl')])] },
      { name: 'focus', args: [], focusedTactics: [tc('exact', [app(cst('f'), cst('x'))])] },
    ];

    const tree = tacticCommandsToProofTree(commands);
    expect(tree.tag).toBe('apply');
    if (tree.tag !== 'apply') return;
    expect(tree.children).toHaveLength(2);

    const roundtripped = proofTreeToTacticCommands(tree);
    const reparsed = tacticCommandsToProofTree(roundtripped);
    expect(stripIds(reparsed)).toEqual(stripIds(tree));
  });

  test('flattens simp nodes into shared text-compatible command sequences', () => {
    const simpTree: ProofNode = {
      tag: 'simp',
      id: 999,
      lemmas: ['h1'],
      steps: [
        mkRewrite('h1', mkHole()),
      ],
      collapsed: true,
      child: mkExact('refl'),
    };

    const commands = proofTreeToTacticCommands(simpTree);
    expect(commands.map(cmd => cmd.name)).toEqual(['rewrite', 'exact']);
  });
});
