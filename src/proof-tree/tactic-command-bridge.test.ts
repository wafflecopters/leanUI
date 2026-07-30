import { beforeEach, describe, expect, test } from 'vitest';
import { flatParamsToCasePatterns, type TacticCommand } from './tactic-command';
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
  buildCaseBranchFromCaseNode,
  buildApplyTacticCommands,
  buildHaveTacticCommands,
  buildInductionTacticCommands,
  proofTreeToTacticCommands,
  rebuildInductionNodeFromCaseBranches,
} from './tactic-command-bridge';

const cst = (name: string): string => name;
const app = (fn: string, arg: string): string => `(${fn} ${arg})`;

function tc(name: string, args: string[] = [], opts?: Partial<TacticCommand>): TacticCommand {
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

  test('buildHaveTacticCommands creates a source-shaped have fragment at the cursor', () => {
    const state = createInitialState();
    const next = applyTacticCommandsAtCursor(state, buildHaveTacticCommands('h', 'refl'));

    expect(next).not.toBeNull();
    expect(next?.root.tag).toBe('have');
    if (!next || next.root.tag !== 'have') return;
    expect(next.root.name).toBe('h');
    expect(next.root.expr).toBe('refl');
  });
});

describe('proofTreeToTacticCommands', () => {
  test('shared induction command builder preserves cases mode and branch params', () => {
    const commands = buildInductionTacticCommands('n', [
      { constructorName: 'Zero', paramNames: [] },
      { constructorName: 'Succ', paramNames: ['k'] },
    ], 'cases');

    expect(commands).toHaveLength(1);
    expect(commands[0].name).toBe('cases');
    expect(commands[0].caseBranches).toEqual([
      { constructor: 'Zero', params: [], tactics: [] },
      {
        constructor: 'Succ',
        params: [{ tag: 'var', name: 'k' }],
        tactics: [],
      },
    ]);

    const reparsed = tacticCommandsToProofTree(commands);
    expect(reparsed.tag).toBe('induction');
    if (reparsed.tag !== 'induction') return;
    expect(reparsed.isCases).toBe(true);
    expect(reparsed.cases[1].constructorParamNames).toEqual(['k']);
  });

  test('rebuilding induction branches preserves existing branch bodies and collapse state', () => {
    const firstBody = mkExact('refl');
    const secondBody = mkHole();
    const firstCase = { ...mkCase('n = Zero', firstBody, 'Zero', []), collapsed: true };
    const secondCase = mkCase('n = Succ k', secondBody, 'Succ', ['k']);
    const node = mkInduction('n', [firstCase, secondCase], true);

    const rebuilt = rebuildInductionNodeFromCaseBranches(node, [
      buildCaseBranchFromCaseNode(firstCase),
      {
        constructor: 'Succ',
        params: [{ tag: 'var', name: 'j' }],
        tactics: [],
      },
    ]);

    expect(rebuilt.isCases).toBe(true);
    expect(rebuilt.cases[0].body.id).toBe(firstBody.id);
    expect(rebuilt.cases[0].collapsed).toBe(true);
    expect(rebuilt.cases[1].body.id).toBe(secondBody.id);
    expect(rebuilt.cases[1].constructorParamNames).toEqual(['j']);
  });

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

  test('serializes source-shaped simp node without flattening it away', () => {
    const tree: ProofNode = {
      tag: 'simp',
      id: 1001,
      lemmas: ['foo', 'bar'],
      steps: [],
      collapsed: true,
      child: mkExact('refl'),
    };
    const commands = proofTreeToTacticCommands(tree);

    expect(commands[0].name).toBe('simp');
    expect(commands[0].args).toEqual([cst('foo'), cst('bar')]);

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
