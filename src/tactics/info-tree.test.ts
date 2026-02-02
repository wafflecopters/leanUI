/**
 * Tests for InfoTree and execution with recording (Phase 3)
 */

import { describe, test, expect, beforeEach } from 'vitest';
import { createProofState } from './proof-state';
import { executeTacticsWithInfo, executeSingleTacticWithInfo } from './execute-with-info';
import { TacticInfoTree, createEmptyInfoTree } from './info-tree';
import { resetMetaCounter } from './tactic';
import { TTKTerm } from '../compiler/kernel';
import { DefinitionsMap } from '../compiler/term';

// Test helper: Create Nat definitions
function createNatDefinitions(): DefinitionsMap {
  const terms = new Map();
  const inductiveTypes = new Map();
  const inductiveNameOfConstructor = new Map();

  inductiveTypes.set('Nat', {
    parameters: [],
    type: { tag: 'Type', level: { tag: 'LevelConst', value: 0 } },
    constructors: [
      {
        name: 'Zero',
        type: { tag: 'Const', name: 'Nat' }
      },
      {
        name: 'Succ',
        type: {
          tag: 'Binder',
          name: '_',
          binderKind: { tag: 'BPi' },
          domain: { tag: 'Const', name: 'Nat' },
          body: { tag: 'Const', name: 'Nat' }
        }
      }
    ]
  });

  terms.set('Zero', {
    name: 'Zero',
    type: { tag: 'Const', name: 'Nat' },
    value: { tag: 'Const', name: 'Zero' }
  });
  inductiveNameOfConstructor.set('Zero', 'Nat');

  terms.set('Succ', {
    name: 'Succ',
    type: {
      tag: 'Binder',
      name: '_',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    },
    value: { tag: 'Const', name: 'Succ' }
  });
  inductiveNameOfConstructor.set('Succ', 'Nat');

  return { terms, inductiveTypes, inductiveNameOfConstructor };
}

describe('InfoTree creation and queries', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('createEmptyInfoTree creates tree with root', () => {
    const tree = createEmptyInfoTree([]);

    expect(tree.root).toBeDefined();
    expect(tree.root.children.length).toBe(0);
  });

  test('getAllNodes returns empty for empty tree', () => {
    const tree = createEmptyInfoTree([]);
    const nodes = tree.getAllNodes();

    expect(nodes.length).toBe(0);
  });

  test('findGoalsAtPosition returns null for position outside tree', () => {
    const tree = createEmptyInfoTree([]);
    const goals = tree.findGoalsAtPosition(100, 100);

    expect(goals).toBeNull();
  });
});

describe('executeTacticsWithInfo', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('executes simple proof and records InfoTree', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'n',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    };

    const state = createProofState(goalType, [], definitions);

    const result = executeTacticsWithInfo(state, [
      {
        expr: { tag: 'Intro', name: 'n' },
        position: { line: 1, col: 0 }
      },
      {
        expr: { tag: 'Exact', term: { tag: 'Var', index: 0 } },
        position: { line: 2, col: 0 }
      }
    ]);

    // Execution succeeded
    expect(result.error).toBeUndefined();

    // InfoTree has two nodes (one per tactic)
    const nodes = result.infoTree.getAllNodes();
    expect(nodes.length).toBe(2);

    // First node: intro
    expect(nodes[0].tactic.tag).toBe('Intro');
    expect(nodes[0].goalsBefore.length).toBe(1);
    expect(nodes[0].goalsAfter.length).toBe(1);
    expect(nodes[0].goalsAfter[0].hypotheses.length).toBe(1); // Added 'n'

    // Second node: exact
    expect(nodes[1].tactic.tag).toBe('Exact');
    expect(nodes[1].goalsBefore.length).toBe(1);
    expect(nodes[1].goalsAfter.length).toBe(0); // Goal solved
  });

  test('records error when tactic fails', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const state = createProofState(goalType, [], definitions);

    const result = executeTacticsWithInfo(state, [
      {
        expr: { tag: 'Intro' }, // Should fail - not a Pi type
        position: { line: 1, col: 0 }
      }
    ]);

    // Execution failed
    expect(result.error).toBeDefined();
    expect(result.error).toContain('not a function type');
    expect(result.errorPosition).toEqual({ line: 1, col: 0 });

    // InfoTree records the failed tactic
    const nodes = result.infoTree.getAllNodes();
    expect(nodes.length).toBe(1);
    expect(nodes[0].error).toBeDefined();
    expect(nodes[0].error).toContain('not a function type');
  });

  test('stops at first error and records partial execution', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'n',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    };

    const state = createProofState(goalType, [], definitions);

    const result = executeTacticsWithInfo(state, [
      {
        expr: { tag: 'Intro', name: 'n' },
        position: { line: 1, col: 0 }
      },
      {
        expr: { tag: 'Intro' }, // Should fail - goal is Nat, not Pi
        position: { line: 2, col: 0 }
      },
      {
        expr: { tag: 'Exact', term: { tag: 'Var', index: 0 } },
        position: { line: 3, col: 0 }
      }
    ]);

    // Failed at second tactic
    expect(result.error).toBeDefined();
    expect(result.errorPosition?.line).toBe(2);

    // InfoTree has two nodes (first succeeded, second failed)
    const nodes = result.infoTree.getAllNodes();
    expect(nodes.length).toBe(2);
    expect(nodes[0].error).toBeUndefined(); // First succeeded
    expect(nodes[1].error).toBeDefined(); // Second failed
  });
});

describe('InfoTree position queries', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('findGoalsAtPosition returns correct goals', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'a',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: {
        tag: 'Binder',
        name: 'b',
        binderKind: { tag: 'BPi' },
        domain: { tag: 'Const', name: 'Nat' },
        body: { tag: 'Const', name: 'Nat' }
      }
    };

    const state = createProofState(goalType, [], definitions);

    const result = executeTacticsWithInfo(state, [
      {
        expr: { tag: 'Intro', name: 'a' },
        position: { line: 1, col: 2, endLine: 1, endCol: 10 }
      },
      {
        expr: { tag: 'Intro', name: 'b' },
        position: { line: 2, col: 2, endLine: 2, endCol: 10 }
      }
    ]);

    expect(result.error).toBeUndefined();

    // Query position inside first tactic
    const goals1 = result.infoTree.findGoalsAtPosition(1, 5);
    expect(goals1).not.toBeNull();
    expect(goals1!.length).toBe(1);
    expect(goals1![0].hypotheses.length).toBe(1); // After intro a
    expect(goals1![0].hypotheses[0].name).toBe('a');

    // Query position inside second tactic
    const goals2 = result.infoTree.findGoalsAtPosition(2, 5);
    expect(goals2).not.toBeNull();
    expect(goals2!.length).toBe(1);
    expect(goals2![0].hypotheses.length).toBe(2); // After intro b
    expect(goals2![0].hypotheses[1].name).toBe('b');

    // Query position outside any tactic
    const goals3 = result.infoTree.findGoalsAtPosition(10, 0);
    expect(goals3).toBeNull();
  });

  test('findGoalsAtPosition returns most specific node', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'n',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    };

    const state = createProofState(goalType, [], definitions);

    const result = executeTacticsWithInfo(state, [
      {
        expr: { tag: 'Intro', name: 'n' },
        position: { line: 1, col: 0, endLine: 1, endCol: 10 }
      },
      {
        expr: { tag: 'Exact', term: { tag: 'Var', index: 0 } },
        position: { line: 2, col: 0, endLine: 2, endCol: 10 }
      }
    ]);

    // Position at line 1 returns state after intro
    const goals1 = result.infoTree.findGoalsAtPosition(1, 5);
    expect(goals1![0].hypotheses.length).toBe(1);

    // Position at line 2 returns state after exact (no goals)
    const goals2 = result.infoTree.findGoalsAtPosition(2, 5);
    expect(goals2!.length).toBe(0);
  });
});

describe('executeSingleTacticWithInfo', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('executes single tactic and returns node', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'n',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    };

    const state = createProofState(goalType, [], definitions);

    const { result, node } = executeSingleTacticWithInfo(
      state,
      { tag: 'Intro', name: 'n' },
      { line: 1, col: 0 }
    );

    expect(result.success).toBe(true);
    expect(node.tactic.tag).toBe('Intro');
    expect(node.goalsBefore.length).toBe(1);
    expect(node.goalsAfter.length).toBe(1);
    expect(node.goalsAfter[0].hypotheses.length).toBe(1);
  });

  test('records error for failed tactic', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const state = createProofState(goalType, [], definitions);

    const { result, node } = executeSingleTacticWithInfo(
      state,
      { tag: 'Intro' },
      { line: 1, col: 0 }
    );

    expect(result.success).toBe(false);
    expect(node.error).toBeDefined();
    expect(node.error).toContain('not a function type');
  });
});

describe('InfoTree statistics', () => {
  beforeEach(() => {
    resetMetaCounter();
  });

  test('getStatistics returns correct counts', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = {
      tag: 'Binder',
      name: 'n',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'Nat' }
    };

    const state = createProofState(goalType, [], definitions);

    const result = executeTacticsWithInfo(state, [
      {
        expr: { tag: 'Intro', name: 'n' },
        position: { line: 1, col: 0 }
      },
      {
        expr: { tag: 'Exact', term: { tag: 'Var', index: 0 } },
        position: { line: 2, col: 0 }
      }
    ]);

    const stats = result.infoTree.getStatistics();

    expect(stats.totalTactics).toBe(2);
    expect(stats.successfulTactics).toBe(2);
    expect(stats.failedTactics).toBe(0);
    expect(stats.maxGoalsAtOnce).toBe(1);
  });

  test('getStatistics includes failed tactics', () => {
    const definitions = createNatDefinitions();
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };

    const state = createProofState(goalType, [], definitions);

    const result = executeTacticsWithInfo(state, [
      {
        expr: { tag: 'Intro' }, // Will fail
        position: { line: 1, col: 0 }
      }
    ]);

    const stats = result.infoTree.getStatistics();

    expect(stats.totalTactics).toBe(1);
    expect(stats.successfulTactics).toBe(0);
    expect(stats.failedTactics).toBe(1);
  });
});
