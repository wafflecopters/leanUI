import { describe, test, expect } from 'vitest';
import { elaborateTacticArg, tacticCommandToTactic, shouldKeepArgAsName } from './elaborate-tactic-arg';
import { createDefinitionsMap, addDefinition } from '../compiler/term';
import { TTKTerm } from '../compiler/kernel';
import { TTerm } from '../compiler/surface';

const natType: TTKTerm = { tag: 'Const', name: 'Nat' };

describe('elaborateTacticArg', () => {
  test('resolves context variable to Var with correct de Bruijn index', () => {
    const ctx = [
      { name: 'x', type: natType },
      { name: 'y', type: natType },
    ];
    // 'y' is at position 1 (last), de Bruijn index 0
    const result = elaborateTacticArg({ tag: 'Const', name: 'y' }, ctx, createDefinitionsMap());
    expect(result).toEqual({ tag: 'Var', index: 0 });
  });

  test('resolves earlier context variable with higher index', () => {
    const ctx = [
      { name: 'x', type: natType },
      { name: 'y', type: natType },
    ];
    // 'x' is at position 0, de Bruijn index 1
    const result = elaborateTacticArg({ tag: 'Const', name: 'x' }, ctx, createDefinitionsMap());
    expect(result).toEqual({ tag: 'Var', index: 1 });
  });

  test('keeps unknown name as Const', () => {
    const ctx = [{ name: 'x', type: natType }];
    const result = elaborateTacticArg({ tag: 'Const', name: 'Succ' }, ctx, createDefinitionsMap());
    expect(result.tag).toBe('Const');
    expect((result as any).name).toBe('Succ');
  });

  test('elaborates App with context resolution', () => {
    const ctx = [{ name: 'n', type: natType }];
    const term: TTerm = {
      tag: 'App',
      fn: { tag: 'Const', name: 'Succ' },
      arg: { tag: 'Const', name: 'n' },
    };
    const result = elaborateTacticArg(term, ctx, createDefinitionsMap());
    expect(result.tag).toBe('App');
    expect((result as any).fn.tag).toBe('Const');
    expect((result as any).fn.name).toBe('Succ');
    expect((result as any).arg).toEqual({ tag: 'Var', index: 0 });
  });

  test('lambda body resolves binder variable at depth 0', () => {
    const ctx: any[] = [];
    const term: TTerm = {
      tag: 'Binder',
      name: 'y',
      binderKind: { tag: 'BLamTT' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'y' },
    };
    const result = elaborateTacticArg(term, ctx, createDefinitionsMap());
    expect(result.tag).toBe('Binder');
    expect((result as any).body).toEqual({ tag: 'Var', index: 0 });
  });

  test('lambda body resolves outer context variable with shift', () => {
    const ctx = [{ name: 'x', type: natType }];
    const term: TTerm = {
      tag: 'Binder',
      name: 'y',
      binderKind: { tag: 'BLamTT' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'x' },  // x from outer context
    };
    const result = elaborateTacticArg(term, ctx, createDefinitionsMap());
    expect(result.tag).toBe('Binder');
    // x is at ctx position 0, nameContext has ['x', 'y'], so index = 1 - 0 + depth(0) = 1
    expect((result as any).body).toEqual({ tag: 'Var', index: 1 });
  });

  test('inserts implicit holes for Const with namedArgMap', () => {
    let defs = createDefinitionsMap();
    const justType: TTKTerm = {
      tag: 'Binder', binderKind: { tag: 'BPi' }, name: 'A',
      domain: { tag: 'Sort', level: { tag: 'ULit', n: 1 } },
      body: { tag: 'Binder', binderKind: { tag: 'BPi' }, name: 'a',
        domain: { tag: 'Var', index: 0 },
        body: { tag: 'Const', name: 'Maybe' } },
    };
    const namedArgMap = new Map([['A', 0]]);
    defs = addDefinition(defs, 'Just', justType, undefined, namedArgMap);

    const term: TTerm = {
      tag: 'App',
      fn: { tag: 'Const', name: 'Just' },
      arg: { tag: 'Const', name: 'Zero' },
    };
    const result = elaborateTacticArg(term, [], defs);
    // Should be App(App(Just, Hole), Zero)
    expect(result.tag).toBe('App');
    expect((result as any).arg.tag).toBe('Const');
    expect((result as any).arg.name).toBe('Zero');
    expect((result as any).fn.tag).toBe('App');
    expect((result as any).fn.arg.tag).toBe('Hole');
  });

  test('Hole passes through', () => {
    const result = elaborateTacticArg({ tag: 'Hole', id: 'test', type: { tag: 'Const', name: '_' } as any, context: [] as any } as any, [], createDefinitionsMap());
    expect(result).toEqual({ tag: 'Hole', id: 'test' });
  });
});

describe('shouldKeepArgAsName', () => {
  test('intro args are kept', () => {
    expect(shouldKeepArgAsName('intro', 0, 1)).toBe(true);
    expect(shouldKeepArgAsName('intros', 0, 2)).toBe(true);
  });

  test('exact args are elaborated', () => {
    expect(shouldKeepArgAsName('exact', 0, 1)).toBe(false);
  });

  test('have arg[0] is name, others elaborated', () => {
    expect(shouldKeepArgAsName('have', 0, 3)).toBe(true);
    expect(shouldKeepArgAsName('have', 1, 3)).toBe(false);
    expect(shouldKeepArgAsName('have', 2, 3)).toBe(false);
  });

  test('obtain: all but last are names', () => {
    expect(shouldKeepArgAsName('obtain', 0, 3)).toBe(true);
    expect(shouldKeepArgAsName('obtain', 1, 3)).toBe(true);
    expect(shouldKeepArgAsName('obtain', 2, 3)).toBe(false);
  });
});

describe('tacticCommandToTactic', () => {
  test('exact creates ExactTactic', () => {
    const t = tacticCommandToTactic({ name: 'exact', args: [{ tag: 'Const', name: 'refl' }] });
    expect(t).not.toBe('sorry');
    expect((t as any).name).toBe('exact');
  });

  test('intros creates IntrosTactic', () => {
    const t = tacticCommandToTactic({
      name: 'intros',
      args: [{ tag: 'Const', name: 'x' }, { tag: 'Const', name: 'y' }],
    });
    expect(t).not.toBe('sorry');
    expect((t as any).name).toBe('intros');
  });

  test('sorry returns string', () => {
    expect(tacticCommandToTactic({ name: 'sorry', args: [] })).toBe('sorry');
  });

  test('constructor creates ConstructorTactic', () => {
    const t = tacticCommandToTactic({ name: 'constructor', args: [] });
    expect(t).not.toBe('sorry');
    expect((t as any).name).toBe('constructor');
  });

  test('unknown tactic throws', () => {
    expect(() => tacticCommandToTactic({ name: 'bogus', args: [] })).toThrow('Unknown tactic');
  });
});
