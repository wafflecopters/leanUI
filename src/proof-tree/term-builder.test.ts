import { describe, expect, test } from 'vitest';
import type { MetaVar } from '../compiler/term';
import { addDefinition, createDefinitionsMap } from '../compiler/term';
import type { TTKContext, TTKTerm } from '../compiler/kernel';
import { createInitialEngine } from '../tactics/tacticsEngine';
import {
  clearTermBuilderSlot,
  computeTermSlots,
  fillTermBuilderSlotFromSource,
  openTermBuilderFromSourceExpr,
  rebuildTermBuilderWithFilledSlot,
  rebuildTermBuilderWithoutSlot,
} from './term-builder';

const nat: TTKTerm = { tag: 'Const', name: 'Nat' };

function mkPi(name: string, domain: TTKTerm, body: TTKTerm): TTKTerm {
  return { tag: 'Binder', binderKind: { tag: 'BPi' }, name, domain, body };
}

describe('term-builder rebuild helpers', () => {
  test('fill/clear helpers preserve source expressions and serialized exprs', () => {
    let defs = createDefinitionsMap();
    defs = addDefinition(
      defs,
      'pairNat',
      mkPi('x', nat, mkPi('y', nat, nat)),
    );

    const ctx: TTKContext = [{ name: 'n', type: nat }];
    const goalMeta: MetaVar = { ctx, type: nat, solution: undefined };
    const engine = createInitialEngine(nat, ctx, defs);

    const initial = computeTermSlots('pairNat', new Map(), engine, goalMeta, defs);
    expect(initial).not.toBeNull();
    if (!initial) return;

    const afterFirstFill = rebuildTermBuilderWithFilledSlot(
      initial,
      0,
      'n',
      engine,
      goalMeta,
      defs,
    );
    expect(afterFirstFill).not.toBeNull();
    if (!afterFirstFill) return;
    expect(afterFirstFill.builderState.slots[0].sourceExpr).toBe('n');
    expect(afterFirstFill.expr).toBe('pairNat (n) ?');

    const afterSecondFill = rebuildTermBuilderWithFilledSlot(
      afterFirstFill.builderState,
      1,
      'n',
      engine,
      goalMeta,
      defs,
    );
    expect(afterSecondFill).not.toBeNull();
    if (!afterSecondFill) return;
    expect(afterSecondFill.builderState.slots[0].sourceExpr).toBe('n');
    expect(afterSecondFill.builderState.slots[1].sourceExpr).toBe('n');
    expect(afterSecondFill.expr).toBe('pairNat (n) (n)');

    const afterClear = rebuildTermBuilderWithoutSlot(
      afterSecondFill.builderState,
      0,
      engine,
      goalMeta,
      defs,
    );
    expect(afterClear).not.toBeNull();
    if (!afterClear) return;
    expect(afterClear.builderState.slots[0].value).toBeNull();
    expect(afterClear.builderState.slots[1].sourceExpr).toBe('n');
    expect(afterClear.expr).toBe('pairNat ? (n)');
  });

  test('shared runtime wrappers delegate slot fill/clear through one path', () => {
    let defs = createDefinitionsMap();
    defs = addDefinition(
      defs,
      'pairNat',
      mkPi('x', nat, mkPi('y', nat, nat)),
    );

    const ctx: TTKContext = [{ name: 'n', type: nat }];
    const goalMeta: MetaVar = { ctx, type: nat, solution: undefined };
    const engine = createInitialEngine(nat, ctx, defs);

    const initial = computeTermSlots('pairNat', new Map(), engine, goalMeta, defs);
    expect(initial).not.toBeNull();
    if (!initial) return;

    const runtime = { engine, goal: goalMeta, definitions: defs };
    const filled = fillTermBuilderSlotFromSource(initial, 0, 'n', runtime);
    expect(filled).not.toBeNull();
    if (!filled) return;
    expect(filled.builderState.slots[0].sourceExpr).toBe('n');
    expect(filled.expr).toBe('pairNat (n) ?');

    const cleared = clearTermBuilderSlot(filled.builderState, 0, runtime);
    expect(cleared).not.toBeNull();
    if (!cleared) return;
    expect(cleared.builderState.slots[0].value).toBeNull();
    expect(cleared.expr).toBe('pairNat ? ?');
  });

  test('openTermBuilderFromSourceExpr rehydrates filled slot source expressions', () => {
    let defs = createDefinitionsMap();
    defs = addDefinition(
      defs,
      'pairNat',
      mkPi('x', nat, mkPi('y', nat, nat)),
    );

    const ctx: TTKContext = [{ name: 'n', type: nat }];
    const goalMeta: MetaVar = { ctx, type: nat, solution: undefined };
    const engine = createInitialEngine(nat, ctx, defs);

    const opened = openTermBuilderFromSourceExpr('pairNat n ?', {
      engine,
      goal: goalMeta,
      definitions: defs,
    });
    expect(opened).not.toBeNull();
    if (!opened) return;
    expect(opened.builderState.fnName).toBe('pairNat');
    expect(opened.builderState.slots[0].sourceExpr).toBe('n');
    expect(opened.builderState.slots[1].value).toBeNull();
    expect(opened.expr).toBe('pairNat n ?');
  });
});
