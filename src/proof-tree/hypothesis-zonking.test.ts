/**
 * Test that hypothesis types are properly zonked before rendering,
 * preventing grey boxes (squares) from appearing in the proof context panel.
 *
 * Bug: When `have h := f args` infers a type with implicit args, the inferred
 * type may contain Meta tags that weren't resolved yet (constraints created but
 * not solved). kernelTypeToSurface had no Meta case, converting them to
 * mkHoleTT('_unsupported_Meta'), which renders as grey squares.
 */
import { describe, test, expect, beforeEach } from 'vitest';
import { compileTTFromText } from '../compiler/compile';
import { createInitialEngine } from '../tactics/tacticsEngine';
import { IntrosTactic } from '../tactics/tactic';
import { HaveTactic } from '../tactics/have-tactic';
import { TTKTerm, mkConst, mkApp, mkMeta } from '../compiler/kernel';
import { kernelTypeToSurface } from './goal-computation';
import { resetProofIds } from './proof-tree';
import { resetIds } from '../math-editor/types';

beforeEach(() => {
  resetProofIds();
  resetIds();
});

describe('kernelTypeToSurface handles Meta tags', () => {
  test('Meta tag is converted to Hole (not _unsupported_Meta)', () => {
    // A Meta tag should produce a Hole, not an unsupported marker
    const meta: TTKTerm = { tag: 'Meta', id: 'test_meta' };
    const surface = kernelTypeToSurface(meta);
    expect(surface.tag).toBe('Hole');
    // Should NOT have the _unsupported prefix
    expect((surface as any).id).not.toContain('_unsupported');
  });

  test('App with Meta arg does not produce _unsupported', () => {
    // Simulate rzero(?m_R) — App(Const("rzero"), Meta("?m_R"))
    const term: TTKTerm = mkApp(mkConst('rzero'), { tag: 'Meta', id: '?m_R' });
    const surface = kernelTypeToSurface(term);
    // The arg should be a Hole, not _unsupported_Meta
    expect(surface.tag).toBe('App');
    if (surface.tag === 'App') {
      expect((surface as any).arg.tag).toBe('Hole');
      expect((surface as any).arg.id).not.toContain('_unsupported');
    }
  });
});

describe('have tactic hypothesis types are zonked', () => {
  test('inferred hypothesis type has no unsolved metas after have', () => {
    // Compile a minimal program with an implicit-arg function
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

myId : {A : Type} -> A -> A
myId x = x

test : Nat -> Nat := by
  intro n
  exact n
`;
    const result = compileTTFromText(source);
    expect(result.success).toBe(true);

    const testDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'test');
    expect(testDecl).toBeDefined();
    expect(testDecl!.kernelType).toBeDefined();

    const definitions = result.definitions;
    const kernelType = testDecl!.kernelType!;

    // Create engine and intro n
    let engine = createInitialEngine(kernelType, [], definitions);
    const goalId = engine.getFocusedGoalId()!;
    const goal = engine.getFocusedGoal()!;

    const introResult = new IntrosTactic(['n']).apply(engine, goal, goalId);
    expect(introResult.success).toBe(true);
    if (!introResult.success) return;
    engine = introResult.newEngine;

    // Now apply: have h := myId _ n
    // At the kernel level, we pass a Hole for the implicit {A} arg.
    // The type checker will create a meta from this Hole during inference,
    // and constraint solving should resolve it to Nat.
    const goalId2 = engine.getFocusedGoalId()!;
    const goal2 = engine.getFocusedGoal()!;

    const holeA: TTKTerm = { tag: 'Hole', id: '_have_A' };
    const proofTerm: TTKTerm = mkApp(mkApp(mkConst('myId'), holeA), { tag: 'Var', index: 0 });
    const haveTactic = new HaveTactic('h', { tag: 'Hole', id: '_' }, proofTerm);
    const haveResult = haveTactic.apply(engine, goal2, goalId2);
    expect(haveResult.success).toBe(true);
    if (!haveResult.success) return;
    engine = haveResult.newEngine;

    // Check the hypothesis type for 'h'
    const goalId3 = engine.getFocusedGoalId()!;
    const goal3 = engine.getFocusedGoal()!;

    // Find the 'h' context entry (last one added)
    const hEntry = goal3.ctx.find(e => e.name === 'h');
    expect(hEntry).toBeDefined();

    // The type should be Nat (fully resolved), not contain any Meta tags
    function containsMeta(t: TTKTerm): boolean {
      switch (t.tag) {
        case 'Meta': return true;
        case 'Hole': return false;
        case 'App': return containsMeta(t.fn) || containsMeta(t.arg);
        case 'Binder': return containsMeta(t.domain) || containsMeta(t.body);
        case 'Sort': return containsMeta(t.level);
        case 'Match': return containsMeta(t.scrutinee) || t.clauses.some(c => containsMeta(c.rhs));
        case 'Annot': return containsMeta(t.term) || containsMeta(t.type);
        default: return false;
      }
    }

    // After the fix, h's type should be Nat with no Metas
    expect(containsMeta(hEntry!.type)).toBe(false);

    // Also verify that kernelTypeToSurface doesn't produce squares
    const surface = kernelTypeToSurface(hEntry!.type, definitions);
    expect(JSON.stringify(surface)).not.toContain('_unsupported');
  });
});
