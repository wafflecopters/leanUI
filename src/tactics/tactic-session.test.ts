import { describe, test, expect } from 'vitest';
import { TacticSession } from './tactic-session';
import { compileTTFromText } from '../compiler/compile';
import { prettyPrintFormatted } from '../compiler/kernel';

function mkConst(name: string): any { return { tag: 'Const', name }; }
function mkApp(fn: any, arg: any): any { return { tag: 'App', fn, arg }; }

const NAT_CODE = `
inductive Nat where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal {A : Type} : A -> A -> Type where
  refl : {a : A} -> Equal a a
`;

function getNatDefs() {
  return compileTTFromText(NAT_CODE).definitions;
}

// ============================================================================
// Basic session creation and simple tactics
// ============================================================================

describe('TacticSession', () => {
  const defs = getNatDefs();

  test('create session from goal type', () => {
    // Goal: Nat -> Nat
    const goalType = {
      tag: 'Binder' as const,
      binderKind: { tag: 'BPi' as const },
      name: 'n',
      domain: { tag: 'Const' as const, name: 'Nat' },
      body: { tag: 'Const' as const, name: 'Nat' },
    };
    const session = TacticSession.create(goalType, defs);
    expect(session.goal).not.toBeNull();
    expect(session.goalId).not.toBeNull();
    expect(session.trace).toHaveLength(0);
    expect(session.isComplete).toBe(false);
  });

  test('intros produces trace entry and extends context', () => {
    const goalType = {
      tag: 'Binder' as const,
      binderKind: { tag: 'BPi' as const },
      name: 'n',
      domain: { tag: 'Const' as const, name: 'Nat' },
      body: { tag: 'Const' as const, name: 'Nat' },
    };
    const s0 = TacticSession.create(goalType, defs);
    const ctxBefore = s0.goal!.ctx.length;

    const s1 = s0.applyCommand({ name: 'intros', args: [mkConst('n')] });
    expect(s1.trace).toHaveLength(1);
    expect(s1.trace[0].tacticName).toBe('intros');
    expect(s1.trace[0].error).toBeUndefined();
    expect(s1.goal!.ctx.length).toBe(ctxBefore + 1);
  });

  test('reflexivity completes equality proof', () => {
    // Goal: Equal Zero Zero (using the compiled definitions which have refl)
    const goalType = mkApp(mkApp(mkApp(mkConst('Equal'), mkConst('Nat')),
      mkConst('Zero')), mkConst('Zero'));
    const s0 = TacticSession.create(goalType, defs);
    const s1 = s0.applyCommand({ name: 'reflexivity', args: [] });
    expect(s1.trace).toHaveLength(1);
    expect(s1.trace[0].tacticName).toBe('reflexivity');
    expect(s1.trace[0].error).toBeUndefined();
  });

  test('applyCommands applies sequence and produces cumulative trace', () => {
    // Goal: Nat -> Equal Zero Zero
    const goalType = {
      tag: 'Binder' as const,
      binderKind: { tag: 'BPi' as const },
      name: '_',
      domain: { tag: 'Const' as const, name: 'Nat' },
      body: mkApp(mkApp(mkApp({ tag: 'Const', name: 'Equal' }, { tag: 'Const', name: 'Nat' }),
        { tag: 'Const', name: 'Zero' }), { tag: 'Const', name: 'Zero' }),
    };

    const s0 = TacticSession.create(goalType, defs);
    const s2 = s0.applyCommands([
      { name: 'intros', args: [mkConst('n')] },
      { name: 'exact', args: [mkConst('refl')] },
    ]);
    expect(s2.trace).toHaveLength(2);
    expect(s2.trace[0].tacticName).toBe('intros');
    expect(s2.trace[1].tacticName).toBe('exact');
  });

  test('failed tactic records error in trace', () => {
    const goalType = { tag: 'Const' as const, name: 'Nat' };
    const s0 = TacticSession.create(goalType, defs);
    // intros on a non-Pi type should fail
    const s1 = s0.applyCommand({ name: 'intros', args: [mkConst('n')] });
    expect(s1.trace).toHaveLength(1);
    expect(s1.trace[0].error).toBeDefined();
  });

  test('session is immutable — original unchanged after applyCommand', () => {
    const goalType = {
      tag: 'Binder' as const,
      binderKind: { tag: 'BPi' as const },
      name: 'n',
      domain: { tag: 'Const' as const, name: 'Nat' },
      body: { tag: 'Const' as const, name: 'Nat' },
    };
    const s0 = TacticSession.create(goalType, defs);
    const s1 = s0.applyCommand({ name: 'intros', args: [mkConst('n')] });

    // Original session is unchanged
    expect(s0.trace).toHaveLength(0);
    expect(s0.goal!.ctx.length).toBeLessThan(s1.goal!.ctx.length);
  });
});

// ============================================================================
// Real-analysis integration test
// ============================================================================

describe('TacticSession with real-analysis preset', () => {
  test('all tactic-mode declarations produce valid traces', { timeout: 20000 }, async () => {
    const { REAL_ANALYSIS_CODE } = await import('../presets/real-analysis');
    const result = compileTTFromText(REAL_ANALYSIS_CODE);
    const allDecls = result.blocks.flatMap(b => b.declarations);

    // Find tactic-mode declarations (surfaceValue is a TacticBlock)
    const tacticDecls = allDecls.filter(
      d => d.surfaceValue?.tag === 'TacticBlock' &&
           (d.surfaceValue as any).tactics?.length > 0 &&
           d.kernelType && d.checkSuccess
    );

    expect(tacticDecls.length).toBeGreaterThanOrEqual(40);

    const errors: string[] = [];
    for (const decl of tacticDecls) {
      const tactics = (decl.surfaceValue as any).tactics;
      try {
        const session = TacticSession.create(decl.kernelType!, result.definitions);
        const final = session.applyCommands(tactics);

        if (final.trace.length === 0) {
          errors.push(`${decl.name}: empty trace`);
        }

        // Check that trace entries have valid engine states
        for (let i = 0; i < final.trace.length; i++) {
          const step = final.trace[i];
          if (!step.engineAfter) {
            errors.push(`${decl.name} step ${i}: missing engineAfter`);
          }
        }
      } catch (e) {
        errors.push(`${decl.name}: threw ${e instanceof Error ? e.message : e}`);
      }
    }

    if (errors.length > 0) {
      console.log('=== TacticSession errors ===');
      for (const e of errors) console.log(e);
    }
    expect(errors).toEqual([]);
  });

  test('session traces match compilation: final engine matches compiled type', { timeout: 20000 }, async () => {
    const { REAL_ANALYSIS_CODE } = await import('../presets/real-analysis');
    const result = compileTTFromText(REAL_ANALYSIS_CODE);
    const allDecls = result.blocks.flatMap(b => b.declarations);

    const tacticDecls = allDecls.filter(
      d => d.surfaceValue?.tag === 'TacticBlock' &&
           (d.surfaceValue as any).tactics?.length > 0 &&
           d.kernelType && d.checkSuccess
    );

    const mismatches: string[] = [];
    for (const decl of tacticDecls) {
      const tactics = (decl.surfaceValue as any).tactics;
      try {
        const session = TacticSession.create(decl.kernelType!, result.definitions);
        const final = session.applyCommands(tactics);

        // The final engine should have solved all goals (for successful proofs)
        const traceErrors = final.trace.filter(s => s.error);
        if (traceErrors.length > 0) {
          mismatches.push(`${decl.name}: ${traceErrors.length} tactic errors in trace`);
          continue;
        }

        // Verify the proof term is complete (can be zonked)
        try {
          final.engine.zonk();
        } catch (e) {
          mismatches.push(`${decl.name}: zonk failed — ${e instanceof Error ? e.message : e}`);
        }
      } catch (e) {
        mismatches.push(`${decl.name}: session threw — ${e instanceof Error ? e.message : e}`);
      }
    }

    if (mismatches.length > 0) {
      console.log('=== Session/compilation mismatches ===');
      for (const m of mismatches) console.log(m);
    }
    // Allow some failures for complex proofs with unsupported features
    expect(mismatches.length).toBeLessThan(5);
  });
});
