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
    const goalType = mkApp(mkApp(mkApp(mkConst('Equal'), mkConst('Nat')),
      mkConst('Zero')), mkConst('Zero'));
    const s0 = TacticSession.create(goalType, defs);
    const s1 = s0.applyCommand({ name: 'reflexivity', args: [] });
    expect(s1.trace).toHaveLength(1);
    expect(s1.trace[0].tacticName).toBe('reflexivity');
    expect(s1.trace[0].error).toBeUndefined();
  });

  test('applyCommands applies sequence and produces cumulative trace', () => {
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
      { name: 'reflexivity', args: [] },
    ]);
    expect(s2.trace).toHaveLength(2);
    expect(s2.trace[0].tacticName).toBe('intros');
    expect(s2.trace[1].tacticName).toBe('reflexivity');
  });

  test('failed tactic records error in trace', () => {
    const goalType = { tag: 'Const' as const, name: 'Nat' };
    const s0 = TacticSession.create(goalType, defs);
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
    expect(s0.trace).toHaveLength(0);
    expect(s0.goal!.ctx.length).toBeLessThan(s1.goal!.ctx.length);
  });
});

// ============================================================================
// Real-analysis integration tests
// ============================================================================

describe('TacticSession with real-analysis preset', () => {
  test('all tactic-mode declarations produce valid traces', { timeout: 30000 }, async () => {
    const { REAL_ANALYSIS_CODE } = await import('../presets/real-analysis');
    const result = compileTTFromText(REAL_ANALYSIS_CODE);
    const allDecls = result.blocks.flatMap(b => b.declarations);

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

  test('session traces match compilation: final engine zonks', { timeout: 30000 }, async () => {
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

        const traceErrors = final.trace.filter(s => s.error);
        if (traceErrors.length > 0) {
          mismatches.push(`${decl.name}: ${traceErrors.length} tactic errors in trace`);
          continue;
        }

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
    expect(mismatches.length).toBeLessThan(5);
  });

  test('traces are stored on compiled declarations', { timeout: 30000 }, async () => {
    const { REAL_ANALYSIS_CODE } = await import('../presets/real-analysis');
    const result = compileTTFromText(REAL_ANALYSIS_CODE);
    const allDecls = result.blocks.flatMap(b => b.declarations);

    const tacticDecls = allDecls.filter(
      d => d.surfaceValue?.tag === 'TacticBlock' && d.checkSuccess
    );
    const withTrace = tacticDecls.filter(d => d.tacticTrace && d.tacticTrace.length > 0);

    expect(tacticDecls.length).toBeGreaterThanOrEqual(40);
    expect(withTrace.length).toBe(tacticDecls.length);

    // Verify trace structure
    for (const decl of withTrace) {
      for (const step of decl.tacticTrace!) {
        expect(step.tacticName).toBeTruthy();
        expect(step.engineAfter).toBeTruthy();
        expect(step.goalId).toBeTruthy();
        expect(Array.isArray(step.branchPath)).toBe(true);
      }
    }
  });

  test('nested case patterns compile successfully', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

add : Nat -> Nat -> Nat
add Zero m = m
add (Succ n) m = Succ (add n m)

record DPair {u v : ULevel} (A : Type u) (B : A -> Type v) : Type (UMax u v) where
  constructor MkDPair
  fst : A
  snd : B fst

record Pair (A B : Type) where
  constructor MkPair
  fst : A
  snd : B

test : DPair Nat (\\n => Pair Nat Nat) -> Nat := by
  intro p
  cases p with
  | MkDPair n (MkPair a b) =>
    exact (add n (add a b))
`;
    const result = compileTTFromText(source);
    const decl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'test');
    const errMsgs = (decl?.checkErrors ?? []).map(e => e.message).join(' | ');
    expect(decl?.checkSuccess, `errors: ${errMsgs}`).toBe(true);
  });

  test('nested case patterns compile successfully (flat Pair in Pair)', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

add : Nat -> Nat -> Nat
add Zero m = m
add (Succ n) m = Succ (add n m)

record Pair (A B : Type) where
  constructor MkPair
  fst : A
  snd : B

test : Pair Nat (Pair Nat Nat) -> Nat := by
  intro p
  cases p with
  | MkPair n (MkPair a b) =>
    exact (add n (add a b))
`;
    const result = compileTTFromText(source);
    const decl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'test');
    const errMsgs = (decl?.checkErrors ?? []).map(e => e.message).join(' | ');
    expect(decl?.checkSuccess, `errors: ${errMsgs}`).toBe(true);
  });
});

// ============================================================================
// Context renaming — user's pattern names flow into the hypothesis panel
// ============================================================================

const PAIR_CODE = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

record Pair (A B : Type) where
  constructor MkPair
  fst : A
  snd : B

record DPair {u v : ULevel} (A : Type u) (B : A -> Type v) : Type (UMax u v) where
  constructor MkDPair
  fst : A
  snd : B fst

inductive Either (A B : Type) : Type where
  Left : A -> Either A B
  Right : B -> Either A B
`;

describe('TacticSession ctx entry renaming', () => {
  const defs = compileTTFromText(PAIR_CODE).definitions;

  /** Build a session with an intro'd `p : Pair Nat Nat` hypothesis. */
  function pairSession() {
    const goalType = {
      tag: 'Binder' as const,
      binderKind: { tag: 'BPi' as const },
      name: 'p',
      domain: mkApp(mkApp(mkConst('Pair'), mkConst('Nat')), mkConst('Nat')),
      body: mkConst('Nat'),
    };
    return TacticSession
      .create(goalType, defs)
      .applyCommand({ name: 'intros', args: [mkConst('p')] });
  }

  test('flat cases pattern names appear in the ctx (not fst/snd)', () => {
    const s = pairSession().applyCommand({
      name: 'cases',
      args: [mkConst('p')],
      caseBranches: [
        {
          constructor: 'MkPair',
          params: [
            { tag: 'var', name: 'myFst' },
            { tag: 'var', name: 'mySnd' },
          ],
          tactics: [{ name: 'exact', args: [mkConst('myFst')] }],
        },
      ],
    });

    // Find the trace step from INSIDE the MkPair branch — it has the renamed ctx.
    const insideBranch = s.trace.find(
      step => step.branchPath.length > 0 && step.branchPath[step.branchPath.length - 1] === 'MkPair',
    );
    expect(insideBranch).toBeDefined();
    const ctx = insideBranch!.engineAfter.metaVars.get(insideBranch!.goalId)?.ctx
      ?? s.engine.metaVars.get(insideBranch!.goalId)?.ctx;
    expect(ctx).toBeDefined();
    const names = ctx!.map(b => b.name);

    // The last two entries should be the user's pattern names, NOT the
    // default field names fst/snd.
    expect(names.slice(-2)).toEqual(['myFst', 'mySnd']);
  });

  test('induction branches each get their own pattern names', () => {
    // Use Nat (Zero/Succ) which is known to compile. cases on Nat
    // gives two branches, each with their own pattern names.
    const goalType = {
      tag: 'Binder' as const,
      binderKind: { tag: 'BPi' as const },
      name: 'n',
      domain: mkConst('Nat'),
      body: mkConst('Nat'),
    };
    const s0 = TacticSession
      .create(goalType, defs)
      .applyCommand({ name: 'intros', args: [mkConst('n')] });

    const s = s0.applyCommand({
      name: 'cases',
      args: [mkConst('n')],
      caseBranches: [
        {
          constructor: 'Zero',
          params: [],
          tactics: [{ name: 'exact', args: [mkConst('Zero')] }],
        },
        {
          constructor: 'Succ',
          params: [{ tag: 'var', name: 'pred' }],
          tactics: [{ name: 'exact', args: [mkConst('pred')] }],
        },
      ],
    });

    // The Succ branch should have a renamed param `pred` (not `_arg0` or `n0`).
    const succStep = s.trace.find(
      step => step.branchPath[step.branchPath.length - 1] === 'Succ',
    );
    expect(succStep).toBeDefined();
    const eng = succStep!.engineAfter;
    const hasName = (name: string) => {
      for (const [, meta] of eng.metaVars) {
        if (meta.ctx.some(b => b.name === name)) return true;
      }
      return false;
    };
    expect(hasName('pred')).toBe(true);
  });

  test('nested destructuring flattens user names into the ctx', () => {
    // Compile a full source that exercises nested case patterns.
    // After `| MkDPair myA (MkPair myB myC) => exact (add myA myB)`,
    // the trace should contain ctx entries named myA, myB, myC.
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

add : Nat -> Nat -> Nat
add Zero m = m
add (Succ n) m = Succ (add n m)

record DPair {u v : ULevel} (A : Type u) (B : A -> Type v) : Type (UMax u v) where
  constructor MkDPair
  fst : A
  snd : B fst

record Pair (A B : Type) where
  constructor MkPair
  fst : A
  snd : B

test : DPair Nat (\\n => Pair Nat Nat) -> Nat := by
  intro p
  cases p with
  | MkDPair myA (MkPair myB myC) =>
    exact (add myA (add myB myC))
`;
    const result = compileTTFromText(source);
    const testDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'test') as any;
    expect(testDecl?.checkSuccess).toBe(true);
    expect(testDecl?.tacticTrace?.length).toBeGreaterThan(0);

    // Check the deepest trace step's ctx for user-provided names.
    const trace = testDecl.tacticTrace!;
    const deepest = trace[trace.length - 1];
    const eng = deepest.engineAfter;
    // Find a ctx in the engine that has all three user names.
    let foundAll = false;
    for (const [, meta] of eng.metaVars) {
      const names = new Set(meta.ctx.map((b: any) => b.name));
      if (names.has('myA') && names.has('myB') && names.has('myC')) {
        foundAll = true;
        // Confirm fst/snd are NOT present (replaced by user names).
        expect(names.has('fst')).toBe(false);
        expect(names.has('snd')).toBe(false);
        break;
      }
    }
    expect(foundAll).toBe(true);
  });

  test('pattern name collision with outer ctx is deconflicted with numeric suffix', () => {
    // Outer ctx has `x : Pair Nat Nat` (from intros). User writes
    // `| MkPair x y =>` — the new `x` collides with the outer `x`.
    // Expected: the new entry is renamed to `x1` to avoid shadowing at
    // the display level.
    const goalType = {
      tag: 'Binder' as const,
      binderKind: { tag: 'BPi' as const },
      name: 'x',
      domain: mkApp(mkApp(mkConst('Pair'), mkConst('Nat')), mkConst('Nat')),
      body: mkConst('Nat'),
    };
    const s = TacticSession
      .create(goalType, defs)
      .applyCommand({ name: 'intros', args: [mkConst('x')] })
      .applyCommand({
        name: 'cases',
        args: [mkConst('x')],
        caseBranches: [
          {
            constructor: 'MkPair',
            params: [
              { tag: 'var', name: 'x' },
              { tag: 'var', name: 'y' },
            ],
            tactics: [{ name: 'exact', args: [mkConst('y')] }],
          },
        ],
      });

    const branchStep = s.trace.find(
      step => step.branchPath[step.branchPath.length - 1] === 'MkPair',
    );
    expect(branchStep).toBeDefined();

    // Find a ctx with the deconflicted name.
    const eng = branchStep!.engineAfter;
    let foundX1 = false;
    for (const [, meta] of eng.metaVars) {
      const names = meta.ctx.map(b => b.name);
      if (names.includes('x1') && names.includes('y')) {
        // Also confirm the original `x` is still in the ctx somewhere.
        // (There should be exactly one `x` — the outer one.)
        expect(names.filter(n => n === 'x').length).toBe(1);
        foundX1 = true;
        break;
      }
    }
    expect(foundX1).toBe(true);
  });

  test('implicit-arg metas are resolved for correct hypothesis types', { timeout: 30000 }, async () => {
    // When `cases Limit.eps_delta limG …` destructures, the hypothesis
    // types should reference `g` and `M` (from limG), NOT `f` and `L`
    // (from the generic parameter name in Limit.eps_delta's type signature).
    // This verifies that the cases tactic resolves implicit-arg metas
    // from inferType's constraints before building the branch context.
    const { REAL_ANALYSIS_CODE } = await import('../presets/real-analysis');
    const result = compileTTFromText(REAL_ANALYSIS_CODE);
    const allDecls = result.blocks.flatMap(b => b.declarations);
    const limitAdd = allDecls.find(d => d.name === 'limitAdd') as any;
    expect(limitAdd?.checkSuccess).toBe(true);

    const session = TacticSession.create(limitAdd.kernelType, result.definitions);
    const final = session.applyCommands(limitAdd.surfaceValue.tactics);

    // Find the trace step inside the second MkDPair branch (for limG).
    // Its context should have `boundG` whose type references `g` (not `f`).
    const step = final.trace.find(
      s => s.branchPath.join('/').includes('MkDPair/MkPair/MkDPair/MkPair'),
    );
    expect(step).toBeDefined();
    const eng = step!.engineAfter;
    const goal = eng.metaVars.get(step!.goalId);
    expect(goal).toBeDefined();

    // Check that boundG's type does NOT contain any unsolved _implicit_ metas
    // (which would render as □ or map to the wrong outer var).
    const boundG = goal!.ctx.find((b: any) => b.name === 'boundG');
    expect(boundG).toBeDefined();

    function hasUnsolvedImplicitMeta(t: any): boolean {
      if (!t || typeof t !== 'object') return false;
      if (t.tag === 'Meta' && t.id?.startsWith('_implicit_')) return true;
      return Object.values(t).some(v => typeof v === 'object' && v !== null && hasUnsolvedImplicitMeta(v));
    }
    expect(hasUnsolvedImplicitMeta(boundG!.type)).toBe(false);
  });
});
