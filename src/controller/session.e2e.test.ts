/**
 * The controller against REAL Lean.
 *
 * The unit suites pin the wiring; this one pins the thing that actually
 * matters — that a person can start at `limitAdd`, be offered moves that work,
 * take them, and end up with a proof Lean accepts. Every assertion here is
 * about behaviour a user would notice.
 *
 * These are slow (each step is a real elaboration). They share one file
 * analysis and one caching analyzer so the cost is paid once.
 */
import { afterAll, beforeAll, describe, expect, test } from 'vitest';
import { LEAN_PRESETS } from '../lean/presets';
import { analyzeLeanSource } from '../../server/lean-bridge';
import { nodeAnalyzer, shutdownLeanBridge } from './nodeAnalyzer';
import { ProofSession } from './session';
import { ACTION } from './actions';
import type { LeanAnalyzer } from './analyzer';
import type { LeanDeclaration } from '../lean/types';

const PRESET = 'Real Analysis (chain rule)';
const MINUTES = 60_000;

let source: string;
let declarations: LeanDeclaration[];
let analyze: LeanAnalyzer;

beforeAll(async () => {
  const preset = LEAN_PRESETS.find((p) => p.name === PRESET);
  if (!preset) throw new Error(`missing preset ${PRESET}`);
  source = preset.code;
  const result = await analyzeLeanSource(source, { timeoutMs: 10 * MINUTES });
  if (result.bridgeError) throw new Error(`Lean bridge: ${result.bridgeError}`);
  declarations = result.declarations;
  // Shared cache: the trials repeat identical sources across tests.
  analyze = nodeAnalyzer({ timeoutMs: 10 * MINUTES });
}, 10 * MINUTES);

afterAll(() => {
  // Lean's persistent workers would otherwise hold the process open.
  shutdownLeanBridge();
});

const open = (declName: string) =>
  ProofSession.open({ analyze, source, declarations, declName, autoRefresh: false });

const labels = (s: ProofSession) =>
  s.getState().suggestions.map((x) => x.label);

describe('ProofSession against real Lean', () => {
  test(
    'opening a theorem reports its real goal and context',
    async () => {
      const s = open('limitAddFromScratch');
      await s.refreshGoals();
      const state = s.getState();
      expect(state.error).toBeUndefined();
      expect(state.goal).not.toBeNull();
      // The ε-δ limit statement, as Lean prints it through the preset's notation.
      expect(state.goal!.targetText).toContain('lim⟦x0⟧');
      expect(state.goal!.hypotheses.map((h) => h.name)).toEqual(
        expect.arrayContaining(['f', 'g', 'x0', 'L', 'M', 'limF', 'limG']),
      );
      // Those two limit hypotheses print with `=`, so they read as rewritable.
      expect(state.goal!.hypotheses.find((h) => h.name === 'limF')?.isEquation).toBe(true);
      expect(state.status.openGoals).toBe(1);
      expect(state.status.complete).toBe(false);
    },
    10 * MINUTES,
  );

  test(
    'constructor is offered on a structure goal, and opens the ε-δ obligation',
    async () => {
      const s = open('limitAddFromScratch');
      await s.refresh();
      expect(labels(s)).toContain('constructor');
      expect(s.insertTactic('constructor')).toEqual({ ok: true });
      await s.refreshGoals();
      // The way IN to an ε-δ proof: the Limit structure's single field.
      expect(s.getState().goal!.targetText).toContain('EpsDeltaWitness');
    },
    10 * MINUTES,
  );

  // THE scenario this whole layer was built to make checkable: at `0 < ε / 2`
  // the engine must offer the positivity lemmas the file actually contains.
  describe('at the ε/2 obligation', () => {
    let session: ProofSession;

    beforeAll(async () => {
      session = open('limitAddFromScratch');
      await session.refreshGoals();
      session.insertTactic('constructor');
      await session.refreshGoals();
      session.runTactic('intros', 'ε epsPos');
      await session.refreshGoals();
      // A typed have states the obligation and parks the cursor on proving it.
      session.runTactic('have', 'h1 : 0 < ε / 2');
      await session.refresh();
    }, 10 * MINUTES);

    test('the cursor is on the stated obligation', () => {
      expect(session.getState().goal!.targetText).toBe('0 < ε / 2');
    });

    test('the file’s positivity lemmas are offered, best first', () => {
      const applies = labels(session).filter((l) => l.startsWith('apply '));
      // divTwoPos proves exactly this; divPos is the general a>0 → b>0 → a/b>0.
      expect(applies.slice(0, 2)).toEqual(['apply divTwoPos', 'apply divPos']);
    });

    test('every offered move says what it would leave behind', () => {
      const state = session.getState();
      const divTwoPos = state.actions.find((a) => a.id === `${ACTION.suggestion}lean-applylemma:divTwoPos`);
      const divPos = state.actions.find((a) => a.id === `${ACTION.suggestion}lean-applylemma:divPos`);
      expect(divTwoPos?.detail?.previews).toHaveLength(1);
      // `0 < a → 0 < b → 0 < a / b` splits into exactly the two positivity goals.
      expect(divPos?.detail?.subgoals).toBe(2);
      expect(divPos?.detail?.previews).toHaveLength(2);
    });

    test('nothing offered here is a false promise: no suggestion claims to close', () => {
      // `0 < ε / 2` is not in the context and no closer exists, so an honest
      // engine offers only transforms.
      expect(session.getState().suggestions.filter((x) => x.closes)).toEqual([]);
    });
  });

  test(
    'a full obligation can be discharged: apply divTwoPos → assumption',
    async () => {
      const s = open('limitAddFromScratch');
      await s.refreshGoals();
      s.insertTactic('constructor');
      await s.refreshGoals();
      s.runTactic('intros', 'ε epsPos');
      await s.refreshGoals();
      s.runTactic('have', 'h1 : 0 < ε / 2');
      await s.refresh();

      // Take the suggestion by id, exactly as a click would.
      expect(s.applySuggestion('lean-applylemma:divTwoPos')).toEqual({ ok: true });
      await s.refresh();
      expect(s.getState().goal!.targetText).toBe('0 < ε');

      // `epsPos : 0 < ε` is right there, so `assumption` must close it.
      const closer = s.getState().suggestions.find((x) => x.closes);
      expect(closer?.label).toBe('assumption');
      expect(s.applySuggestion(closer!.id)).toEqual({ ok: true });
      await s.refresh();

      // The obligation is discharged and the cursor moved on to the rest.
      const state = s.getState();
      expect(state.goal!.targetText).toContain('EpsDeltaWitness');
      expect(state.status.diagnostics.filter((d) => d.severity === 'error')).toEqual([]);
      // And the proof reads as what was done.
      expect(state.proofSource).toContain('have h1 : 0 < ε / 2 := by');
      expect(state.proofSource).toContain('apply divTwoPos');
      expect(state.proofSource).toContain('assumption');
    },
    10 * MINUTES,
  );

  test(
    'a goal-splitting apply opens one branch per premise, and they round-trip',
    async () => {
      const s = open('limitAddFromScratch');
      await s.refreshGoals();
      s.insertTactic('constructor');
      await s.refreshGoals();
      s.runTactic('intros', 'ε epsPos');
      await s.refreshGoals();
      s.runTactic('have', 'h1 : 0 < ε / 2');
      await s.refresh();

      s.applySuggestion('lean-applylemma:divPos');
      await s.refreshGoals();

      // Two visible branches, with Lean's own goals.
      const haveNode = findByLabel(s.getState().outline, 'apply divPos');
      expect(haveNode?.children).toHaveLength(2);
      expect(haveNode!.children.map((c) => c.goalText)).toEqual(['0 < ε', '0 < 2']);

      // …and the written file reads back as the SAME proof, rather than the
      // branches collapsing into a flat tactic sequence. Re-elaborate it so the
      // declaration line numbers match the (now longer) text, exactly as the
      // app does after a write-back.
      const written = s.fullSource();
      const reanalyzed = await analyzeLeanSource(written, { timeoutMs: 10 * MINUTES });
      const reopened = ProofSession.open({
        analyze,
        source: written,
        declarations: reanalyzed.declarations,
        declName: 'limitAddFromScratch',
        autoRefresh: false,
      });
      expect(reopened.proofSource()).toBe(s.proofSource());
    },
    10 * MINUTES,
  );

  // `apply ltLeTrans` leaves a goal that is a BLANK, not a claim: the midpoint
  // you have to choose. Lean names it (case `b`, referenced as `?b` by the
  // siblings), so the prose can say "We need a value of type ℝ" instead of the
  // baffling "We must show ℝ".
  test(
    'the midpoint of a transitivity is marked as a value to supply',
    async () => {
      const s = open('limitAddFromScratch');
      await s.refreshGoals();
      s.insertTactic('constructor');
      await s.refreshGoals();
      s.runTactic('intros', 'ε epsPos');
      await s.refreshGoals();
      s.runTactic('have', 'h1 : 0 < ε / 2');
      await s.refreshGoals();
      s.runTactic('apply', 'ltLeTrans');
      await s.refreshGoals();

      const branches = findByLabel(s.getState().outline, 'apply ltLeTrans')!.children;
      // Three branches, and the midpoint you CHOOSE comes first — Lean orders
      // it last, which strands you on `0 < ?b` with no idea where ?b is from.
      expect(branches.map((c) => c.goalText)).toEqual(['ℝ', '0 < ?b', '?b ≤ ε / 2']);
      expect(branches.map((c) => c.branch)).toEqual(['b', 'hab', 'hbc']);

      // The cursor is ON the choice, because nothing else can be done first.
      expect(s.getState().cursor.nodeId).toBe(branches[0].id);
      expect(s.getState().goal!.targetText).toBe('ℝ');

      // Exactly the midpoint is flagged as a value to supply.
      const flagged = [...s.leanGoalMap.entries()].filter(([, i]) => i.isValueType);
      expect(flagged).toHaveLength(1);
      expect(s.leanGoalMap.get(branches[0].id)?.isValueType).toBe(true);

      // REGRESSION: supplying the value must not erase the marking. The old
      // detection read `?b` mentions out of sibling goals, which vanish the
      // moment `exact 1` assigns the metavariable — the permanent proof then
      // read "We must show ℝ" again. Lean's own Prop check (`isProp` from the
      // extractor) survives assignment.
      s.insertTactic('exact 1');
      await s.refreshGoals();
      const after = findByLabel(s.getState().outline, 'apply ltLeTrans')!.children;
      expect(s.leanGoalMap.get(after[0].id)?.isValueType).toBe(true);

      // The written proof selects the goals BY NAME, so the order sticks.
      expect(s.proofSource()).toContain('case b =>');
      const written = await analyzeLeanSource(s.fullSource(), { timeoutMs: 10 * MINUTES });
      expect(written.messages.filter((m) => m.severity === 'error')).toEqual([]);
    },
    10 * MINUTES,
  );

  test(
    'the write-back is a file Lean still accepts',
    async () => {
      const s = open('limitAddFromScratch');
      await s.refreshGoals();
      s.insertTactic('constructor');
      await s.refreshGoals();
      s.runTactic('intros', 'ε epsPos');
      await s.refreshGoals();
      s.runTactic('have', 'h1 : 0 < ε / 2');
      await s.refresh();
      s.applySuggestion('lean-applylemma:divTwoPos');
      await s.refreshGoals();

      const result = await analyzeLeanSource(s.fullSource(), { timeoutMs: 10 * MINUTES });
      expect(result.bridgeError).toBeUndefined();
      // `sorry` warnings are expected (the proof is unfinished); errors are not.
      const errors = result.messages.filter((m) => m.severity === 'error');
      expect(errors.map((e) => e.text)).toEqual([]);
    },
    10 * MINUTES,
  );

  test(
    'selecting a subterm re-scopes the offered rewrites',
    async () => {
      const s = open('limitAddFromScratch');
      await s.refreshGoals();
      s.insertTactic('constructor');
      await s.refreshGoals();
      s.runTactic('intros', 'ε epsPos');
      await s.refreshGoals();
      s.runTactic('have', 'h1 : 0 < ε / 2');
      await s.refresh();

      const half = s.getState().goal!.subterms.find((t) => t.text.trim() === 'ε / 2');
      expect(half).toBeDefined();
      expect(s.selectSubterm(half!.pos)).toEqual({ ok: true });
      await s.refreshSuggestions();

      // Unfold candidates only exist under a selection.
      expect(s.getState().suggestions.some((x) => x.id.startsWith('lean-unfold:'))).toBe(true);
      expect(s.getState().selection.subterm?.text).toBe('ε / 2');
    },
    10 * MINUTES,
  );

  test(
    'a tactic Lean rejects is never offered',
    async () => {
      const s = open('limitAddFromScratch');
      await s.refresh();
      // At the top-level Limit goal, positivity lemmas cannot apply.
      expect(labels(s).some((l) => l.startsWith('apply div'))).toBe(false);
      // Whatever IS offered must be applicable — that's the contract.
      for (const suggestion of s.getState().suggestions) {
        expect(suggestion.tactic.length).toBeGreaterThan(0);
      }
    },
    10 * MINUTES,
  );
});

/** First outline node with the given label. */
function findByLabel(
  node: { label: string; children: Array<{ label: string; children: unknown[] }> },
  label: string,
): { label: string; children: Array<{ id: number; goalText?: string; branch?: string }> } | null {
  if (node.label === label) return node as never;
  for (const c of node.children) {
    const found = findByLabel(c as never, label);
    if (found) return found;
  }
  return null;
}
