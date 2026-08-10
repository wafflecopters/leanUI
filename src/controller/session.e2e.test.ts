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


// The state the seeded limitAdd USED to open at, before the template carried
// the user's whole left case: setup done, both witnesses still packed
// (fProof/gProof in scope). The mid-proof behaviors below are pinned AT this
// point, so they rebuild it from the blank declaration instead of depending on
// how much proof the template happens to ship with.
const MID_PREFIX = `constructor
intro ε epsPos
have h2 : 0 < ε / 2 := divTwoPos ε epsPos
have hF := limF.eps_delta (ε / 2) h2
cases hF with
| mk deltaF fProof =>
  have hG := limG.eps_delta (ε / 2) h2
  cases hG with
  | mk deltaG gProof =>
    sorry`;

const openMidProof = async (): Promise<ProofSession> => {
  const s = open('limitAddFromScratch');
  await s.refreshGoals();
  s.insertTactic(MID_PREFIX);
  await s.refreshGoals();
  await s.refreshGoals(); // second pass lets enrichment settle the case names
  return s;
};

describe('ProofSession against real Lean', () => {
  // The template ships with the proof as built in the editor: everything
  // through the left case of the δ-comparison, with the right case open.
  test(
    'the seeded limitAdd opens at the right case of the comparison, incomplete',
    async () => {
      const s = open('limitAdd');
      await s.refresh();
      const st = s.getState();
      expect(st.status.diagnostics.filter((d) => d.severity === 'error')).toEqual([]);
      // An open sorry means NOT complete. This lied once: the outline walk
      // skipped destructure nodes, so every hole below the first `obtain` was
      // invisible and the proof read "✓ complete" over an unproved case.
      expect(st.status.complete).toBe(false);
      expect(st.status.openGoals).toBe(1);
      // The cursor sits in the right case, with the left case's vocabulary
      // in scope and the comparison hypothesis available.
      expect(st.goal!.targetText).toContain('EpsDeltaWitness');
      const names = s.hypothesesWithTypes().map((h) => h.name);
      expect(names).toEqual(expect.arrayContaining(['deltaF', 'deltaG', 'dfPos', 'fFn', 'dgPos', 'gFn', 'a']));
    },
    10 * MINUTES,
  );

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

  // The move a sum proof needs once it has TWO of something and must produce
  // one: compare them, and each branch knows which is smaller. Nothing in the
  // engine knows about `leTotal`, ordering, or the reals — the lemma is found by
  // its SHAPE (two explicit args of one type, no premises, an inductive result).
  test(
    'at the δ-comparison point, "compare deltaF and deltaG" is offered, and taking it opens both branches',
    async () => {
      const s = await openMidProof();
      await s.refresh();

      // The preset opens mid-proof, with both deltas destructured out.
      const hyps = s.getState().goal!.hypotheses.map((h) => h.name);
      expect(hyps).toEqual(expect.arrayContaining(['deltaF', 'deltaG']));

      const cmp = s.getState().suggestions.find((x) => x.tactic.startsWith('cases leTotal'));
      expect(cmp, `offered: ${s.getState().suggestions.map((x) => x.tactic).join(' | ')}`).toBeDefined();
      // The two most recent values, not `x0`/`L`/`M` sitting there since the
      // statement — and Lean says the split leaves two goals.
      expect(cmp!.tactic).toBe('cases leTotal deltaF deltaG');
      expect(cmp!.subgoals).toBe(2);

      s.applySuggestion(cmp!.id);
      await s.refresh();

      // BOTH branches exist. Opening only the focused one (a `·` bullet in the
      // trial hides the rest) left `right` unproven and the proof broken.
      const split = findByLabel(s.getState().outline, 'cases leTotal deltaF deltaG')!;
      expect(split.children).toHaveLength(2);
      // Named from Lean's own tags, with the dotted prefix stripped:
      // `eps_delta.mk.mk.left` is the goal tag, but `| left =>` is the alternative.
      expect(split.children.map((c) => c.branch)).toEqual(['case left', 'case right']);
      expect(s.proofSource()).toContain('| left a =>');
      expect(s.proofSource()).toContain('| right a =>');

      // And the file Lean gets back is still clean.
      expect(s.getState().status.diagnostics.filter((d) => d.severity === 'error')).toEqual([]);
    },
    10 * MINUTES,
  );

  // The step after the split: `⊢ ℝ` is a BLANK to fill — the δ. Lean's own
  // search is actively unhelpful here (every real type-checks, so `exact?`
  // answered with `f (f (f (f x0))) / f (f (f (f x0)))` and `assumption` grabs
  // an arbitrary hypothesis), so the editor offers the choices instead.
  test(
    'a value goal offers the values — including the rmin that makes the proof work',
    async () => {
      const s = await openMidProof();
      await s.refresh();

      const ctor = s.getState().suggestions.find((x) => x.tactic === 'constructor')!;
      expect(ctor).toBeDefined();
      s.applySuggestion(ctor.id);
      await s.refresh();

      // The witness goal comes FIRST (it's what the sibling depends on) and is
      // marked as a value to choose, not a claim to prove.
      const st = s.getState();
      expect(st.goal!.targetText).toBe('\u211d');
      expect(s.leanGoalMap.get(st.cursor.nodeId)?.isValueType).toBe(true);

      const tactics = st.suggestions.map((x) => x.tactic);
      // Built, not merely listed: `rmin deltaF deltaG` is no hypothesis.
      expect(tactics).toContain('exact rmin deltaF deltaG');
      // In scope order, and the recent pair — not the reals from the statement.
      expect(tactics).toContain('exact deltaF');
      expect(tactics).toContain('exact deltaG');
      // The noise is gone: nothing that "succeeds" by choosing for you.
      expect(tactics).not.toContain('omega');
      expect(tactics).not.toContain('trivial');
      expect(tactics).not.toContain('assumption');
      expect(tactics.some((t) => /f \(f \(f/.test(t))).toBe(false);

      // Taking it substitutes the witness into the sibling goal, cleanly.
      const pick = st.suggestions.find((x) => x.tactic === 'exact rmin deltaF deltaG')!;
      s.applySuggestion(pick.id);
      await s.refresh();
      expect(s.getState().goal!.targetText).toBe(
        'EpsDeltaWitness (fun x => f x + g x) x0 (L + M) \u03b5 (rmin deltaF deltaG)',
      );
      expect(s.getState().status.diagnostics.filter((d) => d.severity === 'error')).toEqual([]);
    },
    10 * MINUTES,
  );

  // REGRESSION: `cases` on a ONE-constructor structure left its fields as
  // inaccessible `fst✝`/`snd✝` and the header reading "Case (case)" — nothing
  // to name, nothing to refer to. The case had no source range of its own (a
  // lone case prints as a plain continuation, not a `·` bullet), so the
  // enrichment that names cases never saw a goal for it.
  test(
    'destructuring a one-constructor structure binds accessible, nameable fields',
    async () => {
      const s = await openMidProof();
      await s.refresh();
      s.insertTactic('cases fProof');
      await s.refresh();
      // Enrichment rewrote the tree; Lean reports on the NAMED form next pass.
      await s.refresh();

      // Bound by name in the source, so the proof can refer to them.
      expect(s.proofSource()).toContain('cases fProof with');
      expect(s.proofSource()).toContain('| mk fst snd =>');

      const names = s.getState().goal!.hypotheses.map((h) => h.name);
      expect(names).toContain('fst');
      expect(names).toContain('snd');
      expect(names.some((n) => n.includes('\u271d'))).toBe(false); // no daggers

      expect(s.getState().status.diagnostics.filter((d) => d.severity === 'error')).toEqual([]);
    },
    10 * MINUTES,
  );

  // The user's question was "even with the pill gone, how do I build this
  // MYSELF?" — and the answer was: you can't. `cases` had no manual form at
  // all, and `Induction` took an identifier, so a split on a TERM like
  // `leTotal a b` ("either deltaF ≤ deltaG or the other way round") was
  // reachable only if a suggestion happened to offer it.
  test(
    'a case split on a lemma application can be typed by hand, and opens both branches',
    async () => {
      const s = await openMidProof();
      await s.refresh();

      const ran = s.runTactic('cases', 'leTotal deltaF deltaG');
      expect(ran.ok).toBe(true);
      await s.refresh();

      // TWO branches, because `Either` has two constructors — not the two
      // Nat-shaped cases the editor used to print for every split, and not the
      // single branch a count of "1" would have left (which Lean would then
      // reject for unsolved goals).
      expect(s.proofSource()).toContain('cases leTotal deltaF deltaG');
      await s.refresh(); // enrichment names the branches from Lean's tags
      const src = s.proofSource();
      // The preset's `Either` — its constructors are `left`/`right`, and the
      // names come from Lean rather than from anything spelled out here.
      expect(src).toContain('| left');
      expect(src).toContain('| right');
      expect(s.getState().status.diagnostics.filter((d) => d.severity === 'error')).toEqual([]);
    },
    10 * MINUTES,
  );

  // Destructuring used to insert an UNNAMED branch and wait a round-trip for
  // Lean to name it — so the row read "Case (case)" with pieces the proof could
  // not refer to until something else triggered a refresh. `obtain` names them
  // as the step is made.
  test(
    'destructuring names the pieces immediately, with no branch and no indent',
    async () => {
      const s = await openMidProof();
      await s.refresh();
      s.selectHypothesis('fProof');
      await s.refresh();

      const act = s.getState().actions.find((a) => a.id.endsWith('cases:fProof'))!;
      expect(act).toBeDefined();
      // An `obtain`, because Lean reported the shape — not the branch form.
      expect(act.detail?.tactic).toMatch(/^obtain \u27e8/);

      s.dispatch({ id: act.id });
      await s.refresh(); // ONE round-trip, not two

      expect(s.proofSource()).toContain('obtain \u27e8fst, snd\u27e9 := fProof');
      const names = s.getState().goal!.hypotheses.map((h) => h.name);
      expect(names).toContain('fst');
      expect(names).toContain('snd');
      // Accessible immediately: no inaccessible daggers waiting to be renamed.
      expect(names.some((n) => n.includes('\u271d'))).toBe(false);
      // And they carry their TYPES — the context panel lists them, and the
      // prose can show one on hover. Several tree walkers had a `default`
      // branch rather than an exhaustive switch, so they silently skipped the
      // new node and everything below it lost its goal info.
      const hyps = s.getState().goal!.hypotheses;
      expect(hyps.find((h) => h.name === 'fst')?.text).toBe('0 < deltaF');
      expect(hyps.find((h) => h.name === 'snd')?.text).toContain('|f x - L| < ε / 2');
      expect(s.getState().status.diagnostics.filter((d) => d.severity === 'error')).toEqual([]);
    },
    10 * MINUTES,
  );

  // `⟨a, b, c⟩` is Lean's anonymous constructor and associates to the RIGHT, so
  // a flat name list can only describe the right spine. Flattening an earlier
  // field describes a left-nested shape and Lean rejects the pattern.
  test(
    'the reported shape nests only where the pattern can',
    async () => {
      const s = await openMidProof();
      await s.refresh();
      const hyps = s.hypothesesWithTypes();
      // `fProof : EpsDeltaWitness …` is a pair whose FIRST field is itself a
      // pair. Flattening it would need ⟨⟨a,b⟩,c⟩, which ⟨a,b,c⟩ does not mean.
      expect(hyps.find((h) => h.name === 'fProof')?.flatFields).toEqual(['fst', 'snd']);
      // A real, not a structure: nothing to take apart.
      expect(hyps.find((h) => h.name === 'deltaF')?.flatFields ?? []).toEqual([]);
    },
    10 * MINUTES,
  );

  // Branch counts come from the extractor, not from a guess: a hypothesis
  // carries its type's constructor count and a lemma carries its conclusion's.
  test(
    'Lean reports how many branches a split opens',
    async () => {
      const s = await openMidProof();
      await s.refresh();

      // `hF : ∃δ …` is a one-constructor structure.
      const hyps = s.hypothesesWithTypes();
      expect(hyps.find((h) => h.name === 'fProof')?.ctors).toBe(1);
      // `ε : ℝ` is not an inductive at all — splitting it is not a 2-way split.
      expect(hyps.find((h) => h.name === 'ε')?.ctors ?? 0).toBe(0);
      // `leTotal a b` concludes an `Either`.
      expect(declarations.find((d) => d.name === 'leTotal')?.conclCtors).toBe(2);
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
