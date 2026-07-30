/**
 * One editor, two audiences — proved against real Lean.
 *
 * The suggestion engine was built and tuned entirely against a from-scratch
 * axiomatisation of ℝ, where `exact?` finds nothing and `rw?` doesn't exist. The
 * risk in that is invisible until you try the other kind of user: an engine that
 * has quietly grown to assume "no library" serves the Mathlib user badly, and an
 * engine that assumes Mathlib abandons the person building their own theory.
 *
 * The design answer is that NOTHING asks which one it has. `SOLVER_TACTICS`
 * proposes core Lean and Mathlib tactics side by side on every goal, and
 * validation — a real trial, at the real cursor — decides what survives. These
 * tests pin both halves of that, on the same code path:
 *
 *   - on the from-scratch preset, the Mathlib tactics must NOT appear;
 *   - on the Mathlib preset, they must appear AND close the goal.
 *
 * Skipped (not failed) when Mathlib isn't fetched/built, since core mode is a
 * supported configuration in its own right — that's the whole point.
 *
 * Real Lean; run with `npm run test:e2e`.
 */
import { afterAll, beforeAll, describe, expect, test } from 'vitest';
import { LEAN_PRESETS } from '../lean/presets';
import { analyzeLeanSource } from '../../server/lean-bridge';
import { nodeAnalyzer, shutdownLeanBridge } from './nodeAnalyzer';
import { ProofSession } from './session';
import { SOLVER_TACTICS } from './candidates';
import type { LeanAnalyzer } from './analyzer';
import type { LeanDeclaration } from '../lean/types';

const MINUTES = 60_000;
/** Mathlib's first import is tens of seconds even warm, and the very first
 *  prefix compile is minutes. */
const SLOW = 20 * MINUTES;

/** Tactics that exist only with Mathlib — the half that must vanish on core. */
const MATHLIB_ONLY = ['positivity', 'linarith', 'norm_num', 'ring', 'nlinarith'];

let mathlibReady = false;
let source: string;
let declarations: LeanDeclaration[];
let analyze: LeanAnalyzer;

beforeAll(async () => {
  const preset = LEAN_PRESETS.find((p) => p.mathlib);
  if (!preset) throw new Error('missing Mathlib preset');
  source = preset.code;
  const result = await analyzeLeanSource(source, { mathlib: true, timeoutMs: SLOW });
  // Not built → every import fails. Report it once, clearly, and skip.
  if (result.bridgeError || result.messages.some((m) => m.severity === 'error')) {
    const why = result.bridgeError ?? result.messages.find((m) => m.severity === 'error')?.text ?? '?';
    console.warn(`[mathlib parity] skipped — Mathlib preset does not compile: ${why.split('\n')[0]}`);
    return;
  }
  declarations = result.declarations;
  analyze = nodeAnalyzer({ timeoutMs: SLOW });
  mathlibReady = true;
}, SLOW);

afterAll(() => {
  shutdownLeanBridge();
});

const openMathlib = (declName: string) =>
  ProofSession.open({ analyze, source, declarations, declName, mathlib: true, autoRefresh: false });

describe('the same suggestion engine on both kinds of file', () => {
  test(
    'on a from-scratch axiomatisation, the Mathlib tactics are never offered',
    async () => {
      // No skip: this half is exactly the configuration that IS always available,
      // and it's the half that would break if someone made Mathlib a hard dep.
      const preset = LEAN_PRESETS.find((p) => p.name === 'Real Analysis (chain rule)')!;
      const res = await analyzeLeanSource(preset.code, { timeoutMs: SLOW });
      expect(res.bridgeError).toBeUndefined();
      const s = ProofSession.open({
        analyze: nodeAnalyzer({ timeoutMs: SLOW }),
        source: preset.code,
        declarations: res.declarations,
        declName: 'limitAdd',
        autoRefresh: false,
      });
      await s.refresh();
      const offered = s.getState().suggestions.map((x) => x.tactic);
      // The premise: these really are proposed to every goal, unconditionally.
      // If someone quietly drops them from the candidate list, this test would
      // otherwise still "pass" while proving nothing.
      expect(MATHLIB_ONLY.every((t) => SOLVER_TACTICS.includes(t))).toBe(true);
      // And every one died in validation, because core Lean doesn't have them.
      // No mode flag was consulted anywhere on the way.
      expect(offered.filter((t) => MATHLIB_ONLY.includes(t))).toEqual([]);
    },
    SLOW,
  );

  test(
    'with Mathlib, `positivity` closes the goal that costs 20 lemmas from scratch',
    async (ctx) => {
      if (!mathlibReady) return ctx.skip();
      const s = openMathlib('halfPos');
      await s.refresh();
      const state = s.getState();
      expect(state.error).toBeUndefined();
      expect(state.goal!.targetText.replace(/\s/g, '')).toContain('0<ε/2');

      const positivity = state.suggestions.find((x) => x.tactic === 'positivity');
      expect(positivity, `offered: ${state.suggestions.map((x) => x.tactic).join(', ')}`).toBeDefined();
      // Validated, not merely listed: it really discharges the goal.
      expect(positivity!.closes).toBe(true);

      // And taking it leaves a finished proof — no open goals, no errors.
      await s.applySuggestion(positivity!.id);
      const after = s.getState().status;
      expect(after.diagnostics.filter((d) => d.severity === 'error')).toEqual([]);
      expect(after.openGoals).toBe(0);
      expect(after.complete).toBe(true);
    },
    SLOW,
  );

  test(
    'with Mathlib, `linarith` does the arithmetic the axioms had to build up',
    async (ctx) => {
      if (!mathlibReady) return ctx.skip();
      const s = openMathlib('shiftLt');
      await s.refresh();
      const closers = s
        .getState()
        .suggestions.filter((x) => x.closes)
        .map((x) => x.tactic);
      expect(closers.length, `no closer offered; got ${JSON.stringify(closers)}`).toBeGreaterThan(0);
      expect(closers.some((t) => MATHLIB_ONLY.includes(t))).toBe(true);
    },
    SLOW,
  );

  test(
    'Mathlib round-trips go through the fast path, not a whole-file re-elaboration',
    async (ctx) => {
      if (!mathlibReady) return ctx.skip();
      // The prefix-olean cache used to be core-only, so every Mathlib refresh
      // re-elaborated `import Mathlib` — tens of seconds, per goal, per trial.
      // Warm the prefix, then time a refresh: this asserts the cache is actually
      // reached in Mathlib mode, which is what makes the mode usable at all.
      const s = openMathlib('halfPos');
      await s.refresh();
      const started = Date.now();
      await s.refreshGoals();
      const elapsed = Date.now() - started;
      console.warn(`[mathlib parity] warm goal refresh: ${elapsed}ms`);
      // Deliberately loose — this is a "did the cache engage at all" check, not
      // a benchmark. A whole-file Mathlib elaboration is >20s.
      expect(elapsed).toBeLessThan(15_000);
    },
    SLOW,
  );
});
