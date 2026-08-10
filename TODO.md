# TODO

`status.md` is the live tracker (current focus, recent progress, blockers). This
file is the longer-range list.

M5 deleted the custom TT/TTK engine, and with it most of what used to be on this
list — the parser work, constraint-solver hardening, pattern matching and
wildcard naming, records, the Prop deep dive, totality checking, the TT tactic
engine. Those are Lean's problems now. The archived reasoning is in
[`docs/tt-archive/`](./docs/tt-archive/).

## Milestone proofs

1. [x] **Triangle numbers** — `∑_{i=0}^{n} i = n(n+1)/2` (proved in-preset)
2. [ ] **Limits add** — `lim f + lim g = lim (f + g)`
       The math is DONE: a sorry-free hand proof from the preset's own toolkit,
       pinned in `src/lean/realAnalysisPositivity.e2e.test.ts` (`#print axioms`
       confirms no `sorryAx`). What remains is making the editor OFFER each step.
3. [ ] **Chain rule** — `d/dx f(g(x)) = f'(g(x)) · g'(x)`

## Editor ergonomics — the limitAdd path

This is the current focus: every step of a proof we can already write by hand
should be reachable by clicking.

- [ ] **Order-compare two reals.** Where `deltaF` and `deltaG` are both in scope,
      offer the case split (`leTotal` / the `rmin`, `minElim`, `minLeLeft/Right`
      family) that picking `δ := rmin deltaF deltaG` needs.
- [ ] **Seed the `limitAdd` preset with the built-up proof prefix**, so iterating
      on the NEXT step doesn't mean rebuilding the first ten by hand.
- [ ] Surface `limF.eps_delta` as a chip at the `∃δ` goal (suspected cause:
      projection candidates can't read the `lim⟦x0⟧`-notation hypothesis type).
- [ ] Destructure flow for DPair/Pair — the `(δ, witness)` pairs.
- [ ] Witness-first constructor ordering when the witness is `rmin δ1 δ2`.

## `lim` as a projection

See [LIMIT-DESIGN.md](LIMIT-DESIGN.md) for the design.

- [ ] Port `limitScalarAll` and prove `limit_pull_scalar`: `c * lim f = lim (c * f)`
- [ ] Restore the derivatives section (blocked behind the same dependency)

## Mathlib

- [ ] Decide whether Mathlib becomes the default preset. `mathlibParity.e2e.test.ts`
      pins that ONE engine serves both audiences — the from-scratch file where
      Mathlib tactics must never appear, and the Mathlib file where they must
      appear AND close the goal.
- [ ] A Mathlib real-analysis preset: the same `Limit` statement over real ℝ,
      where `positivity`/`linarith`/`norm_num` close the arithmetic legs.
- [ ] **Memory is the constraint here.** A Mathlib-loaded Lean process holds
      4–7GB. Pools are split and capped (`LEANUI_MATHLIB_WORKERS` defaults to 1);
      always run Lean-heavy suites under `scripts/guarded-run.sh`.

## Editing surface

- [ ] MathRow → Lean source for type/value edits — editing a declaration's
      STATEMENT, not just its proof. (The proof direction round-trips today.)
- [ ] Type-at-cursor in the text editor (Lean reports it; needs wiring).
- [ ] Keyboard shortcut to comment/uncomment.
- [ ] Keyboard shortcut to toggle the binder at the cursor between `()` and `{}`.

## Rendering parity

The battery lives in the render regression tests; keep it green as new notation
lands: `\lim` with under-subscript, ℝ via the `Carrier` unexpander, spelled-out
Greek (`epsilon` → ε), `∀ x ∈ T` binder prose, implication chains, `f(x)`
application style, display-math sizing.

- [ ] Paper-style density is in (short goals inline, long ones display, the
      edited row expands) — keep tuning as real proofs get longer.

## Paper-rendering, remaining
- **Preset notation for the statement itself**: an `Add (Carrier R → Carrier R)` instance so `limitAdd` can be STATED as `Limit (f + g) x0 (L + M)` (goals then print `(f+g)(x)`), and a display form for `EpsDeltaWitness` (its ∀-meaning, or a compact `δ ⊨ (f, x₀, L, ε)` if too wide). Statement changes → the seeded proof must be re-verified by replay, so this wants its own pass.
- **Choose-merge**: a `have h := …` immediately followed by `obtain ⟨a, b⟩ := h` is the mathematician's "Choose a and b with … since …" — fuse the two prose rows into one. Design note: keep the bound names clickable (rename targets the DESTRUCTURE node's names), which is why the quick version wasn't shipped.
- **Merge value-goal lines**: "Goal 1: We must choose a value of type ℝ. / Take δ_F." into one row: "Take δ_F : ℝ." (needs the subgoalHeader to see its branch's solving exact).

## /loop: natural presentation (limitAdd + triangleSum + vector-space basis)
Active loop goal: these three proofs read decently natural. Iterate: pick top gap → implement generically → verify vs real Lean → pin with tests → commit → screenshot-compare.
1. Destructure rows show CONDITION types inline (user request): "Write fProof as ⟨dfPos : 0 < δ_F, fFn⟩." — types from the child goal's hypotheses, shown when prop-like (isProp/dependsOn signal), muted for data.
2. EpsDeltaWitness display form (preset unexpander → its ∀-meaning); update goal-text e2e assertions; replay-verify seed.
3. Choose-merge: have+obtain fusion → "Choose δ_F and fProof with … since …" (keep rename affordance: rename targets destructure names).
4. Citations: "since divTwoPos(ε, epsPos)" → instantiated-fact-first or name-as-citation; fix missing app gap in since-exprs (`(ε/2)h₂`).
5. "This holds by construction, after showing 2 subgoals: / Goal 1 …" → paper voice: for ∃/structure intro: "Take δ := δ_F. It remains to show …" (merge value goal + witness); nested Goal blocks flatten when a branch is one line.
6. Presets/batteries: triangleSum (NAT_MATH) prose battery; NEW from-scratch finite-dim vector-space preset (span/linear-independence/basis, `every finite VS has a basis` as the exercise) — stress-tests genericity beyond ℝ.
7. Presentation e2e: for each of the three proofs, a test that renders prose items and asserts shape properties (no `mk` ceremony, no raw-term justifications, conditions folded, no repeated adjacent goals) — generic assertions, not golden text.
