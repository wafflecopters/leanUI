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
1. ✅ DONE — Destructure rows show CONDITION types inline: "Write fProof as ⟨dfPos : 0 < δ_F, fFn⟩." — types from the child goal's hypotheses, shown when prop-like (isProp/dependsOn signal), muted for data.
2. ✅ DONE — EpsDeltaWitness displays as its ∀-meaning (lambda-aware unexpander reuses the function's own binder: no hygiene dagger, no beta-redex).
3. Choose-merge: have+obtain fusion → "Choose δ_F and fProof with … since …" (keep rename affordance: rename targets destructure names).
4. ✅ DONE — mathTextToLatex application spacing: `ltLeTrans (…) δF δG h₁ a` renders with NO gaps between juxtaposed args once a parenthesized arg breaks call-detection (`)δ_Fδ_Gh₁a`); fix the restructure/tokenize pipeline the way expr-latex.ts fixed the tree view.
5. Citations: "since divTwoPos(ε, epsPos)" → instantiated-fact-first or name-as-citation; fix missing app gap in since-exprs (`(ε/2)h₂`).
5. "This holds by construction, after showing 2 subgoals: / Goal 1 …" → paper voice: for ∃/structure intro: "Take δ := δ_F. It remains to show …" (merge value goal + witness); nested Goal blocks flatten when a branch is one line.
6. ✅ DONE — presentation battery DONE (limitAdd + triangleSum, 8/8). Vector-space preset LANDED (Field'/VectorSpace/combo/InSpan/Spans/Independent/Basis in core Prop; nilIndependent + nilSpanCombo proved; spanDrop and basisExists are the sorry exercises). NEXT: prove spanDrop + basisExists (strong induction on list length, classical case on independence), seed the proof, add its battery describe.
7. ✅ DONE — Presentation e2e: for each of the three proofs, a test that renders prose items and asserts shape properties (no `mk` ceremony, no raw-term justifications, conditions folded, no repeated adjacent goals) — generic assertions, not golden text.

## /loop 2: adversarial presentation pass (WITHOUT breaking editability)
Gate: the adversarial reviewer's report (agent still running). When it lands, triage every offense into: renderer fix / prose-generator fix / preset notation / won't-fix (with reason), then implement top-down. Already-known offenses from the user's screenshots (fix regardless of report):
1. Projection rendering: `vs.length` renders as `vs(.length)`, `a.succ` as `a(.succ)`, `W.V` as `W(.V)` — the f(x)-application style treats a dotted projection as a call with a leading-dot argument. Postfix projections must render as `vs.length` (or better: `.length` → |vs| style only via preset notation). Pipeline: codeWithInfos tokenize/restructure.
2. `++` renders as `+ +` (two spaced pluses) — List append must be one operator token.
3. Statement binder chain mashes: `∀K : Field'W : VectorSpace(K)(n : Nat)…` — no separators between ∀-binders in the theorem header rendering.
4. Anonymous-ctor exacts read raw: "By ⟨[], h, nilIndependent⟩." — consider "Take bs := [] with …" phrasing (value+proofs tuple).
Constraint for ALL fixes: every row stays clickable/editable exactly as now (names renameable, subterms selectable, rows deletable) — presentation changes must be display-layer or preset-notation only, never lossy rewrites of the tree.

## /loop 2 TRIAGE of the adversarial report (2026-08-10)
Already fixed since the review ran: dev-build break (mid-edit hot reload), a(.succ)/W(.V)/vs(.length) projection mangles, "++" spacing, settled "no goals" false errors. limitAdd's open right case = intended exercise (won't-fix). Remaining, ranked:

R1. ✅ DONE — **Daggered names leak** (basisExistsAux): `K✝ : Field'` in CONTEXT (auto-bound section variable never named in the statement — fix in preset: bind K/W explicitly in the theorem signature) and `x✝ : Independent ∨ …` in the Let-line (an unnamed intro — find why the case hyp shows daggered in intro prose; likely the Let-line lists a hypothesis the split later names; dedup with R6).
R2. ✅ DONE — **Statement header binder soup**: `∀K : Field'W : VectorSpace(K)(n : Nat)…` — no separators between ∀ binders; mixed bare/parenthesized styles. Render "Let K be a …"-style or at minimum comma-separate binders. (Renderer: recognizeForall chain.)
R3. **Justifications are terms, not reasons** (global #1): "since divTwoPos(ε, epsPos)". SMART-UI mechanism preserving editability: preset lemmas get /-- doc comments --/ ("halving preserves positivity", "the triangle inequality"); extractor surfaces docstrings; the citation renders the DOC TEXT with the term on hover/click (term stays the editable truth). Fall back to current call-style when no doc.
R4. **fx vs f(x) inconsistency** (limitAdd): `|fx − L|` in Goal-1/absTriangle rows vs `f(x)` in displays — the app rule doesn't fire inside |…| bars in mathTextToLatex. Make juxtaposition inside bars apply too.
R5. **Goal-N scaffolding → suffices voice**: "This holds by construction, after showing 2 subgoals: Goal 1: We must choose a value of type ℝ. By δ_F." → "It suffices to exhibit δ; take δ := δ_F." Merge value-goal header+exact (existing TODO item); vary "We must show" (suffices/remains/i.e.).
R6. **Let-line duplicates the split**: basisExistsAux's Let lists the disjunction hyp, then "Either …" restates it verbatim. When an intro'd hyp is immediately case-split, drop it from the Let-line.
R7. **Induction-on-data case labels**: "Case (zero.nil):"/"Case (cons (a, rest)):" → conditions "vs = []" / "vs = a :: rest" (we know the constructor + scrutinee; render the equation). Also triangleSum "Inductive step (n = succ (n))" BINDS THE SAME LETTER — uniquify the case param against the scrutinee name (enrichment bug, real).
R8. **⟨tuple⟩ exacts**: "By ⟨[], h, nilIndependent⟩." → "Take bs := [] …" phrasing for ∃-witness tuples (value + proofs).
R9. **Proof./∎ framing**: open with "Proof." row, end with ∎ (qed item exists; ensure it appears when complete, and add the opener).
R10. **Chips in prose**: "(mulDistribLeft) ×" delete buttons and "✓ solved" rows inside the document — keep the affordances but move to hover-reveal/margin styling.
R11. Font consistency pass: one convention for lemma names vs hypothesis names vs variables (currently 3 systems); `epsPos`/`hlen` in math italic reads as products (texNameForProse for ALL name sites).
R12. Misc punctuation: dangling colons at row ends; "if" hanging before displays; capitalize-after-display.
Won't-fix (by design, note in status): suggestion tray/goal panel in the open case (it IS an editor); unevaluated `ε/2 + ε/2` and `(0+1)·0` (honest goals from Lean — a Compute pill exists for the user to take).
