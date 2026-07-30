# TT/TTK archive — history only

These documents describe **LeanUI's original custom dependent-type-theory
engine**, which M5 deleted (~129,000 lines: parser, elaborator, TTK kernel, type
checker, unifier, normalizer, tactic engine, `.tt` test corpus, TT presets, and
the legacy editor page).

**Do not implement against them.** Nothing they describe exists in the codebase
any more. Lean 4 is the engine now — see `CLAUDE.md` for the current
architecture.

They are kept because the reasoning is still worth reading. The problems are
real problems, and several were solved here before being solved again by asking
Lean:

- `SYSTEM_OVERVIEW.md` — the whole TT → TTK pipeline, bidirectional checking,
  metas and constraints
- `language-spec.md` — the surface syntax of the deleted `.tt` language
- `ALGORITHMS/` — pattern elaboration, totality checking, implicit resolution,
  `with`-abstraction
- `RECORDS.md`, `IMPLICITS-DESIGN.md`, `AXIOM_K.md`, `PATTERN-UNIFICATION-PLAN.md`
  — design docs for individual features
- `TACTICS.md`, `structured_editor_overview.md` — the TT tactic engine and the
  editor built on it

The one piece of guidance in here that outlived the engine: **when a feature
looks like type theory, it is type theory, and it has been studied.** The
conclusion just changed from "implement the known algorithm" to "ask the
implementation that already has it."
