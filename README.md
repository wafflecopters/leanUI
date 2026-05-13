# LeanUI

> **Note on use:** This repository is public solely so prospective employers,
> collaborators, and reviewers can inspect the author's work. **No license is
> granted to use, copy, modify, or redistribute this code.** See
> [`LICENSE`](./LICENSE) for the full notice.

A bridge between Overleaf and Lean: write LaTeX-like math with proof correctness,
or write Lean-style code that renders as real-looking LaTeX in a WYSIWYG editor.

LeanUI ships its own dependently-typed language (TT), an elaborator and kernel
type checker, a tactic engine, a proof-tree UI, and a LaTeX renderer — all
running in the browser.

## Vision

The near-term goal is a live demo of three milestone proofs, each presented as
real-looking math with autocomplete and tactic suggestions under the hood:

1. **Triangle numbers** — `∑_{i=0}^{n} i = n(n+1)/2` (current target)
2. **Limits add** — `lim f + lim g = lim (f + g)`
3. **Chain rule** — `d/dx f(g(x)) = f'(g(x))·g'(x)`

See `status.md` for current focus, recent progress, and open work.

## Architecture

```
Source Text
    ↓ Parser + indentation grouper
TT (surface syntax) + SourceMap
    ↓ Elaboration  (named vars → de Bruijn, holes → metas, sugar → core)
TTK (kernel syntax) + ElabMap
    ↓ Bidirectional type checker  (metas, constraint solving, unification)
Checked TTK
    ↓ Totality + structural recursion checks
CompiledDeclaration  →  LaTeX renderer / proof tree UI
```

All verification runs on **TTK** (kernel terms), never on **TT** (surface).

Top-level source layout:

| Path | What lives there |
|------|------------------|
| `src/parser/` | Indentation-aware parser, produces TT + source map |
| `src/compiler/` | Elaboration pipeline, incremental compile driver, LaTeX converter |
| `src/types/` | `tt-core.ts` (TT), `tt-kernel.ts` (TTK), context types |
| `src/tactics/` | Tactic engine, `TacticSession`, individual tactics (intro, rewrite, …) |
| `src/proof-tree/` | Proof-tree view + tactic suggestion system |
| `src/math-editor/` | WYSIWYG math editor surface |
| `src/components/` | React UI |
| `src/presets/` | Built-in preludes (Reals, Nats, equality, …) |
| `src/test-programs/` | `.tt` end-to-end test files; see "Tests" below |
| `server/` | Small Express server for editor persistence |

## Running

```bash
npm install
npm run start          # dev server (UI) + backend server
npm run dev            # UI only
npm run server         # backend only
npm test               # full vitest suite
npm test -- -t "name"  # run a single test by substring
npm run build          # production build
```

## Tests

Two complementary styles:

- **Unit tests** (`*.test.ts` next to source) — exercise individual passes
  (parser, elaborator, unifier, WHNF, tactics, …).
- **`.tt` program tests** — full source files in `src/test-programs/` with
  `@test success|failure` / `@name "..."` / `@import` / `@error` directives.
  The runner (`src/test-programs/tt-runner.test.ts`) compiles each file and
  asserts. Prefer this style for any "does this code compile?" check.

```bash
# Run one .tt test:
npx vitest run src/test-programs/tt-runner.test.ts -t "sym: Equal u v"
```

Always run `npx tsc --noEmit && npm test` before claiming a change is done.

## Documentation Index

Start with `SYSTEM_OVERVIEW.md`. Everything else is either reference material
or a design note for a specific subsystem.

### Read first
- **`SYSTEM_OVERVIEW.md`** — architecture, type-checking rules, key algorithms
- **`language-spec.md`** — surface-syntax specification
- **`status.md`** — current focus, recent progress, up-next, open questions
- **`TODO.md`** — what is and isn't implemented yet

### Algorithm reference (`ALGORITHMS/`)
- `IMPLICIT_RESOLUTION.md` — implicit argument insertion
- `PATTERN_ELABORATION.md`, `PATTERN_LHS_CHECKING.md`, `PATTERN_RHS_CHECKING.md` — pattern matching pipeline
- `TOTALITY_CHECKING.md` — coverage and termination
- `WITH_ABSTRACTION.md` — `with`-clause desugaring

### Subsystem deep-dives (`docs/`)
- `eliminator-generation.md` — how recursors are generated for inductives
- `meta-constraint-analysis.md` — constraint solver internals
- `parameter-index-inference.md` — inferring inductive parameters vs indices
- `structural-recursion.md` — termination checker
- `README.md` — index of the deep-dives

### Design notes (project root)
- `RECORDS.md` — records elaborate to inductives
- `IMPLICITS-DESIGN.md` — implicit-argument design
- `PARSER-DESIGN.md` — indentation handling, multi-line expressions
- `TACTICS.md` — tactic engine overview
- `LIMIT-DESIGN.md` — limits in the real-analysis preset
- `NUMERIC_LITERALS_PLAN.md`, `PATTERN-UNIFICATION-PLAN.md`,
  `WITH_CLAUSE_IMPLICIT_ARGS_PLAN.md`, `zonk_checking_plan.md` — staged plans
- `AXIOM_K.md`, `K_TEST_AUDIT.md`, `DELETION_RULE_ANALYSIS.md` — equality / K
- `PADDING_HOLES_FIX.md`, `whnf-match-fix-summary.md` — post-mortems on tricky bugs
- `structured_editor_overview.md` — editor UX notes

### For contributors
- **`CLAUDE.md` / `AGENTS.md`** — coding guidelines, debugging strategy, what
  belongs in the kernel vs. in a preset, how to add `.tt` tests. Read these
  before making non-trivial changes.

## Key invariants

- Verification operates only on TTK, never on surface TT.
- Kernel / engine / parser / tactic engine **must not** hard-code
  domain-specific names (`rone`, `Zero`, `Succ`, …). Domain knowledge lives in
  presets and is exposed via `@syntax` / `@unfold` / the notation registry.
- Major data structures (`TCEnv`, `TTKTerm`, `TTerm`, `TTKContext`) are
  immutable. Methods return new instances; never mutate in place.
- Fix bugs at the lowest layer that reproduces them; add a unit test or `.tt`
  regression test before declaring done.
