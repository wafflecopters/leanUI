# LeanUI

A browser-based proof assistant that renders **formal proofs as real-looking
mathematics**. Write a Lean-style script and watch it appear as typeset LaTeX
in a WYSIWYG editor; edit the rendered form and the underlying dependently-
typed term stays in sync, fully checked.

Built end-to-end in TypeScript, no external prover: a custom dependently-typed
surface language (TT) and kernel (TTK), bidirectional elaborator, constraint-
solving unifier, tactic engine, proof-tree UI, totality and structural-
recursion checks, and a LaTeX renderer — all running client-side.

## Milestone proofs

The near-term target is a live demo of three proofs, each shown as ordinary
math with autocomplete and tactic suggestions running underneath:

1. **Triangle numbers** — `∑_{i=0}^{n} i = n(n+1)/2`  *(current target)*
2. **Limits add** — `lim f + lim g = lim (f + g)`
3. **Chain rule** — `d/dx f(g(x)) = f'(g(x)) · g'(x)`

See [`status.md`](./status.md) for what's working today and what's next.

## Architecture

```
Source text
    │  Indentation-aware parser
    ▼
TT  (surface syntax, named vars)  + SourceMap
    │  Elaboration  (names → de Bruijn, holes → metas, sugar → core)
    ▼
TTK (kernel syntax, fully explicit) + ElabMap
    │  Bidirectional type checker  (metas, constraint solving, unification)
    ▼
Checked TTK
    │  Totality + structural recursion
    ▼
CompiledDeclaration  →  LaTeX renderer / proof-tree UI
```

All verification runs on **TTK**, never on the surface **TT**. The kernel,
unifier, parser, and tactic engine are domain-agnostic; numeric literals,
record sugar, real-analysis primitives, and similar concerns live in
*presets* exposed through a notation registry (`@syntax` / `@unfold`).

### Source layout

| Path | What lives there |
|------|------------------|
| `src/parser/`        | Indentation-aware parser, produces TT + source map |
| `src/compiler/`      | Elaboration pipeline, incremental compile driver, LaTeX converter |
| `src/types/`         | `tt-core.ts` (TT), `tt-kernel.ts` (TTK), context types |
| `src/tactics/`       | Tactic engine, `TacticSession`, individual tactics |
| `src/proof-tree/`    | Proof-tree view + tactic suggestion system |
| `src/math-editor/`   | WYSIWYG math editor surface |
| `src/components/`    | React UI |
| `src/presets/`       | Built-in preludes (Reals, Nats, equality, …) |
| `src/test-programs/` | `.tt` end-to-end test files |
| `server/`            | Small Express server for editor persistence |

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

Always run `npx tsc --noEmit && npm test` before declaring a change done.

## Tests

Two complementary styles:

- **Unit tests** (`*.test.ts` next to source) — exercise individual passes
  (parser, elaborator, unifier, WHNF, tactics, …).
- **`.tt` program tests** — full source files in `src/test-programs/` with
  `@test success|failure`, `@name "..."`, `@import`, and `@error` directives.
  The runner (`src/test-programs/tt-runner.test.ts`) compiles each file and
  asserts the expected outcome. Preferred for any "does this code compile?"
  check.

```bash
# Run one .tt test by name:
npx vitest run src/test-programs/tt-runner.test.ts -t "sym: Equal u v"
```

## Where to read more

Start with **[`SYSTEM_OVERVIEW.md`](./SYSTEM_OVERVIEW.md)** — it covers the
type theory, the elaboration pipeline, and the key algorithms in one place.

| Document | Purpose |
|----------|---------|
| [`SYSTEM_OVERVIEW.md`](./SYSTEM_OVERVIEW.md) | Architecture, type-checking rules, key algorithms |
| [`language-spec.md`](./language-spec.md)    | Surface-syntax specification |
| [`status.md`](./status.md)                   | Current focus, recent progress, open questions |
| [`TODO.md`](./TODO.md)                       | What is and isn't implemented yet |
| [`ALGORITHMS/`](./ALGORITHMS/)               | Implicit resolution, pattern elaboration, totality, `with`-abstraction |
| [`docs/`](./docs/)                           | Subsystem deep-dives (eliminator generation, meta-constraint analysis, structural recursion, parameter / index inference) |
| [`TACTICS.md`](./TACTICS.md)                 | Tactic engine overview |
| [`RECORDS.md`](./RECORDS.md), [`IMPLICITS-DESIGN.md`](./IMPLICITS-DESIGN.md), [`PARSER-DESIGN.md`](./PARSER-DESIGN.md), [`LIMIT-DESIGN.md`](./LIMIT-DESIGN.md) | Design notes per subsystem |
| [`AXIOM_K.md`](./AXIOM_K.md), [`K_TEST_AUDIT.md`](./K_TEST_AUDIT.md), [`DELETION_RULE_ANALYSIS.md`](./DELETION_RULE_ANALYSIS.md) | Equality / Axiom K analysis |
| [`CLAUDE.md`](./CLAUDE.md), [`AGENTS.md`](./AGENTS.md) | Coding guidelines, debugging strategy, what belongs in the kernel vs. a preset |

## Key invariants

- Verification operates only on TTK, never on surface TT.
- Kernel, engine, parser, and tactic engine **must not** hard-code
  domain-specific names (`rone`, `Zero`, `Succ`, …). Domain knowledge lives
  in presets and is exposed via `@syntax` / `@unfold` / the notation registry.
- Major data structures (`TCEnv`, `TTKTerm`, `TTerm`, `TTKContext`) are
  immutable; methods return new instances rather than mutating in place.
- Fix bugs at the lowest layer that reproduces them, and add a unit or `.tt`
  regression test before declaring done.

## License

This repository is public solely so that prospective employers,
collaborators, and reviewers may inspect the author's work. **No license is
granted to use, fork, modify, redistribute, or train ML models on this
code.** See [`LICENSE`](./LICENSE) for the full terms. Licensing inquiries:
`wcopters@gmail.com`.
