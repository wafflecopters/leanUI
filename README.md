# LeanUI

A browser-based WYSIWYG editor for **Lean 4** proofs that renders formal proofs
as real-looking mathematics. Open a Lean declaration and its proof appears as
typeset mathematical prose — "We must show 0 < ε/2. which is true, by divPos,
after showing 2 subgoals:" — that you can click into, edit structurally, and
extend from suggestions. The Lean source stays in sync, and Lean checks
everything.

Every suggestion the editor offers has been **tried against real Lean at the
real cursor** before you see it, so a tactic that isn't available simply never
appears. That is also why the same editor serves someone axiomatising their own
theory from scratch and someone importing Mathlib, with nothing anywhere asking
which one it has.

## Milestone proofs

The near-term target is a live demo of three proofs, each shown as ordinary
math with autocomplete and tactic suggestions running underneath:

1. **Triangle numbers** — `∑_{i=0}^{n} i = n(n+1)/2`  *(current target)*
2. **Limits add** — `lim f + lim g = lim (f + g)`
3. **Chain rule** — `d/dx f(g(x)) = f'(g(x)) · g'(x)`

See [`status.md`](./status.md) for what's working today and what's next.

## Architecture

```
Lean source ──► server/lean-bridge.ts ──► lean/Extract.lean ──► Lean 4
    ▲            resident workers,          InfoTree walk →
    │            prefix-olean cache,        goals · messages ·
    │            priority queue             declarations · tagged pp
    │                                              │
    └──── src/controller/  (headless ProofSession) ◄┘
                  │        tree · cursor · history · candidates ·
                  │        validation · write-back
                  ▼
           src/components/  (thin React view)
```

Lean is the entire semantic engine: type checking, elaboration, unification,
tactics, `simp`, `exact?`. `lean/Extract.lean` is a Lean meta-program that
elaborates a file and emits JSON — per-tactic goal states with Lean's own tagged
pretty-print (`CodeWithInfos`, carrying subexpression positions, which is what
makes subterms clickable), diagnostics, and declarations.

The round-trip in the middle is the whole trick: `proofTreeToLean` prints the
proof tree as a Lean tactic block recording a source range per node;
`leanGoalMapping` maps Lean's range-keyed goal states back onto those nodes.

The proof editor is a **headless controller** (`src/controller/`) with a thin
React view on top, so the same session runs in a browser, under Node against
real Lean, or against a scripted fake — and can be driven from a REPL:

```bash
npx tsx scripts/proof-repl.ts --decl limitAdd
```

An earlier version of this project implemented its own dependently-typed
language and kernel in TypeScript (~129k lines: parser, bidirectional
elaborator, constraint-solving unifier, tactic engine, totality checking). That
engine was deleted in favour of Lean; its design documents are kept in
[`docs/tt-archive/`](./docs/tt-archive/) for the reasoning, not the code.

## Running

Needs Lean 4 via [elan](https://github.com/leanprover/elan) (currently 4.30.0 /
Lake 5.0.0) on `PATH`.

```bash
npm install
npm run start        # builds the Lean extractor, then bridge + UI (http://localhost:3000)
npm run dev:web      # UI only
npm run dev:server   # bridge only (port 3457; override with LEAN_BRIDGE_PORT)
npm run lean:build   # rebuild lean/Extract.lean after editing it
npm test             # fast test gate
npm run build        # production build
```

The Lean bridge is a separate process; the UI proxies to it. If you edit
`lean/Extract.lean`, rerun `npm run lean:build` — the resident workers run the
compiled binary.

Always run `npx tsc --noEmit && npm test` before declaring a change done.

## Tests

- **Unit tests** (`*.test.ts` next to source) — the fast gate. They exercise the
  pure layers (proof-tree edits, prose generation, the Lean↔tree round-trip
  printers/parsers, candidate ranking) and, for the controller, run a full
  `ProofSession` against a **scripted fake Lean** (`src/controller/testing.ts`),
  so a test can assert on state rather than on timing.
- **Real-Lean e2e** (`*.e2e.test.ts`) — the same sessions against actual Lean.
  Excluded from `npm test`; run deliberately with `npm run test:e2e`, file-serial.

```bash
npm test                                   # fast gate (~1s)
npx vitest run src/lean/leanTacticsToTree.test.ts -t "conv-scoped simp"
scripts/guarded-run.sh -l 14 -- npm run test:e2e   # real Lean, memory-guarded
```

**Lean-heavy runs need the watchdog.** A Lean process that has imported Mathlib
holds 4–7GB resident, and stacking them will take a machine down.
`scripts/guarded-run.sh` walks the whole process tree and kills it past a limit:

```bash
scripts/guarded-run.sh -l 14 -- env E2E=1 npx vitest run src/controller/session.e2e.test.ts
```

## Where to read more

| Document | Purpose |
|----------|---------|
| [`status.md`](./status.md) | **Start here** — current focus, recent progress, blockers |
| [`LEAN_WYSIWYG_PORT.md`](./LEAN_WYSIWYG_PORT.md) | The Lean-backend architecture and the port's design |
| [`LIMIT-DESIGN.md`](./LIMIT-DESIGN.md) | `lim` as a type-directed projection; the ε-δ toolkit |
| [`TODO.md`](./TODO.md) | Longer-range list |
| [`CLAUDE.md`](./CLAUDE.md), [`AGENTS.md`](./AGENTS.md) | Coding guidelines, debugging strategy, what belongs in the engine vs. a preset |
| [`docs/tt-archive/`](./docs/tt-archive/) | Design docs for the DELETED TT engine — history only |

## Key invariants

- **Lean owns the semantics.** No type checking, elaboration, or unification
  happens in TypeScript. Never parse Lean source — a tactic argument is text
  that goes to Lean verbatim.
- **Capability is discovered, not declared.** Suggestions are proposed to every
  goal and trialled at the real cursor; an unavailable tactic errors and is
  dropped. Nothing asks whether Mathlib is loaded.
- The bridge, controller, and proof model **must not** hard-code domain-specific
  names (`rone`, `Zero`, `Succ`, …). Domain knowledge lives in the preset's Lean
  source, exposed through Lean's own attributes (`@[simp]`, `@[app_unexpander]`).
- `ProofNode`/`ProofTreeState` are immutable; transformations return new trees.
- Fix bugs at the lowest layer that reproduces them, and add a regression test
  before declaring done.

## License

This repository is public solely so that prospective employers,
collaborators, and reviewers may inspect the author's work. **No license is
granted to use, fork, modify, redistribute, or train ML models on this
code.** See [`LICENSE`](./LICENSE) for the full terms. Licensing inquiries:
`wcopters@gmail.com`.
