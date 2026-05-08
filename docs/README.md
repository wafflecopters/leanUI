# Docs Index

This repo has grown a large set of design notes. This index is meant to keep the important ones easy to find and reduce duplicated “where should I start?” guidance.

## Start Here

- [`../SYSTEM_OVERVIEW.md`](../SYSTEM_OVERVIEW.md): end-to-end architecture, TT → TTK pipeline, checker, unification, normalization, and hardening ideas.
- [`../language-spec.md`](../language-spec.md): surface syntax reference. Update this whenever parser or syntax behavior changes.
- [`../TODO.md`](../TODO.md): active engineering backlog and current implementation focus.
- [`../status.md`](../status.md): short project snapshot for Conductor and quick orientation.

## Core Design Areas

- [`../RECORDS.md`](../RECORDS.md): record elaboration, projections, eta, and `extends`.
- [`../IMPLICITS-DESIGN.md`](../IMPLICITS-DESIGN.md): implicit arguments and insertion/elaboration rules.
- [`../TACTICS.md`](../TACTICS.md): tactic architecture, supported tactics, proof construction flow, and limitations.
- [`../PATTERN-UNIFICATION-PLAN.md`](../PATTERN-UNIFICATION-PLAN.md): higher-order pattern unification motivation and implementation notes.
- [`../AXIOM_K.md`](../AXIOM_K.md): deletion rule / UIP / K behavior and rationale.

## Algorithms

- [`../ALGORITHMS/PATTERN_ELABORATION.md`](../ALGORITHMS/PATTERN_ELABORATION.md)
- [`../ALGORITHMS/PATTERN_LHS_CHECKING.md`](../ALGORITHMS/PATTERN_LHS_CHECKING.md)
- [`../ALGORITHMS/PATTERN_RHS_CHECKING.md`](../ALGORITHMS/PATTERN_RHS_CHECKING.md)
- [`../ALGORITHMS/WITH_ABSTRACTION.md`](../ALGORITHMS/WITH_ABSTRACTION.md)
- [`../ALGORITHMS/IMPLICIT_RESOLUTION.md`](../ALGORITHMS/IMPLICIT_RESOLUTION.md)
- [`../ALGORITHMS/TOTALITY_CHECKING.md`](../ALGORITHMS/TOTALITY_CHECKING.md)

## Deeper Notes

- [`./meta-constraint-analysis.md`](./meta-constraint-analysis.md): constraint-solver analysis and follow-up ideas.
- [`./structural-recursion.md`](./structural-recursion.md): recursion checker details.
- [`./parameter-index-inference.md`](./parameter-index-inference.md): parameter/index classification notes.
- [`./eliminator-generation.md`](./eliminator-generation.md): eliminator generation design notes.

## Rule Of Thumb

- If you are changing parsing or syntax, update `language-spec.md`.
- If you are changing kernel/checker architecture, update `SYSTEM_OVERVIEW.md`.
- If you are changing tactic behavior or proof-state plumbing, update `TACTICS.md`.
- If you are fixing or landing a substantial project milestone, update `status.md`.
