---
name: update-status
description: Regenerate status.md with current project state from recent commits and project docs.
---

# Update Status

Regenerate `status.md` so external tools (like Conductor) have an accurate snapshot of this project.

## Steps

1. **Gather current state** — Read these sources:
   - `TODO.md` — current tasks and priorities
   - `git log --oneline -10` — recent commits
   - Current `status.md` — preserve Vision, Near-Term Goal, Milestone Proofs, and Open Questions sections

2. **Regenerate `status.md`** with these sections:
   - **Vision** — Keep stable
   - **Near-Term Goal** — Keep stable unless the target has shifted
   - **Milestone Proofs** — Keep stable (update checkmarks as proofs are completed)
   - **Current Focus** — What's actively being worked on
   - **Recent Progress** — From git log + TODO.md, ~5-8 bullet points
   - **Up Next** — Priority-ordered upcoming work
   - **Open Questions** — Keep stable unless resolved or new ones arise

3. **Stage the file** — Run `git add status.md`

## Format

Keep status.md concise — a busy person should grasp the project state in 30 seconds. No more than ~40 lines of content.
