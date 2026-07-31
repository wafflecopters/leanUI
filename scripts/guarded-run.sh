#!/bin/bash
# Run a command under a memory watchdog: if the combined RSS of the command's
# entire process tree (vitest forks, node, every `extract`/`lake`/`lean` child)
# exceeds the limit, the whole tree is killed immediately.
#
# Born from the 2026-07-28 incident where the Mathlib e2e drove the machine
# into the ground: each Mathlib-loaded Lean process holds 4-7GB resident, and
# stacked pools + one-shot spill passed physical RAM before anyone noticed.
# The RSS samplers used that day only matched `extract --serve`, so the
# heaviest processes (one-shot extract / `lake env lean`) were invisible.
# This guard walks the process TREE instead — nothing in the tree can hide.
#
# Usage:
#   scripts/guarded-run.sh [-l GB] -- <command...>
#   scripts/guarded-run.sh -l 14 -- env E2E=1 npx vitest run src/controller/mathlibParity.e2e.test.ts
#
# Exit codes: command's own exit code, or 137 if killed by the watchdog.

set -u

LIMIT_GB=14
POLL_SECS=1

while [ $# -gt 0 ]; do
  case "$1" in
    -l) LIMIT_GB="$2"; shift 2 ;;
    --) shift; break ;;
    *) echo "usage: $0 [-l GB] -- <command...>" >&2; exit 2 ;;
  esac
done
[ $# -gt 0 ] || { echo "usage: $0 [-l GB] -- <command...>" >&2; exit 2; }

LIMIT_KB=$((LIMIT_GB * 1024 * 1024))

"$@" &
ROOT=$!

# All descendant pids of $1 (inclusive), via BFS over the ps pid/ppid table.
tree_pids() {
  ps -axo pid=,ppid= | awk -v root="$1" '
    { kids[$2] = kids[$2] " " $1 }
    END {
      queue = root; result = ""
      while (queue != "") {
        n = split(queue, q, " "); queue = ""
        for (i = 1; i <= n; i++) {
          if (q[i] == "" || seen[q[i]]) continue
          seen[q[i]] = 1; result = result " " q[i]
          queue = queue kids[q[i]]
        }
      }
      print result
    }'
}

# Lean processes ANYWHERE on the system, whatever their parent.
#
# The tree walk alone is not enough, and believing it was is how this script
# under-reported a run that took the machine into swap. A Lean worker whose
# parent dies — a vitest fork being recycled, a killed test process — is
# reparented to init, drops out of the tree, and becomes invisible to a
# BFS from ROOT while still holding several GB. Those orphans are exactly
# the ones that accumulate across runs and take a machine down, so they are
# what this most needs to see.
#
# Matching by name has the opposite bias to the tree walk (it catches Lean
# processes this run did not start), which is the right bias for a safety
# limit: over-report and stop, rather than under-report and continue.
lean_pids() {
  pgrep -f '\.lake/build/bin/extract|lean --run|lake env' 2>/dev/null
}

# Union of the tree and every Lean process, deduped.
watched_pids() {
  { tree_pids "$1"; lean_pids; } | tr ' ' '\n' | grep -E '^[0-9]+$' | sort -un
}

watched_rss_kb() {
  local total=0 r
  for p in $(watched_pids "$1"); do
    r=$(ps -o rss= -p "$p" 2>/dev/null | tr -d ' ')
    [ -n "$r" ] && total=$((total + r))
  done
  echo "$total"
}

kill_tree() {
  local pids
  pids=$(watched_pids "$1")
  kill -TERM $pids 2>/dev/null
  sleep 2
  kill -KILL $pids 2>/dev/null
}

peak=0
while kill -0 "$ROOT" 2>/dev/null; do
  rss=$(watched_rss_kb "$ROOT")
  [ "$rss" -gt "$peak" ] && peak=$rss
  if [ "$rss" -gt "$LIMIT_KB" ]; then
    echo "[guarded-run] MEMORY LIMIT BREACHED: watched RSS $((rss / 1024 / 1024))GB > ${LIMIT_GB}GB — killing the tree AND every Lean process" >&2
    kill_tree "$ROOT"
    wait "$ROOT" 2>/dev/null
    echo "[guarded-run] killed. peak watched RSS: $((peak / 1024))MB" >&2
    exit 137
  fi
  sleep "$POLL_SECS"
done

wait "$ROOT"
code=$?
leftover=$(lean_pids | wc -l | tr -d ' ')
echo "[guarded-run] done (exit $code). peak watched RSS: $((peak / 1024))MB; Lean processes still alive: $leftover" >&2
exit $code
