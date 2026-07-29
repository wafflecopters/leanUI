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
POLL_SECS=3

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

tree_rss_kb() {
  local pids total
  pids=$(tree_pids "$1")
  total=0
  for p in $pids; do
    r=$(ps -o rss= -p "$p" 2>/dev/null | tr -d ' ')
    [ -n "$r" ] && total=$((total + r))
  done
  echo "$total"
}

kill_tree() {
  local pids
  pids=$(tree_pids "$1")
  kill -TERM $pids 2>/dev/null
  sleep 2
  kill -KILL $pids 2>/dev/null
}

peak=0
while kill -0 "$ROOT" 2>/dev/null; do
  rss=$(tree_rss_kb "$ROOT")
  [ "$rss" -gt "$peak" ] && peak=$rss
  if [ "$rss" -gt "$LIMIT_KB" ]; then
    echo "[guarded-run] MEMORY LIMIT BREACHED: tree RSS $((rss / 1024 / 1024))GB > ${LIMIT_GB}GB — killing process tree" >&2
    kill_tree "$ROOT"
    wait "$ROOT" 2>/dev/null
    echo "[guarded-run] killed. peak tree RSS: $((peak / 1024))MB" >&2
    exit 137
  fi
  sleep "$POLL_SECS"
done

wait "$ROOT"
code=$?
echo "[guarded-run] done (exit $code). peak tree RSS: $((peak / 1024))MB" >&2
exit $code
