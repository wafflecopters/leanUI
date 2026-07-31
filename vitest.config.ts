import { defineConfig, configDefaults } from 'vitest/config';

/**
 * `npm test` is the fast smoke gate — it must stay fast enough to run on every
 * change, so it excludes the `*.e2e.test.ts` suites.
 *
 * Those drive REAL Lean, and Lean processes are BIG. Measured on this project's
 * real-analysis preset, in CORE mode with no Mathlib anywhere: a resident
 * `extract --serve` worker settles at **2.7–4.4GB**, not the few hundred MB this
 * file used to claim. The default pool is three of them, so a single Node
 * process holding a bridge costs ~10GB before anything else happens — and the
 * dev server is one such process, sitting there all day.
 *
 * Run them deliberately, and through the watchdog:
 *   scripts/guarded-run.sh -l 14 -- npm run test:e2e
 */
const includeE2E = process.env.E2E === '1';

if (includeE2E) {
  // ONE worker per test process, not three. A test run does not need
  // validation parallelism the way an interactive session does, and three
  // multi-GB workers per fork is most of the reason an e2e run can push a
  // machine into swap. Only set as a default — an explicit override wins, so
  // a deliberate perf experiment is still possible.
  process.env.LEANUI_EXTRACT_WORKERS ??= '1';
  process.env.LEANUI_MATHLIB_WORKERS ??= '1';
}

export default defineConfig({
  test: {
    exclude: [...configDefaults.exclude, ...(includeE2E ? [] : ['**/*.e2e.test.ts'])],
    // E2E runs are file-SERIAL: every test file that touches the bridge gets
    // its own fork with its own worker pool, and each pool is multiple GB.
    // Parallel files stack those pools — that (plus one-shot spill) is how two
    // sessions drove the machine to ~100GB. Serial keeps at most one Lean fleet
    // alive at a time.
    //
    // Serial is necessary but NOT sufficient: a fork that dies without running
    // `afterAll` orphans its workers, they are reparented to init, and they
    // survive the run holding GBs. Check for leftovers after an e2e run —
    // `guarded-run.sh` now reports the count when it exits.
    ...(includeE2E ? { fileParallelism: false } : {}),
  },
});
