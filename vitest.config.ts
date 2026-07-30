import { defineConfig, configDefaults } from 'vitest/config';

/**
 * `npm test` is the fast smoke gate — it must stay fast enough to run on every
 * change, so it excludes the `*.e2e.test.ts` suites.
 *
 * Those drive REAL Lean: each test file that imports the bridge spawns its own
 * pool of resident `extract --serve` processes (a few hundred MB each), which
 * competes for cores with the CPU-bound TT suites running in parallel. Mixed
 * into the default run they turned an 80-second suite into a 24-minute one and
 * pushed unrelated tests past their timeouts.
 *
 * Run them deliberately:  npm run test:e2e
 */
const includeE2E = process.env.E2E === '1';

export default defineConfig({
  test: {
    exclude: [...configDefaults.exclude, ...(includeE2E ? [] : ['**/*.e2e.test.ts'])],
    // E2E runs are file-SERIAL: every test file that touches the bridge gets
    // its own fork with its own worker pool, and a Mathlib-loaded pool is
    // multiple GB resident. Parallel files stack those pools — that (plus
    // one-shot spill) is how two sessions drove the machine to ~100GB.
    // Serial keeps at most one Lean fleet alive at a time.
    ...(includeE2E ? { fileParallelism: false } : {}),
  },
});
