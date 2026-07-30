/**
 * Shared client for POST /api/analyze — with a BACKGROUND-request semaphore.
 *
 * Browsers allow only ~6 concurrent HTTP/1.1 connections per origin. Suggestion
 * trials and discovery probes hold their connections OPEN while queued on the
 * server, so without a client-side cap they exhaust the pool and the
 * latency-critical GOAL refresh queues inside the browser behind them — goals
 * looked seconds-slow while the server was idle-fast. Background requests
 * funnel through `BG_MAX` slots; foreground (goal-state) requests bypass the
 * semaphore entirely and always find a free connection.
 */
import type { AnalyzeResult } from './types';

export interface AnalyzePayload {
  source: string;
  /** Prefix/body split → server's prefix-olean fast path. */
  prefix?: string;
  body?: string;
  mathlib?: boolean;
  /** Server-side queue-jump for goal/display refreshes. */
  priority?: boolean;
}

/** Max concurrent BACKGROUND analyze fetches. With the page-level analyze and
 *  a goal refresh alongside, total stays under the browser's ~6-per-origin
 *  connection cap. Matches the server's worker pool, so extra client
 *  concurrency couldn't run any faster anyway. */
const BG_MAX = 3;

let bgInFlight = 0;
const bgWaiters: Array<() => void> = [];

function acquireBackground(): Promise<void> {
  if (bgInFlight < BG_MAX) {
    bgInFlight++;
    return Promise.resolve();
  }
  return new Promise((res) => bgWaiters.push(res));
}

function releaseBackground(): void {
  const next = bgWaiters.shift();
  if (next) next(); // the slot transfers
  else bgInFlight = Math.max(0, bgInFlight - 1);
}

/**
 * POST an analyze request. `background: true` (suggestion trials, discovery,
 * probes, the page-level full-file analyze) throttles through the semaphore;
 * foreground (goal refreshes, interactive validations) goes straight out.
 * Returns null on network failure.
 */
export async function analyzeRequest(
  payload: AnalyzePayload,
  opts: { background?: boolean } = {},
): Promise<AnalyzeResult | null> {
  const background = opts.background === true;
  if (background) await acquireBackground();
  try {
    const resp = await fetch('/api/analyze', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(payload),
    });
    return (await resp.json()) as AnalyzeResult;
  } catch {
    return null;
  } finally {
    if (background) releaseBackground();
  }
}

/** Test hook: current in-flight background count (for semaphore tests). */
export function backgroundInFlight(): number {
  return bgInFlight;
}
