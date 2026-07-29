/**
 * The ONE seam between the proof controller and Lean.
 *
 * Everything the controller knows about Lean arrives through a `LeanAnalyzer`:
 * a function from "here is a Lean file" to "here are its messages, goals and
 * declarations". Nothing else in `src/controller` may reach for `fetch`, a
 * child process, or a React hook.
 *
 * That one indirection is what makes the whole proof engine drivable outside a
 * browser: the UI injects `httpAnalyzer` (POST /api/analyze), tests and the
 * REPL inject a Node analyzer that calls `analyzeLeanSource` directly, and unit
 * tests inject a scripted fake that answers from a table without running Lean
 * at all.
 */
import type { AnalyzeResult } from '../lean/types';
import { analyzeRequest } from '../lean/analyzeClient';

export interface AnalyzeInput {
  /** The complete Lean file to elaborate. */
  source: string;
  /** Unchanged text before the edited declaration — enables the server's
   *  prefix-olean fast path. `source` must equal `prefix + '\n' + body`. */
  prefix?: string;
  /** The edited declaration (with the spliced proof). */
  body?: string;
  mathlib?: boolean;
  /**
   * Latency-critical work the user is waiting on (the visible goal state).
   * Priority requests jump the server queue and bypass the browser-connection
   * semaphore; everything else (suggestion trials, discovery probes) is
   * background and throttled so it can never starve the goal refresh.
   */
  priority?: boolean;
}

/** Elaborate a Lean file. Resolves to null when the request itself failed
 *  (network/transport) — distinct from a result carrying Lean errors. */
export type LeanAnalyzer = (input: AnalyzeInput) => Promise<AnalyzeResult | null>;

/** Browser transport: POST /api/analyze through the connection semaphore. */
export const httpAnalyzer: LeanAnalyzer = (input) =>
  analyzeRequest(
    {
      source: input.source,
      prefix: input.prefix,
      body: input.body,
      mathlib: input.mathlib,
      priority: input.priority,
    },
    { background: input.priority !== true },
  );

/**
 * Wrap an analyzer with a bounded in-flight cap and a result cache keyed by the
 * exact request. Trials repeat identical sources constantly (re-validating the
 * same candidate after a cursor move), so the cache turns most of a refresh
 * into zero Lean work.
 */
export function cachingAnalyzer(inner: LeanAnalyzer, maxEntries = 200): LeanAnalyzer {
  const cache = new Map<string, AnalyzeResult>();
  return async (input) => {
    const key = `${input.mathlib ? 'M' : 'c'}|${input.source}`;
    const hit = cache.get(key);
    if (hit) return hit;
    const result = await inner(input);
    // Never cache a transport failure or a bridge error — they're transient,
    // and caching one would poison every later request for that source.
    if (result && !result.bridgeError) {
      cache.set(key, result);
      if (cache.size > maxEntries) {
        const oldest = cache.keys().next().value;
        if (oldest !== undefined) cache.delete(oldest);
      }
    }
    return result;
  };
}

/** Run `fn` over `items` with at most `limit` concurrent calls, in order. */
export async function mapPool<T>(
  items: readonly T[],
  limit: number,
  fn: (item: T, index: number) => Promise<void>,
): Promise<void> {
  let next = 0;
  const worker = async (): Promise<void> => {
    for (;;) {
      const i = next++;
      if (i >= items.length) return;
      await fn(items[i], i);
    }
  };
  await Promise.all(Array.from({ length: Math.max(1, Math.min(limit, items.length)) }, worker));
}
