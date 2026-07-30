/**
 * The Node-side `LeanAnalyzer`: real Lean, no HTTP server, no browser.
 *
 * This is what lets the REPL and the e2e tests drive a `ProofSession` against
 * the actual Lean toolchain — same controller, same code paths, different
 * transport.
 *
 * NODE ONLY. It imports `server/lean-bridge`, which spawns processes. Nothing
 * reachable from the browser entry point may import this file.
 */
import { analyzeLeanSource, shutdownLeanBridge } from '../../server/lean-bridge';
import { cachingAnalyzer, type LeanAnalyzer } from './analyzer';

/** Release Lean's persistent workers so the process can exit. Headless callers
 *  MUST call this when done — the workers hold the event loop open. */
export { shutdownLeanBridge };

export interface NodeAnalyzerOptions {
  /** Per-request Lean timeout. The first call compiles the whole prefix, which
   *  on a large preset is slow; later calls hit the prefix-olean cache. */
  timeoutMs?: number;
  /** Cache identical requests (on by default — suggestion trials repeat the
   *  same sources constantly). */
  cache?: boolean;
  /** Called with each request's duration, for the REPL's timing display. */
  onTiming?: (ms: number) => void;
}

export function nodeAnalyzer(opts: NodeAnalyzerOptions = {}): LeanAnalyzer {
  const base: LeanAnalyzer = async (input) => {
    const started = Date.now();
    const result = await analyzeLeanSource(input.source, {
      prefix: input.prefix,
      body: input.body,
      mathlib: input.mathlib,
      priority: input.priority,
      timeoutMs: opts.timeoutMs ?? 300_000,
    });
    opts.onTiming?.(Date.now() - started);
    return result;
  };
  return opts.cache === false ? base : cachingAnalyzer(base);
}
