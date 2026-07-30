/**
 * The background-fetch semaphore exists because browsers cap concurrent
 * connections per origin (~6): suggestion trials hold connections open while
 * queued server-side, and without the cap they starve the goal refresh INSIDE
 * the browser. Foreground requests must bypass the semaphore entirely.
 */
import { afterEach, describe, expect, test, vi } from 'vitest';
import { analyzeRequest, backgroundInFlight } from './analyzeClient';

const tick = () => new Promise((r) => setTimeout(r, 10));

function deferredFetch() {
  const resolvers: Array<() => void> = [];
  const fetchMock = vi.fn(
    () =>
      new Promise<Response>((res) => {
        resolvers.push(() =>
          res(new Response(JSON.stringify({ success: true, messages: [], goals: [], declarations: [], durationMs: 0 }))),
        );
      }),
  );
  vi.stubGlobal('fetch', fetchMock);
  return { fetchMock, resolvers };
}

afterEach(() => {
  vi.unstubAllGlobals();
});

describe('analyzeRequest background semaphore', () => {
  test('background caps at 3 in flight; foreground bypasses; slots recycle', async () => {
    const { fetchMock, resolvers } = deferredFetch();

    // 5 background requests → only 3 fetches actually start.
    const bg = Array.from({ length: 5 }, () => analyzeRequest({ source: 's' }, { background: true }));
    await tick();
    expect(fetchMock).toHaveBeenCalledTimes(3);
    expect(backgroundInFlight()).toBe(3);

    // A foreground (goal-refresh) request goes straight out — 4th fetch —
    // even with the background lanes saturated.
    const fg = analyzeRequest({ source: 'goal', priority: true });
    await tick();
    expect(fetchMock).toHaveBeenCalledTimes(4);

    // Completing requests admits the queued ones; everything drains.
    for (;;) {
      const r = resolvers.shift();
      if (!r) break;
      r();
      await tick();
    }
    const results = await Promise.all([fg, ...bg]);
    expect(fetchMock).toHaveBeenCalledTimes(6); // 5 background + 1 foreground
    expect(results.every((x) => x !== null)).toBe(true);
    expect(backgroundInFlight()).toBe(0);
  });

  test('network failure returns null and releases the slot', async () => {
    vi.stubGlobal('fetch', vi.fn(() => Promise.reject(new Error('boom'))));
    const r = await analyzeRequest({ source: 's' }, { background: true });
    expect(r).toBeNull();
    expect(backgroundInFlight()).toBe(0);
  });
});
