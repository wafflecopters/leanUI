import { describe, expect, test } from 'vitest';
import { parseLeanJson, parseAnalyzeJson } from './lean-bridge';

describe('parseLeanJson', () => {
  test('parses lean --json NDJSON into messages', () => {
    const stdout = [
      '{"severity":"information","pos":{"line":2,"column":0},"endPos":{"line":2,"column":6},"data":"good : Nat"}',
      '{"severity":"error","pos":{"line":3,"column":17},"endPos":{"line":3,"column":28},"data":"Type mismatch"}',
    ].join('\n');
    const msgs = parseLeanJson(stdout);
    expect(msgs).toHaveLength(2);
    expect(msgs[0]).toMatchObject({ severity: 'information', startLine: 2, startCol: 0, text: 'good : Nat' });
    expect(msgs[1]).toMatchObject({ severity: 'error', startLine: 3, startCol: 17, endCol: 28 });
  });

  test('skips non-JSON noise and objects without positions', () => {
    const stdout = ['warning: some build noise', '{"severity":"error","data":"no pos"}', ''].join('\n');
    expect(parseLeanJson(stdout)).toHaveLength(0);
  });

  test('defaults endPos to pos when absent', () => {
    const stdout = '{"severity":"warning","pos":{"line":5,"column":2},"data":"w"}';
    const [m] = parseLeanJson(stdout);
    expect(m).toMatchObject({ startLine: 5, startCol: 2, endLine: 5, endCol: 2 });
  });
});

describe('parseAnalyzeJson', () => {
  test('parses extractor output with messages, goals, and declarations', () => {
    const stdout = JSON.stringify({
      messages: [{ severity: 'error', text: 'boom', startLine: 1, startCol: 0, endLine: 1, endCol: 3 }],
      goals: [
        {
          startLine: 6,
          startCol: 2,
          endLine: 6,
          endCol: 5,
          goals: [
            {
              case: 'succ',
              hyps: [{ names: ['n'], type: { t: 'text', s: 'Nat' } }],
              targetTagged: { t: 'append', kids: [{ t: 'tag', pos: '/', child: { t: 'text', s: 'n + 0 = n' } }] },
              plain: 'n : Nat\n⊢ n + 0 = n',
            },
          ],
        },
      ],
      declarations: [
        { name: 'good', kind: 'def', prettyType: 'Nat', prettyValue: '42', line: 1, col: 0 },
        { name: 'add_zero_ex', kind: 'theorem', prettyType: '∀ (n : Nat), n + 0 = n', line: 5, col: 0 },
      ],
    });
    const parsed = parseAnalyzeJson(stdout);
    expect(parsed).not.toBeNull();
    expect(parsed!.messages).toHaveLength(1);
    expect(parsed!.goals).toHaveLength(1);
    const gstate = parsed!.goals[0].goals[0];
    expect(gstate.case).toBe('succ');
    expect(gstate.hyps).toEqual([{ names: ['n'], type: { t: 'text', s: 'Nat' } }]);
    expect(gstate.targetTagged.t).toBe('append');
    expect(gstate.plain).toContain('⊢ n + 0 = n');
    expect(parsed!.declarations).toHaveLength(2);
    expect(parsed!.declarations[0]).toMatchObject({ name: 'good', kind: 'def', prettyValue: '42' });
    expect(parsed!.declarations[1]).toMatchObject({ name: 'add_zero_ex', kind: 'theorem' });
    expect(parsed!.declarations[1].prettyValue).toBeUndefined();
  });

  test('a goal state without targetTagged falls back to a text node from plain', () => {
    const stdout = JSON.stringify({
      messages: [],
      goals: [{ startLine: 1, startCol: 0, endLine: 1, endCol: 1, goals: [{ hyps: [], plain: '⊢ True' }] }],
    });
    const g = parseAnalyzeJson(stdout)!.goals[0].goals[0];
    expect(g.targetTagged).toEqual({ t: 'text', s: '⊢ True' });
    expect(g.hyps).toEqual([]);
    expect(g.case).toBeUndefined();
  });

  test('coerces unknown declaration kind to def and defaults missing declarations to []', () => {
    const withBadKind = JSON.stringify({
      messages: [],
      goals: [],
      declarations: [{ name: 'x', kind: 'structure', prettyType: 'T', line: 1, col: 0 }],
    });
    expect(parseAnalyzeJson(withBadKind)!.declarations[0].kind).toBe('def');
    // declarations absent (older extractor) → empty array, still valid
    const noDecls = JSON.stringify({ messages: [], goals: [] });
    expect(parseAnalyzeJson(noDecls)!.declarations).toEqual([]);
  });

  test('returns null on empty or malformed output', () => {
    expect(parseAnalyzeJson('')).toBeNull();
    expect(parseAnalyzeJson('not json')).toBeNull();
    expect(parseAnalyzeJson('{"messages":[]}')).toBeNull();
  });

  test('takes the last JSON line if extra stdout precedes it', () => {
    const stdout = ['some lean stderr leaked to stdout', JSON.stringify({ messages: [], goals: [], declarations: [] })].join('\n');
    expect(parseAnalyzeJson(stdout)).toEqual({ messages: [], goals: [], declarations: [] });
  });
});

describe('createAnalyzeLimiter', () => {
  test('caps concurrency and priority jumps the queue', async () => {
    const { createAnalyzeLimiter } = await import('./lean-bridge');
    const limiter = createAnalyzeLimiter(1);
    const order: string[] = [];

    // Occupy the single slot.
    await limiter.acquire(false);

    // Queue: two background trials, then one priority goal refresh.
    const bg1 = limiter.acquire(false).then(() => order.push('bg1'));
    const bg2 = limiter.acquire(false).then(() => order.push('bg2'));
    const pri = limiter.acquire(true).then(() => order.push('priority'));

    // Nothing runs until the slot frees.
    await Promise.resolve();
    expect(order).toEqual([]);

    limiter.release(); // → priority first, despite arriving last
    await pri;
    expect(order).toEqual(['priority']);

    limiter.release(); // → bg1 (FIFO among non-priority)
    await bg1;
    limiter.release(); // → bg2
    await bg2;
    expect(order).toEqual(['priority', 'bg1', 'bg2']);
    limiter.release(); // final release drops the running count safely
  });

  test('priority waiters keep FIFO order among themselves', async () => {
    const { createAnalyzeLimiter } = await import('./lean-bridge');
    const limiter = createAnalyzeLimiter(1);
    const order: string[] = [];
    await limiter.acquire(false);
    const p1 = limiter.acquire(true).then(() => order.push('p1'));
    const p2 = limiter.acquire(true).then(() => order.push('p2'));
    limiter.release();
    await p1;
    limiter.release();
    await p2;
    expect(order).toEqual(['p1', 'p2']);
    limiter.release();
  });
});
