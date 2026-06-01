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
  test('parses extractor output with messages and goals', () => {
    const stdout = JSON.stringify({
      messages: [{ severity: 'error', text: 'boom', startLine: 1, startCol: 0, endLine: 1, endCol: 3 }],
      goals: [{ startLine: 6, startCol: 2, endLine: 6, endCol: 5, goals: ['n : Nat\n⊢ n + 0 = n'] }],
    });
    const parsed = parseAnalyzeJson(stdout);
    expect(parsed).not.toBeNull();
    expect(parsed!.messages).toHaveLength(1);
    expect(parsed!.goals).toHaveLength(1);
    expect(parsed!.goals[0].goals[0]).toContain('⊢ n + 0 = n');
  });

  test('returns null on empty or malformed output', () => {
    expect(parseAnalyzeJson('')).toBeNull();
    expect(parseAnalyzeJson('not json')).toBeNull();
    expect(parseAnalyzeJson('{"messages":[]}')).toBeNull();
  });

  test('takes the last JSON line if extra stdout precedes it', () => {
    const stdout = ['some lean stderr leaked to stdout', JSON.stringify({ messages: [], goals: [] })].join('\n');
    expect(parseAnalyzeJson(stdout)).toEqual({ messages: [], goals: [] });
  });
});
