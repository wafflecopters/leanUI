import { describe, expect, test, vi } from 'vitest';

import { parseAssumeKDirective } from './compile-directives';

describe('compile directives', () => {
  test('returns undefined when @assumeK is absent', () => {
    expect(parseAssumeKDirective('foo : Type\nfoo = Type\n')).toBeUndefined();
  });

  test('accepts bare and commented @assumeK directives as true', () => {
    expect(parseAssumeKDirective('@assumeK\nfoo : Type\nfoo = Type\n')).toBe(true);
    expect(parseAssumeKDirective('-- @assumeK=true\nfoo : Type\nfoo = Type\n')).toBe(true);
  });

  test('accepts explicit @assumeK=false', () => {
    expect(parseAssumeKDirective('@assumeK=false\nfoo : Type\nfoo = Type\n')).toBe(false);
  });

  test('warns and falls back to false for invalid @assumeK values', () => {
    const warn = vi.spyOn(console, 'warn').mockImplementation(() => {});
    expect(parseAssumeKDirective('@assumeK=maybe\nfoo : Type\nfoo = Type\n')).toBe(false);
    expect(warn).toHaveBeenCalledOnce();
    warn.mockRestore();
  });
});
