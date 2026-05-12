import { describe, test, expect } from 'vitest';
import { compileTTFromText } from '../compiler/compile';
import { REAL_ANALYSIS_CODE } from '../presets/real-analysis';
import { renderSubtermLatex } from './goal-computation';
import { buildReverseRegistry } from '../math-editor/tt-to-math';

/**
 * Regression: subgoals containing literal-valued witnesses produced by
 * tactics (e.g., supplying \`1\` to ltLeTrans) used to show their full
 * kernel encoding @ofRat(R, MkRat(IntOfNat 1, 1, IsSucc 0)) instead of
 * collapsing to "1". Two missing pieces:
 *   1. fullNormalize was called with an empty definitions map, so the
 *      kernel inverse-iota for MkRat couldn't fire.
 *   2. kernelTypeToSurface had a fold for @ofNat coercions but not @ofRat.
 */
describe('renderer collapses @ofRat / MkRat literal witnesses', () => {
  test('@ofRat(R, MkRat(IntOfNat 1, 1, IsSucc 0)) renders as "1"', { timeout: 30000 }, () => {
    const r = compileTTFromText(REAL_ANALYSIS_CODE);
    const definitions = (r as any).kernelEnv?.definitions ?? (r as any).definitions;
    expect(definitions).toBeTruthy();

    const term: any = {
      tag: 'App',
      fn: {
        tag: 'App',
        fn: { tag: 'Const', name: 'realOfRat' },
        arg: { tag: 'Var', index: 0 },
      },
      arg: {
        tag: 'App',
        fn: {
          tag: 'App',
          fn: {
            tag: 'App',
            fn: { tag: 'Const', name: 'MkRat' },
            arg: {
              tag: 'App',
              fn: { tag: 'Const', name: 'IntOfNat' },
              arg: { tag: 'NatLit', value: 1n },
            },
          },
          arg: { tag: 'NatLit', value: 1n },
        },
        arg: {
          tag: 'App',
          fn: { tag: 'Const', name: 'IsSucc' },
          arg: { tag: 'NatLit', value: 0n },
        },
      },
    };
    const ctx: any = [{ name: 'R', type: { tag: 'Const', name: 'Real' } }];
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    const out = renderSubtermLatex(term, ctx, definitions, rev);
    expect(out).toBe('1');
  });

  test('@ofRat(R, MkRat(IntOfNat 3, 2, IsSucc 1)) renders as a fraction, not MkRat', { timeout: 30000 }, () => {
    const r = compileTTFromText(REAL_ANALYSIS_CODE);
    const definitions = (r as any).kernelEnv?.definitions ?? (r as any).definitions;
    expect(definitions).toBeTruthy();

    const term: any = {
      tag: 'App',
      fn: {
        tag: 'App',
        fn: { tag: 'Const', name: 'realOfRat' },
        arg: { tag: 'Var', index: 0 },
      },
      arg: {
        tag: 'App',
        fn: {
          tag: 'App',
          fn: {
            tag: 'App',
            fn: { tag: 'Const', name: 'MkRat' },
            arg: {
              tag: 'App',
              fn: { tag: 'Const', name: 'IntOfNat' },
              arg: { tag: 'NatLit', value: 3n },
            },
          },
          arg: { tag: 'NatLit', value: 2n },
        },
        arg: {
          tag: 'App',
          fn: { tag: 'Const', name: 'IsSucc' },
          arg: { tag: 'NatLit', value: 1n },
        },
      },
    };
    const ctx: any = [{ name: 'R', type: { tag: 'Const', name: 'Real' } }];
    const rev = buildReverseRegistry({ symbolMap: new Map(), entries: [] });
    const out = renderSubtermLatex(term, ctx, definitions, rev);
    expect(out).not.toContain('MkRat');
    expect(out).not.toContain('IntOfNat');
    expect(out).not.toContain('IsSucc');
    expect(out).not.toContain('realOfRat');
  });
});
