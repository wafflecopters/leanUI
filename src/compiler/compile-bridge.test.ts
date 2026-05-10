import { describe, expect, test } from 'vitest';
import {
  collectAppSpine,
  kernelTypeToSurface,
  replaceHoleInSurfaceTerm,
  surfaceTermToKernel,
} from './compile-bridge';

describe('compile-bridge', () => {
  test('surfaceTermToKernel converts simple supported forms structurally', () => {
    const surface = {
      tag: 'App',
      fn: { tag: 'Const', name: 'f' },
      arg: {
        tag: 'Sort',
        level: { tag: 'ULit', n: 0 },
      },
    } as any;

    expect(surfaceTermToKernel(surface)).toEqual({
      tag: 'App',
      fn: { tag: 'Const', name: 'f' },
      arg: { tag: 'Sort', level: { tag: 'ULit', n: 0 } },
    });
  });

  test('collectAppSpine preserves head and argument order', () => {
    const spine = collectAppSpine({
      tag: 'App',
      fn: {
        tag: 'App',
        fn: { tag: 'Const', name: 'f' },
        arg: { tag: 'Var', index: 0 },
      },
      arg: { tag: 'Const', name: 'x' },
    } as any);

    expect(spine.head).toEqual({ tag: 'Const', name: 'f' });
    expect(spine.args).toEqual([
      { tag: 'Var', index: 0 },
      { tag: 'Const', name: 'x' },
    ]);
  });

  test('kernelTypeToSurface omits implicit arguments when namedArgMap is available', () => {
    const definitions = {
      terms: new Map([
        ['Vec', { namedArgMap: new Map([['A', 0]]) }],
      ]),
      inductiveTypes: new Map(),
      inductiveNameOfConstructor: new Map(),
      natImplByCtor: new Map(),
      ofNatByTargetHead: new Map(),
      natOpByFn: new Map(),
    } as any;

    const surface = kernelTypeToSurface({
      tag: 'App',
      fn: {
        tag: 'App',
        fn: { tag: 'Const', name: 'Vec' },
        arg: { tag: 'Const', name: 'Nat' },
      },
      arg: { tag: 'Var', index: 0 },
    } as any, definitions);

    expect(surface).toEqual({
      tag: 'App',
      fn: { tag: 'Const', name: 'Vec' },
      arg: { tag: 'Var', index: 0 },
    });
  });

  test('replaceHoleInSurfaceTerm rewrites nested occurrences without touching others', () => {
    const term = {
      tag: 'Binder',
      name: 'x',
      binderKind: { tag: 'BPiTT' },
      domain: { tag: 'Hole', id: '_scrut0_type', type: { tag: 'Sort', level: { tag: 'ULit', n: 0 } } },
      body: {
        tag: 'App',
        fn: { tag: 'Const', name: 'Vec' },
        arg: { tag: 'Hole', id: '_scrut0_type', type: { tag: 'Sort', level: { tag: 'ULit', n: 0 } } },
      },
    } as any;

    const replacement = { tag: 'Const', name: 'Nat' } as any;
    const rewritten = replaceHoleInSurfaceTerm(term, '_scrut0_type', replacement) as any;

    expect(rewritten.domain).toEqual(replacement);
    expect(rewritten.body.arg).toEqual(replacement);
  });
});
