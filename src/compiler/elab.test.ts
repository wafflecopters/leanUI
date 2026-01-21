import { describe, test, expect } from 'vitest';
import { elabToKernel } from './elab';
import { TTerm } from './surface';
import { TTKTerm } from './kernel';

describe('Elaboration: MultiBinder', () => {
  test('MultiBinder Pi expands to nested Binder terms', () => {
    // (a b : Nat) -> T
    const surface: TTerm = {
      tag: 'MultiBinder',
      names: ['a', 'b'],
      binderKind: { tag: 'BPiTT' },
      domain: { tag: 'Const', name: 'Nat' },
      body: { tag: 'Const', name: 'T' }
    };

    const kernel = elabToKernel(surface);

    // Should expand to: (a : Nat) -> (b : Nat) -> T
    expect(kernel.tag).toBe('Binder');
    if (kernel.tag === 'Binder') {
      expect(kernel.name).toBe('a');
      expect(kernel.binderKind.tag).toBe('BPi');
      expect(kernel.domain.tag).toBe('Const');
      if (kernel.domain.tag === 'Const') {
        expect(kernel.domain.name).toBe('Nat');
      }

      // Inner binder
      expect(kernel.body.tag).toBe('Binder');
      if (kernel.body.tag === 'Binder') {
        expect(kernel.body.name).toBe('b');
        expect(kernel.body.binderKind.tag).toBe('BPi');
        expect(kernel.body.domain.tag).toBe('Const');

        // Innermost body
        expect(kernel.body.body.tag).toBe('Const');
        if (kernel.body.body.tag === 'Const') {
          expect(kernel.body.body.name).toBe('T');
        }
      }
    }
  });

  test('MultiBinder Lambda expands to nested Binder terms', () => {
    // \(x y : A) => body
    const surface: TTerm = {
      tag: 'MultiBinder',
      names: ['x', 'y'],
      binderKind: { tag: 'BLamTT' },
      domain: { tag: 'Const', name: 'A' },
      body: { tag: 'Var', index: 1 } // x (outer var)
    };

    const kernel = elabToKernel(surface);

    // Should expand to: \(x : A) => \(y : A) => body
    expect(kernel.tag).toBe('Binder');
    if (kernel.tag === 'Binder') {
      expect(kernel.name).toBe('x');
      expect(kernel.binderKind.tag).toBe('BLam');

      // Inner binder
      expect(kernel.body.tag).toBe('Binder');
      if (kernel.body.tag === 'Binder') {
        expect(kernel.body.name).toBe('y');
        expect(kernel.body.binderKind.tag).toBe('BLam');

        // Innermost body should be Var 1 (still pointing to x)
        expect(kernel.body.body.tag).toBe('Var');
        if (kernel.body.body.tag === 'Var') {
          expect(kernel.body.body.index).toBe(1);
        }
      }
    }
  });

  test('MultiBinder with many names expands correctly', () => {
    // (a b c d : T) -> R
    const surface: TTerm = {
      tag: 'MultiBinder',
      names: ['a', 'b', 'c', 'd'],
      binderKind: { tag: 'BPiTT' },
      domain: { tag: 'Const', name: 'T' },
      body: { tag: 'Const', name: 'R' }
    };

    const kernel = elabToKernel(surface);

    // Should be 4 nested Binders
    let current: TTKTerm = kernel;
    const names = ['a', 'b', 'c', 'd'];

    for (let i = 0; i < 4; i++) {
      expect(current.tag).toBe('Binder');
      if (current.tag === 'Binder') {
        expect(current.name).toBe(names[i]);
        expect(current.binderKind.tag).toBe('BPi');
        current = current.body;
      }
    }

    // Final body should be R
    expect(current.tag).toBe('Const');
    if (current.tag === 'Const') {
      expect(current.name).toBe('R');
    }
  });

  test('Single-name Binder elaborates normally (no MultiBinder)', () => {
    // (x : A) -> B
    const surface: TTerm = {
      tag: 'Binder',
      name: 'x',
      binderKind: { tag: 'BPiTT' },
      domain: { tag: 'Const', name: 'A' },
      body: { tag: 'Const', name: 'B' }
    };

    const kernel = elabToKernel(surface);

    expect(kernel.tag).toBe('Binder');
    if (kernel.tag === 'Binder') {
      expect(kernel.name).toBe('x');
      expect(kernel.binderKind.tag).toBe('BPi');
    }
  });
});
