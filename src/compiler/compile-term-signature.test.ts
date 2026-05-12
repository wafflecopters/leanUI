import { describe, expect, test } from 'vitest';
import { parseTTSource } from './compile-parse';
import { prepareTermSignature, unsolvedMetasToHoles } from './compile-term-signature';
import { compileTTFromText } from './compile';
import { createNamedArgInfoLookup, createNamedArgLookup, createDefinitionsMap, type DefinitionsMap } from './term';
import { elabToKernelWithMap } from './elab';
import { prettyPrintFormatted, type TTKTerm } from './kernel';

function loadPreludeDefinitions(): DefinitionsMap {
  return compileTTFromText(`
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a
`).definitions;
}

describe('compile-term-signature', () => {
  test('unsolvedMetasToHoles rewrites nested metas and preserves rat literals', () => {
    const term = {
      tag: 'Binder',
      name: 'x',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Meta', id: '?m0' },
      body: {
        tag: 'App',
        fn: {
          tag: 'Annot',
          term: { tag: 'Meta', id: '?m1' },
          type: { tag: 'Meta', id: '?m2' },
        },
        arg: { tag: 'RatLit', num: 5n, den: 8n },
      },
    } as any as TTKTerm;

    expect(unsolvedMetasToHoles(term)).toEqual({
      tag: 'Binder',
      name: 'x',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Hole', id: '?m0' },
      body: {
        tag: 'App',
        fn: {
          tag: 'Annot',
          term: { tag: 'Hole', id: '?m1' },
          type: { tag: 'Hole', id: '?m2' },
        },
        arg: { tag: 'RatLit', num: 5n, den: 8n },
      },
    });
  });

  test('prepareTermSignature zonks implicit constructor arguments in the declaration type', () => {
    const definitions = loadPreludeDefinitions();
    const parseResult = parseTTSource(`
foo : Equal Zero Zero
foo = refl
`);
    const declBlock = parseResult.blocks.find(block => block.kind === 'declarations');
    expect(declBlock?.kind).toBe('declarations');
    if (!declBlock || declBlock.kind !== 'declarations') {
      throw new Error('expected declaration block');
    }

    const parsedDecl = declBlock.declarations[0];
    const elabMap = new Map();
    const typePath = [{ kind: 'field', name: 'type' }] as const;
    const kernelType = elabToKernelWithMap(
      parsedDecl.type!,
      elabMap,
      [...typePath],
      [...typePath],
      undefined,
      createNamedArgInfoLookup(definitions),
    );

    const result = prepareTermSignature({
      name: parsedDecl.name,
      kind: 'term',
      surfaceType: parsedDecl.type,
      surfaceValue: parsedDecl.value,
      kernelType,
      elabMap,
    }, definitions);

    expect(result.success).toBe(true);
    if (!result.success) {
      throw new Error('expected signature preparation to succeed');
    }

    const prettyType = prettyPrintFormatted(
      result.prepared.zonkedKernelType,
      [],
      undefined,
      { namedArgLookup: createNamedArgLookup(result.prepared.termEnv.definitions) },
    );
    expect(prettyType).toContain('Equal');
    expect(prettyType).toContain('Nat');
    expect(prettyType).toContain('Zero');
  });

  test('prepareTermSignature reports unsolved signature metas when not allowed', () => {
    const result = prepareTermSignature({
      name: 'holey',
      kind: 'term',
      surfaceType: { tag: 'Hole', id: '_sig', type: { tag: 'Sort', level: { tag: 'ULit', n: 0 } } } as any,
      kernelType: { tag: 'Hole', id: '_sig' } as any,
    }, createDefinitionsMap());

    expect(result.success).toBe(false);
    if (result.success) {
      throw new Error('expected signature preparation to fail');
    }
    expect(result.errors[0].message).toContain('unsolved metas');
  });

  test('prepareTermSignature wraps non-TCEnv signature failures into declaration errors', () => {
    const result = prepareTermSignature({
      name: 'x',
      kind: 'term',
      surfaceType: { tag: 'Const', name: 'Nat' } as any,
      kernelType: { tag: 'Const', name: 'Nat' } as any,
    }, createDefinitionsMap());

    expect(result.success).toBe(false);
    if (result.success) {
      throw new Error('expected signature preparation to fail');
    }
    expect(result.errors).toHaveLength(1);
    expect(result.errors[0].message).toContain('Type definition not found: Nat');
  });
});
