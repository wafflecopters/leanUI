import { describe, expect, test } from 'vitest';
import { compileIncrementalTT } from '../compiler/compile';
import { createIncrementalCache } from '../compiler/incremental';
import type { CompileResult, CompiledDeclaration } from '../compiler/compile';
import { deserializeIndexPath, type SourceMap } from '../types/source-position';
import {
  collectAllCompiledDeclarations,
  collectCompiledDeclEntries,
  findRangeViaElabMapWithSuffix,
  getTypeInfoAtCursor,
  mapErrorPathToSourceRange,
  replaceDeclarationNameInSource,
  resolveInitialEditorCode,
  slugifyPresetName,
} from './textEditorModel';

describe('textEditorModel', () => {
  test('slugifyPresetName normalizes preset names for URLs', () => {
    expect(slugifyPresetName('Nat Math (Tactics)')).toBe('nat-math-tactics');
    expect(slugifyPresetName(' Real Analysis ')).toBe('real-analysis');
  });

  test('resolveInitialEditorCode picks matching slug or falls back to first preset', () => {
    const presets = [
      { name: 'First Preset', code: 'first' },
      { name: 'Nat Math (Tactics)', code: 'nat' },
    ];

    expect(resolveInitialEditorCode(presets, 'nat-math-tactics')).toBe('nat');
    expect(resolveInitialEditorCode(presets, 'missing')).toBe('first');
    expect(resolveInitialEditorCode(presets, null)).toBe('first');
  });

  test('collectCompiledDeclEntries excludes with auxiliaries while full collection keeps all declarations', () => {
    const compileResult = {
      blocks: [{
        sourceLines: ['foo'],
        startLine: 10,
        declarations: [
          { name: 'main', isWithAuxiliary: false },
          { name: 'aux', isWithAuxiliary: true },
        ],
      }],
    } as unknown as CompileResult;

    const entries = collectCompiledDeclEntries(compileResult, true);
    expect(entries).toHaveLength(1);
    expect(entries[0].decl.name).toBe('main');
    expect(entries[0].blockSource).toBe('foo');
    expect(entries[0].blockStartLine).toBe(10);

    const allDecls = collectAllCompiledDeclarations(compileResult, true);
    expect(allDecls).toHaveLength(2);
  });

  test('replaceDeclarationNameInSource rewrites only the declaration name span', () => {
    const code = 'foo : Nat\nfoo = Zero';
    const sourceMap = new Map([
      ['name', {
        start: { line: 1, col: 1 },
        end: { line: 1, col: 4 },
      }],
    ]) as SourceMap;

    const entry = {
      decl: { sourceMap } as CompiledDeclaration,
      blockSource: code,
      blockStartLine: 0,
    };

    expect(replaceDeclarationNameInSource(code, entry, 'bar')).toBe('bar : Nat\nfoo = Zero');
    expect(replaceDeclarationNameInSource(code, undefined, 'bar')).toBe(code);
  });

  test('mapErrorPathToSourceRange preserves elaboration suffixes', () => {
    const sourceMap = new Map([
      ['type.body.body.domain.fn.arg.arg', {
        start: { line: 4, col: 7 },
        end: { line: 4, col: 18 },
      }],
    ]) as SourceMap;
    const elabMap = new Map([
      ['type.body.body.body.domain.fn', 'type.body.body.domain.fn'],
    ]);

    expect(
      findRangeViaElabMapWithSuffix(
        deserializeIndexPath('type.body.body.body.domain.fn.arg.arg'),
        elabMap,
        sourceMap
      )
    ).toEqual({
      start: { line: 4, col: 7 },
      end: { line: 4, col: 18 },
    });

    expect(
      mapErrorPathToSourceRange(
        deserializeIndexPath('type.body.body.body.domain.fn.arg.arg'),
        elabMap,
        sourceMap
      )
    ).toEqual({
      start: { line: 4, col: 7 },
      end: { line: 4, col: 18 },
    });
  });

  test('getTypeInfoAtCursor returns source expression and inferred type for a checked term', () => {
    const code = [
      'id : {A : Type} -> A -> A',
      'id x = x',
    ].join('\n');

    const compileResult = compileIncrementalTT(code, createIncrementalCache());
    const decl = compileResult.blocks[0]?.declarations[0];
    const rhsRange = decl?.sourceMap?.get('value.clauses[0].rhs');

    expect(decl?.checkSuccess).toBe(true);
    expect(rhsRange).toBeDefined();
    if (!rhsRange) {
      return;
    }

    const result = getTypeInfoAtCursor(
      { lineNumber: rhsRange.start.line, column: rhsRange.start.col },
      compileResult,
      code
    );

    expect(result?.kind).toBe('term');
    if (result?.kind !== 'term') {
      return;
    }
    expect(result.expression).toBe('x');
    expect(result.info.prettyType).toBe('A');
  });

  test('getTypeInfoAtCursor returns undefined outside typed declarations', () => {
    const code = [
      'id : {A : Type} -> A -> A',
      'id x = x',
    ].join('\n');

    const compileResult = compileIncrementalTT(code, createIncrementalCache());

    expect(
      getTypeInfoAtCursor({ lineNumber: 10, column: 1 }, compileResult, code)
    ).toBeUndefined();
  });
});
