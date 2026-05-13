import { describe, test, expect } from 'vitest';
import { compileTTFromText, compileIncrementalTT } from '../../compiler/compile';
import { createIncrementalCache } from '../../compiler/incremental';
import { REAL_ANALYSIS_CODE } from '../../presets/real-analysis';

const BUGGY_SUFFIX = `

limit_add_3 : {R : Real} -> (f g h : Carrier R -> Carrier R) ->
  (x0 Lf Lg Lh : Carrier R) ->
  (limF : Limit f x0 Lf) -> (limG : Limit g x0 Lg) -> (limH : Limit h x0 Lh) ->
  Equal (radd (lim f x0 limF) (radd (lim g x0 limG) (lim h x0 limH)))
        (lim (\\x => radd (f x) (radd (g x) (h x))) x0)
limit_add_3 = ?TODO
`;

describe('lim partial application bug', () => {
  test('compileTTFromText: partially applied lim should produce a type error', { timeout: 120000 }, () => {
    const result = compileTTFromText(REAL_ANALYSIS_CODE + BUGGY_SUFFIX);
    const allDecls = result.blocks.flatMap(b => b.declarations);
    const limit_add_3 = allDecls.find(d => d.name === 'limit_add_3');

    expect(limit_add_3).toBeDefined();
    console.log('compileTTFromText checkSuccess:', limit_add_3!.checkSuccess);
    console.log('compileTTFromText checkErrors:', limit_add_3!.checkErrors?.map(e => ({ msg: e.message, sev: e.severity })));

    expect(limit_add_3!.checkSuccess).toBe(false);
    expect(limit_add_3!.checkErrors.length).toBeGreaterThan(0);
  });

  test('compileIncrementalTT: partially applied lim should produce a type error', { timeout: 120000 }, () => {
    // This is the code path the UI uses
    const cache = createIncrementalCache();
    const result = compileIncrementalTT(REAL_ANALYSIS_CODE + BUGGY_SUFFIX, cache);
    const allDecls = result.blocks.flatMap(b => b.declarations);
    const limit_add_3 = allDecls.find(d => d.name === 'limit_add_3');

    console.log('compileIncrementalTT total blocks:', result.blocks.length);
    console.log('compileIncrementalTT total decls:', allDecls.length);
    console.log('compileIncrementalTT all decl names:', allDecls.map(d => d.name));

    if (!limit_add_3) {
      // Declaration might not appear at all — check the last block
      const lastBlock = result.blocks[result.blocks.length - 1];
      console.log('Last block parse success:', lastBlock.parseSuccess);
      console.log('Last block name resolution:', lastBlock.nameResolutionSuccess);
      console.log('Last block decl count:', lastBlock.declarations.length);
      console.log('Last block decl names:', lastBlock.declarations.map(d => d.name));
      if (!lastBlock.parseSuccess) {
        console.log('Parse errors:', lastBlock.parseErrors);
      }
      if (!lastBlock.nameResolutionSuccess) {
        console.log('Name errors:', lastBlock.nameResolutionErrors?.map(e => e.message));
      }
    }

    expect(limit_add_3).toBeDefined();
    console.log('compileIncrementalTT checkSuccess:', limit_add_3!.checkSuccess);
    console.log('compileIncrementalTT checkErrors:', limit_add_3!.checkErrors?.map(e => ({ msg: e.message, sev: e.severity })));

    expect(limit_add_3!.checkSuccess).toBe(false);
    expect(limit_add_3!.checkErrors.length).toBeGreaterThan(0);
  });

  test('compileIncrementalTT with warm cache: partially applied lim should produce a type error', { timeout: 120000 }, () => {
    // Simulate: first compile the good preset, then add the buggy code (like user editing)
    const cache = createIncrementalCache();
    // First compilation — warm the cache
    compileIncrementalTT(REAL_ANALYSIS_CODE, cache);

    // Second compilation — add the buggy code
    const result = compileIncrementalTT(REAL_ANALYSIS_CODE + BUGGY_SUFFIX, cache);
    const allDecls = result.blocks.flatMap(b => b.declarations);
    const limit_add_3 = allDecls.find(d => d.name === 'limit_add_3');

    console.log('warm cache checkSuccess:', limit_add_3?.checkSuccess);
    console.log('warm cache checkErrors:', limit_add_3?.checkErrors?.map(e => ({ msg: e.message, sev: e.severity })));

    if (!limit_add_3) {
      const lastBlock = result.blocks[result.blocks.length - 1];
      console.log('warm cache last block parse:', lastBlock.parseSuccess);
      console.log('warm cache last block nameRes:', lastBlock.nameResolutionSuccess);
      console.log('warm cache last block decls:', lastBlock.declarations.map(d => d.name));
    }

    expect(limit_add_3).toBeDefined();
    expect(limit_add_3!.checkSuccess).toBe(false);
    expect(limit_add_3!.checkErrors.length).toBeGreaterThan(0);
  });

  test('error marker data is valid for Monaco editor', { timeout: 120000 }, () => {
    // Test that the error has valid data for placing a Monaco marker
    const cache = createIncrementalCache();
    compileIncrementalTT(REAL_ANALYSIS_CODE, cache);
    const result = compileIncrementalTT(REAL_ANALYSIS_CODE + BUGGY_SUFFIX, cache);

    // Find the block containing limit_add_3
    let targetBlock: typeof result.blocks[0] | undefined;
    let targetDecl: typeof result.blocks[0]['declarations'][0] | undefined;
    for (const block of result.blocks) {
      for (const decl of block.declarations) {
        if (decl.name === 'limit_add_3') {
          targetBlock = block;
          targetDecl = decl;
          break;
        }
      }
    }

    expect(targetBlock).toBeDefined();
    expect(targetDecl).toBeDefined();

    console.log('block startLine:', targetBlock!.startLine);
    console.log('block isComment:', targetBlock!.isComment);
    console.log('block parseSuccess:', targetBlock!.parseSuccess);
    console.log('block nameResSuccess:', targetBlock!.nameResolutionSuccess);
    console.log('block nameResErrors:', targetBlock!.nameResolutionErrors?.map(e => e.message));
    console.log('decl checkSuccess:', targetDecl!.checkSuccess);
    console.log('decl checkErrors count:', targetDecl!.checkErrors?.length);

    // Check each error's env for valid indexPath
    for (const err of targetDecl!.checkErrors) {
      console.log('error message:', err.message);
      console.log('error severity:', err.severity);
      console.log('error has env:', !!err.env);
      console.log('error env indexPath:', err.env?.indexPath);
      console.log('decl has sourceMap:', !!targetDecl!.sourceMap);
      console.log('decl has elabMap:', !!targetDecl!.elabMap);

      // Check sourceMap/elabMap sizes
      console.log('sourceMap size:', targetDecl!.sourceMap?.size);
      console.log('elabMap size:', targetDecl!.elabMap?.size);
    }

    // The block should NOT be a comment
    expect(targetBlock!.isComment).toBe(false);
    // Should have valid errors
    expect(targetDecl!.checkErrors.length).toBeGreaterThan(0);
    // startLine should be reasonable (near end of file)
    const sourceLines = (REAL_ANALYSIS_CODE + BUGGY_SUFFIX).split('\n');
    console.log('total lines in source:', sourceLines.length);
    expect(targetBlock!.startLine).toBeGreaterThan(400); // Should be near end
  });
});
