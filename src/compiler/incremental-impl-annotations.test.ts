/**
 * Regression: compileIncrementalTT must apply impl annotations EAGERLY
 * (per-block, during the fresh-compile pass), the same way compileTTFromText
 * does. Without that, blocks defined after \`@syntax @impl=nat Nat\` can't
 * elaborate \`NatLit\` literals because the impl registry is empty mid-pass.
 *
 * Also: applyBlockContributions must carry forward EVERY impl/coercion
 * registry. Forgetting one (intImplByCtor, ofIntByTargetHead, simpLemmas,
 * etc.) silently drops a registration during cached-block replay.
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText, compileIncrementalTT } from './compile';
import { createIncrementalCache } from './incremental';
import { REAL_ANALYSIS_CODE } from '../presets/real-analysis';

describe('incremental compile applies impl annotations per-block', () => {
  test('real-analysis preset compiles cleanly via compileIncrementalTT', { timeout: 60000 }, () => {
    const cache = createIncrementalCache();
    const result = compileIncrementalTT(REAL_ANALYSIS_CODE, cache);
    const failures = result.blocks
      .flatMap(b => b.declarations ?? [])
      .filter(d => d.checkSuccess === false)
      .map(d => d.name);
    expect(failures).toEqual([]);
    expect(result.success).toBe(true);
  });

  test('incremental matches full-compile output for the preset', { timeout: 60000 }, () => {
    const full = compileTTFromText(REAL_ANALYSIS_CODE);
    const cache = createIncrementalCache();
    const incremental = compileIncrementalTT(REAL_ANALYSIS_CODE, cache);
    expect(incremental.success).toBe(full.success);
    expect(incremental.totalCheckErrors).toBe(full.totalCheckErrors);
    // Every impl/coercion/simp registry should be identical between paths.
    expect([...(incremental.definitions.natImplByCtor?.keys() ?? [])].sort())
      .toEqual([...(full.definitions.natImplByCtor?.keys() ?? [])].sort());
    expect([...(incremental.definitions.intImplByCtor?.keys() ?? [])].sort())
      .toEqual([...(full.definitions.intImplByCtor?.keys() ?? [])].sort());
    expect([...(incremental.definitions.ratImplByCtor?.keys() ?? [])].sort())
      .toEqual([...(full.definitions.ratImplByCtor?.keys() ?? [])].sort());
    expect([...(incremental.definitions.ofNatByTargetHead?.entries() ?? [])].sort())
      .toEqual([...(full.definitions.ofNatByTargetHead?.entries() ?? [])].sort());
    expect([...(incremental.definitions.ofIntByTargetHead?.entries() ?? [])].sort())
      .toEqual([...(full.definitions.ofIntByTargetHead?.entries() ?? [])].sort());
    expect([...(incremental.definitions.ofRatByTargetHead?.entries() ?? [])].sort())
      .toEqual([...(full.definitions.ofRatByTargetHead?.entries() ?? [])].sort());
    expect([...(incremental.definitions.simpLemmas ?? [])].sort())
      .toEqual([...(full.definitions.simpLemmas ?? [])].sort());
  });

  test('cached-block replay preserves impl registries through a re-run', { timeout: 60000 }, () => {
    const cache = createIncrementalCache();
    const r1 = compileIncrementalTT(REAL_ANALYSIS_CODE, cache);
    expect(r1.success).toBe(true);
    // Second run hits the all-blocks-cached fast path; registries must
    // still be populated identically.
    const r2 = compileIncrementalTT(REAL_ANALYSIS_CODE, cache);
    expect(r2.success).toBe(true);
    expect(r2.definitions.simpLemmas?.size).toBe(r1.definitions.simpLemmas?.size);
    expect(r2.definitions.ofIntByTargetHead?.get('Carrier'))
      .toBe(r1.definitions.ofIntByTargetHead?.get('Carrier'));
  });
});
