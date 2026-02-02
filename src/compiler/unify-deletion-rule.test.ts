/**
 * Tests for the deletion rule implementation in unification.
 *
 * The deletion rule (axiom K) allows reflexive equations (x = x) to be
 * automatically eliminated during unification. Without K, these equations
 * must fail.
 */

import { describe, test, expect } from 'vitest';
import { unifyTerms, UnifyOptions } from './unify';
import { mkVar } from './kernel';
import { createDefinitionsMap } from './term';

describe('Deletion rule (axiom K) in unification', () => {
  const baseOptions: UnifyOptions = {
    mode: 'pattern',
    definitions: createDefinitionsMap(),
  };

  test('Reflexive equation succeeds WITH K (default)', () => {
    const x = mkVar(0);
    const result = unifyTerms(x, x, { ...baseOptions, assumeK: true });

    expect(result.success).toBe(true);
    if (result.success) {
      expect(result.substitutions).toEqual([]);
    }
  });

  test('Reflexive equation FAILS WITHOUT K', () => {
    const x = mkVar(0);
    const result = unifyTerms(x, x, { ...baseOptions, assumeK: false });

    expect(result.success).toBe(false);
    if (!result.success) {
      expect(result.reason).toBe('deletion-rule');
    }
  });

  test('Different variables unify regardless of K', () => {
    const x = mkVar(0);
    const y = mkVar(1);

    // With K
    const resultWithK = unifyTerms(x, y, {
      ...baseOptions,
      assumeK: true,
      flexibleVars: true
    });
    expect(resultWithK.success).toBe(true);

    // Without K
    const resultWithoutK = unifyTerms(x, y, {
      ...baseOptions,
      assumeK: false,
      flexibleVars: true
    });
    expect(resultWithoutK.success).toBe(true);
  });
});
