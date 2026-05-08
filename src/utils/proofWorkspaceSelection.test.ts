import { describe, expect, test } from 'vitest';
import {
  buildHypothesisSelectionMetadata,
  buildLetBindingSelectionMetadata,
  PROOF_WORKSPACE_KEYS,
} from './proofWorkspaceSelection';

describe('proofWorkspaceSelection', () => {
  test('buildHypothesisSelectionMetadata populates selected hypothesis fields', () => {
    const metadata = buildHypothesisSelectionMetadata(
      {
        id: 'h0',
        name: 'h',
        type: null,
        description: 'hypothesis',
        introducedBy: 'user',
      },
      2,
      true
    );

    expect(metadata[PROOF_WORKSPACE_KEYS.selectedHypothesisId]).toBe('h0');
    expect(metadata[PROOF_WORKSPACE_KEYS.selectedHypothesisIndex]).toBe(2);
    expect(metadata[PROOF_WORKSPACE_KEYS.selectedHypothesisName]).toBe('h');
  });

  test('buildHypothesisSelectionMetadata clears hypothesis fields at section root', () => {
    const metadata = buildHypothesisSelectionMetadata(null, null, true);

    expect(metadata[PROOF_WORKSPACE_KEYS.selectedHypothesisId]).toBeNull();
    expect(metadata[PROOF_WORKSPACE_KEYS.selectedHypothesisIndex]).toBeNull();
    expect(metadata[PROOF_WORKSPACE_KEYS.selectedHypothesisName]).toBeNull();
  });

  test('buildLetBindingSelectionMetadata populates selected let fields', () => {
    const metadata = buildLetBindingSelectionMetadata(
      {
        id: 'let-0',
        name: 'x',
        value: { id: 'expr', type: 'variable', raw: 'x', children: [] },
        editorMode: { tag: 'value' },
      } as any,
      1,
      true
    );

    expect(metadata[PROOF_WORKSPACE_KEYS.selectedLetBindingId]).toBe('let-0');
    expect(metadata[PROOF_WORKSPACE_KEYS.selectedLetBindingIndex]).toBe(1);
  });

  test('buildLetBindingSelectionMetadata clears let fields at section root', () => {
    const metadata = buildLetBindingSelectionMetadata(null, null, true);

    expect(metadata[PROOF_WORKSPACE_KEYS.selectedLetBindingId]).toBeNull();
    expect(metadata[PROOF_WORKSPACE_KEYS.selectedLetBindingIndex]).toBeNull();
  });
});
