import { Assumption, LetElement } from '../types/enhanced-focus';

export const PROOF_WORKSPACE_KEYS = {
  selectedHypothesisId: 'proofWorkspace.selectedHypothesisId',
  selectedHypothesisIndex: 'proofWorkspace.selectedHypothesisIndex',
  selectedHypothesisName: 'proofWorkspace.selectedHypothesisName',
  selectedLetBindingId: 'proofWorkspace.selectedLetBindingId',
  selectedLetBindingIndex: 'proofWorkspace.selectedLetBindingIndex',
  onDeleteHypothesis: 'proofWorkspace.onDeleteHypothesis',
  onEditLetBinding: 'proofWorkspace.onEditLetBinding',
  onDeleteLetBinding: 'proofWorkspace.onDeleteLetBinding',
} as const;

export function buildHypothesisSelectionMetadata(
  selectedHypothesis: Assumption | null,
  selectedIndex: number | null,
  isInFocusChain: boolean
): Record<string, unknown> {
  if (!selectedHypothesis || selectedIndex === null) {
    return isInFocusChain
      ? {
          [PROOF_WORKSPACE_KEYS.selectedHypothesisId]: null,
          [PROOF_WORKSPACE_KEYS.selectedHypothesisIndex]: null,
          [PROOF_WORKSPACE_KEYS.selectedHypothesisName]: null,
        }
      : {};
  }

  return {
    [PROOF_WORKSPACE_KEYS.selectedHypothesisId]: selectedHypothesis.id,
    [PROOF_WORKSPACE_KEYS.selectedHypothesisIndex]: selectedIndex,
    [PROOF_WORKSPACE_KEYS.selectedHypothesisName]: selectedHypothesis.name,
  };
}

export function buildLetBindingSelectionMetadata(
  selectedLetBinding: LetElement | null,
  selectedIndex: number | null,
  isInFocusChain: boolean
): Record<string, unknown> {
  if (!selectedLetBinding || selectedIndex === null) {
    return isInFocusChain
      ? {
          [PROOF_WORKSPACE_KEYS.selectedLetBindingId]: null,
          [PROOF_WORKSPACE_KEYS.selectedLetBindingIndex]: null,
        }
      : {};
  }

  return {
    [PROOF_WORKSPACE_KEYS.selectedLetBindingId]: selectedLetBinding.id,
    [PROOF_WORKSPACE_KEYS.selectedLetBindingIndex]: selectedIndex,
  };
}
