import { describe, expect, test, vi } from 'vitest';
import { createApplicationCommandTree } from './navigationCommands';
import { PROOF_WORKSPACE_KEYS } from '../utils/proofWorkspaceSelection';

describe('createApplicationCommandTree', () => {
  const tree = createApplicationCommandTree();

  test('hypotheses delete invokes the real delete callback and returns to section root', () => {
    const onDeleteHypothesis = vi.fn();
    const command = tree.findCommand('d', ['Hypotheses', '1']);
    expect(command?.id).toBe('hypotheses-delete');

    const result = command!.execute({
      navigationPath: ['Hypotheses', '1'],
      metadata: {
        [PROOF_WORKSPACE_KEYS.selectedHypothesisId]: 'h1',
        [PROOF_WORKSPACE_KEYS.selectedHypothesisIndex]: 1,
        [PROOF_WORKSPACE_KEYS.onDeleteHypothesis]: onDeleteHypothesis,
      },
    });

    expect(onDeleteHypothesis).toHaveBeenCalledWith('h1');
    expect(result).toEqual({
      navigationPath: ['Hypotheses'],
      preventDefault: true,
    });
  });

  test('let binding edit activates the selected let instead of routing to add-let editor', () => {
    const onEditLetBinding = vi.fn();
    const command = tree.findCommand('e', ['Let Bindings', '0']);
    expect(command?.id).toBe('letbindings-edit');

    const result = command!.execute({
      navigationPath: ['Let Bindings', '0'],
      metadata: {
        [PROOF_WORKSPACE_KEYS.selectedLetBindingId]: 'let-0',
        [PROOF_WORKSPACE_KEYS.selectedLetBindingIndex]: 0,
        [PROOF_WORKSPACE_KEYS.onEditLetBinding]: onEditLetBinding,
      },
    });

    expect(onEditLetBinding).toHaveBeenCalledWith('let-0');
    expect(result).toEqual({
      navigationPath: ['Let Bindings', '0'],
      preventDefault: true,
    });
  });

  test('let binding delete invokes the real delete callback and returns to section root', () => {
    const onDeleteLetBinding = vi.fn();
    const command = tree.findCommand('d', ['Let Bindings', '3']);
    expect(command?.id).toBe('letbindings-delete');

    const result = command!.execute({
      navigationPath: ['Let Bindings', '3'],
      metadata: {
        [PROOF_WORKSPACE_KEYS.selectedLetBindingId]: 'let-3',
        [PROOF_WORKSPACE_KEYS.onDeleteLetBinding]: onDeleteLetBinding,
      },
    });

    expect(onDeleteLetBinding).toHaveBeenCalledWith('let-3');
    expect(result).toEqual({
      navigationPath: ['Let Bindings'],
      preventDefault: true,
    });
  });

  test('hypotheses add is unavailable while a hypothesis is selected', () => {
    const command = tree.findCommand('a', ['Hypotheses']);
    expect(command?.id).toBe('hypotheses-add');

    expect(command!.isAvailable?.({
      navigationPath: ['Hypotheses'],
      metadata: {
        [PROOF_WORKSPACE_KEYS.selectedHypothesisId]: 'h0',
      },
    })).toBe(false);
  });
});
