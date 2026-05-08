import { describe, expect, test, vi } from 'vitest';
import { createNamedItemCommands, NAMED_ITEM_KEYS } from './namedItemCommands';

describe('createNamedItemCommands', () => {
  const commands = createNamedItemCommands({
    itemKind: 'field',
    sectionName: 'Fields',
  });

  test('navigates to selected item name editor', () => {
    const editName = commands.find(command => command.id === 'edit-field-name');
    expect(editName).toBeDefined();

    const result = editName!.execute({
      navigationPath: ['Fields'],
      metadata: { [NAMED_ITEM_KEYS.selectedItemIndex]: 2 },
    });

    expect(result).toEqual({
      navigationPath: ['Fields', '2', 'EditName'],
      preventDefault: true,
    });
  });

  test('deletes selected item through generic metadata hooks', () => {
    const onDeleteItem = vi.fn();
    const deleteCommand = commands.find(command => command.id === 'delete-field');
    expect(deleteCommand).toBeDefined();

    const result = deleteCommand!.execute({
      navigationPath: ['Fields', '1'],
      metadata: {
        [NAMED_ITEM_KEYS.selectedItemId]: 'field-1',
        [NAMED_ITEM_KEYS.selectedItemIndex]: 1,
        [NAMED_ITEM_KEYS.onDeleteItem]: onDeleteItem,
      },
    });

    expect(onDeleteItem).toHaveBeenCalledWith('field-1');
    expect(result).toEqual({
      navigationPath: ['Fields'],
      preventDefault: true,
    });
  });

  test('type edit command exposes shared type-editing children', () => {
    const editType = commands.find(command => command.id === 'edit-field-type');
    expect(editType?.children?.length).toBeGreaterThan(0);
    expect(editType?.children?.some(child => child.label === 'Wrap')).toBe(true);
  });

  test('runs add through generic metadata hook', () => {
    const onAddItem = vi.fn();
    const addCommand = commands.find(command => command.id === 'add-field');
    expect(addCommand).toBeDefined();

    const result = addCommand!.execute({
      navigationPath: ['Fields'],
      metadata: {
        [NAMED_ITEM_KEYS.onAddItem]: onAddItem,
      },
    });

    expect(onAddItem).toHaveBeenCalledTimes(1);
    expect(result).toEqual({ preventDefault: true });
  });

  test('edit and delete commands become unavailable once selection metadata is cleared', () => {
    const editName = commands.find(command => command.id === 'edit-field-name');
    const deleteCommand = commands.find(command => command.id === 'delete-field');
    expect(editName).toBeDefined();
    expect(deleteCommand).toBeDefined();

    const clearedSelection = {
      navigationPath: ['Fields'],
      metadata: {
        [NAMED_ITEM_KEYS.selectedItemId]: undefined,
        [NAMED_ITEM_KEYS.selectedItemIndex]: undefined,
      },
    };

    expect(editName!.isAvailable?.(clearedSelection)).toBe(false);
    expect(deleteCommand!.isAvailable?.(clearedSelection)).toBe(false);
  });
});
