import { describe, expect, test, vi } from 'vitest';
import { buildNamedItemSectionMetadata } from './NamedItemsSection';
import { NAMED_ITEM_KEYS } from '../utils/namedItemCommands';
import { TYPE_EDITING_KEYS } from '../utils/typeEditingCommands';
import { mkTypeTT } from '../compiler/surface';

describe('buildNamedItemSectionMetadata', () => {
  test('populates generic named-item and type-editing metadata for the selected item', () => {
    const onUpdateItem = vi.fn();
    const setTypeFocusPath = vi.fn();
    const item = { id: 'field-0', name: 'field0', type: mkTypeTT(0) };

    const metadata = buildNamedItemSectionMetadata({
      navigationKey: 'Fields',
      onUpdateItem,
      selectedIndex: 0,
      selectedItem: item,
      setTypeFocusPath,
      typeFocusPath: ['body'],
    });

    expect(metadata[NAMED_ITEM_KEYS.selectedItemId]).toBe('field-0');
    expect(metadata[NAMED_ITEM_KEYS.selectedItemIndex]).toBe(0);
    expect(metadata[TYPE_EDITING_KEYS.term]).toBe(item.type);
    expect(metadata[TYPE_EDITING_KEYS.focusPath]).toEqual(['body']);
    expect(metadata[TYPE_EDITING_KEYS.setFocusPath]).toBe(setTypeFocusPath);
    expect(metadata[TYPE_EDITING_KEYS.returnPath]).toEqual(['Fields', '0', 'Type']);

    const setTerm = metadata[TYPE_EDITING_KEYS.setTerm] as ((term: ReturnType<typeof mkTypeTT>) => void);
    const nextType = mkTypeTT(1);
    setTerm(nextType);
    expect(onUpdateItem).toHaveBeenCalledWith('field-0', { ...item, type: nextType });
  });

  test('clears stale named-item and type-editing metadata when selection disappears', () => {
    const metadata = buildNamedItemSectionMetadata({
      navigationKey: 'Fields',
      onUpdateItem: vi.fn(),
      selectedIndex: null,
      selectedItem: null,
      setTypeFocusPath: vi.fn(),
      typeFocusPath: [],
    });

    expect(metadata[NAMED_ITEM_KEYS.selectedItemId]).toBeUndefined();
    expect(metadata[NAMED_ITEM_KEYS.selectedItemIndex]).toBeUndefined();
    expect(metadata[TYPE_EDITING_KEYS.term]).toBeUndefined();
    expect(metadata[TYPE_EDITING_KEYS.focusPath]).toBeUndefined();
    expect(metadata[TYPE_EDITING_KEYS.setTerm]).toBeUndefined();
    expect(metadata[TYPE_EDITING_KEYS.setFocusPath]).toBeUndefined();
    expect(metadata[TYPE_EDITING_KEYS.returnPath]).toBeUndefined();
  });
});
