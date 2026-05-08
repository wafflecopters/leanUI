import { Command, CommandContext, createCommand } from '../types/commands';
import { createTypeEditingCommands as createSharedTypeEditingCommands } from './typeEditingCommands';

interface NamedItemCommandConfig {
  itemKind: string;
  sectionName: string;
}

export const NAMED_ITEM_KEYS = {
  selectedItemId: 'namedItem.selectedItemId',
  selectedItemIndex: 'namedItem.selectedItemIndex',
  onAddItem: 'namedItem.onAddItem',
  onDeleteItem: 'namedItem.onDeleteItem',
} as const;

interface NamedItemCommandContext {
  selectedItemId?: string;
  selectedItemIndex?: number;
  onAddItem?: () => void;
  onDeleteItem?: (id: string) => void;
}

function getNamedItemCommandContext(context: CommandContext): NamedItemCommandContext {
  return {
    selectedItemId: context.metadata?.[NAMED_ITEM_KEYS.selectedItemId] as string | undefined,
    selectedItemIndex: context.metadata?.[NAMED_ITEM_KEYS.selectedItemIndex] as number | undefined,
    onAddItem: context.metadata?.[NAMED_ITEM_KEYS.onAddItem] as (() => void) | undefined,
    onDeleteItem: context.metadata?.[NAMED_ITEM_KEYS.onDeleteItem] as ((id: string) => void) | undefined,
  };
}

function getSelectedItemIndex(context: CommandContext): number | undefined {
  return getNamedItemCommandContext(context).selectedItemIndex;
}

function hasSelectedItem(context: CommandContext): boolean {
  return getSelectedItemIndex(context) !== undefined;
}

export function createNamedItemCommands(config: NamedItemCommandConfig): Command[] {
  const { itemKind, sectionName } = config;

  return [
    createCommand(
      `add-${itemKind}`,
      'a',
      'Add',
      (context) => {
        getNamedItemCommandContext(context).onAddItem?.();
        return { preventDefault: true };
      },
      {
        description: `Add a new ${itemKind}`,
      }
    ),

    createCommand(
      `edit-${itemKind}-name`,
      'n',
      'Name',
      (context) => {
        const selectedIndex = getSelectedItemIndex(context);
        if (selectedIndex === undefined) return { preventDefault: true };

        return {
          navigationPath: [sectionName, String(selectedIndex), 'EditName'],
          preventDefault: true,
        };
      },
      {
        description: `Edit ${itemKind} name`,
        isAvailable: hasSelectedItem,
      }
    ),

    createCommand(
      `edit-${itemKind}-type`,
      't',
      'Type',
      (context) => {
        const selectedIndex = getSelectedItemIndex(context);
        if (selectedIndex === undefined) return { preventDefault: true };

        return {
          navigationPath: [sectionName, String(selectedIndex), 'Type'],
          preventDefault: true,
        };
      },
      {
        description: `Edit ${itemKind} type`,
        isAvailable: hasSelectedItem,
        children: createSharedTypeEditingCommands(),
      }
    ),

    createCommand(
      `delete-${itemKind}`,
      'd',
      'Delete',
      (context) => {
        const { selectedItemId: selectedId, onDeleteItem } = getNamedItemCommandContext(context);
        if (selectedId && onDeleteItem) {
          onDeleteItem(selectedId);
        }
        return {
          navigationPath: [sectionName],
          preventDefault: true,
        };
      },
      {
        description: `Delete selected ${itemKind}`,
        isAvailable: hasSelectedItem,
      }
    ),
  ];
}
