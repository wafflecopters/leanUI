/**
 * List Navigation System
 *
 * Provides generic keyboard navigation for lists of items.
 * Supports:
 * - Numeric selection: 0-9 for single digit, 'N for multi-digit
 * - Arrow key navigation: Up/Down to move through items
 * - Focus-specific commands: Commands available when an item is focused
 */

/**
 * Represents an item in a navigable list
 */
export interface ListItem<T = any> {
  /** Unique identifier for this item */
  id: string;

  /** Display data for the item */
  data: T;

  /** Index in the list (for numeric selection) */
  index: number;
}

/**
 * State for a navigable list
 */
export interface ListNavigationState {
  /** ID of the currently focused item, or null if none */
  focusedItemId: string | null;

  /** Buffer for multi-digit numeric input (e.g., after pressing ') */
  numericBuffer: string;

  /** Whether we're in apostrophe mode for multi-digit selection */
  isApostropheMode: boolean;
}

/**
 * Controller for managing list navigation
 */
export interface ListController<T = any> {
  /** All items in the list */
  items: ListItem<T>[];

  /** Current navigation state */
  state: ListNavigationState;

  /** Focus an item by ID */
  focusItem: (id: string | null) => void;

  /** Focus an item by index */
  focusItemByIndex: (index: number) => void;

  /** Move focus to next item (wrapping) */
  focusNext: () => void;

  /** Move focus to previous item (wrapping) */
  focusPrevious: () => void;

  /** Handle numeric input for selection */
  handleNumericInput: (digit: string) => boolean;

  /** Start apostrophe mode for multi-digit selection */
  startApostropheMode: () => void;

  /** Cancel apostrophe mode */
  cancelApostropheMode: () => void;

  /** Get currently focused item */
  getFocusedItem: () => ListItem<T> | null;
}

/**
 * Create a list controller for managing navigation
 */
export function createListController<T = any>(
  items: ListItem<T>[],
  initialFocusedId: string | null = null
): ListController<T> {
  let state: ListNavigationState = {
    focusedItemId: initialFocusedId,
    numericBuffer: '',
    isApostropheMode: false,
  };

  const controller: ListController<T> = {
    items,
    state,

    focusItem: (id: string | null) => {
      state.focusedItemId = id;
      state.numericBuffer = '';
      state.isApostropheMode = false;
    },

    focusItemByIndex: (index: number) => {
      if (index >= 0 && index < items.length) {
        controller.focusItem(items[index].id);
      }
    },

    focusNext: () => {
      if (items.length === 0) return;

      const currentIndex = state.focusedItemId
        ? items.findIndex(item => item.id === state.focusedItemId)
        : -1;

      const nextIndex = (currentIndex + 1) % items.length;
      controller.focusItemByIndex(nextIndex);
    },

    focusPrevious: () => {
      if (items.length === 0) return;

      const currentIndex = state.focusedItemId
        ? items.findIndex(item => item.id === state.focusedItemId)
        : -1;

      const prevIndex = (currentIndex - 1 + items.length) % items.length;
      controller.focusItemByIndex(prevIndex);
    },

    handleNumericInput: (digit: string) => {
      if (!/^\d$/.test(digit)) return false;

      if (state.isApostropheMode) {
        // Multi-digit mode: accumulate digits
        state.numericBuffer += digit;

        // Try to parse and focus
        const index = parseInt(state.numericBuffer, 10);
        if (index < items.length) {
          controller.focusItemByIndex(index);
          return true;
        }
        // Keep accumulating if index is still valid as we type more digits
        return false;
      } else {
        // Single digit mode: immediate focus
        const index = parseInt(digit, 10);
        if (index < items.length) {
          controller.focusItemByIndex(index);
          return true;
        }
        return false;
      }
    },

    startApostropheMode: () => {
      state.isApostropheMode = true;
      state.numericBuffer = '';
    },

    cancelApostropheMode: () => {
      state.isApostropheMode = false;
      state.numericBuffer = '';
    },

    getFocusedItem: () => {
      if (!state.focusedItemId) return null;
      return items.find(item => item.id === state.focusedItemId) || null;
    },
  };

  return controller;
}
