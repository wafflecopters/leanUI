/**
 * Hook for managing keyboard-navigable lists
 *
 * Provides:
 * - Numeric selection (0-9, 'N for multi-digit)
 * - Arrow key navigation (j/k or up/down)
 * - Focus management
 * - Integration with command system
 */

import { useState, useEffect, useCallback, useRef } from 'react';
import { useNavigation } from '../contexts/NavigationContext';
import { Command } from '../types/commands';

export interface NavigableListItem<T = any> {
  id: string;
  data: T;
}

export interface NavigableListOptions<T> {
  /** Items in the list */
  items: NavigableListItem<T>[];

  /** Navigation context (section name) where this list is active */
  context: string;

  /** Generate commands for a focused item */
  createItemCommands?: (item: NavigableListItem<T>, index: number) => Command[];

  /** Callback when an item is focused */
  onItemFocused?: (item: NavigableListItem<T> | null, index: number | null) => void;
}

export interface NavigableListState {
  /** Index of focused item (null if none) */
  focusedIndex: number | null;

  /** Numeric input buffer for apostrophe mode */
  numericBuffer: string;

  /** Whether in apostrophe mode (multi-digit selection) */
  isApostropheMode: boolean;

  /** Focus an item by index */
  focusIndex: (index: number | null) => void;

  /** Focus next item (with wrapping) */
  focusNext: () => void;

  /** Focus previous item (with wrapping) */
  focusPrevious: () => void;
}

export function useNavigableList<T>({
  items,
  context,
  createItemCommands,
  onItemFocused,
}: NavigableListOptions<T>): NavigableListState {
  const navigation = useNavigation();
  const [focusedIndex, setFocusedIndex] = useState<number | null>(null);
  const [numericBuffer, setNumericBuffer] = useState('');
  const [isApostropheMode, setIsApostropheMode] = useState(false);

  // Use ref to store createItemCommands to avoid recreating effect
  const createItemCommandsRef = useRef(createItemCommands);
  createItemCommandsRef.current = createItemCommands;

  const focusIndex = useCallback((index: number | null) => {
    if (index !== null && (index < 0 || index >= items.length)) {
      return; // Invalid index
    }

    setFocusedIndex(index);
    setNumericBuffer('');
    setIsApostropheMode(false);

    const item = index !== null ? items[index] : null;
    onItemFocused?.(item, index);
  }, [items, onItemFocused]);

  const focusNext = useCallback(() => {
    if (items.length === 0) return;

    if (focusedIndex === null) {
      focusIndex(0);
    } else {
      focusIndex((focusedIndex + 1) % items.length);
    }
  }, [items.length, focusedIndex, focusIndex]);

  const focusPrevious = useCallback(() => {
    if (items.length === 0) return;

    if (focusedIndex === null) {
      focusIndex(items.length - 1);
    } else {
      focusIndex((focusedIndex - 1 + items.length) % items.length);
    }
  }, [items.length, focusedIndex, focusIndex]);

  // Update metadata when focused item changes
  useEffect(() => {
    if (focusedIndex === null) return;

    const focusedItem = items[focusedIndex];
    if (!focusedItem) return;

    // Generate commands for this item
    const itemCommands = createItemCommandsRef.current?.(focusedItem, focusedIndex) || [];

    navigation.updateMetadata({
      focusedItemId: focusedItem.id,
      focusedItemIndex: focusedIndex,
      itemCommands,
    });
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [focusedIndex, items.length]);

  // Handle keyboard input
  useEffect(() => {
    const handleKeyDown = (e: KeyboardEvent) => {
      // Only handle if we're in the correct context
      if (!navigation.state.navigationPath.includes(context)) return;
      if (navigation.state.mode !== 'navigate') return;

      const target = e.target as HTMLElement;
      const isInInput = target.tagName === 'INPUT' || target.tagName === 'TEXTAREA';
      if (isInInput) return;

      // Apostrophe - start multi-digit mode
      if (e.key === "'") {
        setIsApostropheMode(true);
        setNumericBuffer('');
        e.preventDefault();
        return;
      }

      // Escape in apostrophe mode - cancel
      if (e.key === 'Escape' && isApostropheMode) {
        setIsApostropheMode(false);
        setNumericBuffer('');
        e.preventDefault();
        return;
      }

      // Numeric input (0-9)
      if (/^\d$/.test(e.key)) {
        if (isApostropheMode) {
          // Multi-digit mode: accumulate digits
          const newBuffer = numericBuffer + e.key;
          setNumericBuffer(newBuffer);
          const index = parseInt(newBuffer, 10);
          if (index < items.length) {
            focusIndex(index);
          }
        } else {
          // Single digit mode: immediate focus
          const index = parseInt(e.key, 10);
          if (index < items.length) {
            focusIndex(index);
          }
        }
        e.preventDefault();
        return;
      }

      // Arrow key / vim-style navigation
      if (e.key === 'ArrowDown' || e.key === 'j') {
        focusNext();
        e.preventDefault();
        return;
      }

      if (e.key === 'ArrowUp' || e.key === 'k') {
        focusPrevious();
        e.preventDefault();
        return;
      }
    };

    window.addEventListener('keydown', handleKeyDown);
    return () => window.removeEventListener('keydown', handleKeyDown);
  }, [
    context,
    items.length,
    focusedIndex,
    isApostropheMode,
    numericBuffer,
    navigation.state.navigationPath,
    navigation.state.mode,
    focusIndex,
    focusNext,
    focusPrevious,
  ]);

  return {
    focusedIndex,
    numericBuffer,
    isApostropheMode,
    focusIndex,
    focusNext,
    focusPrevious,
  };
}
