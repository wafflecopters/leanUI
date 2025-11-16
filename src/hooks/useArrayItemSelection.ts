/**
 * Reusable hook for selecting items in a dynamic array via keyboard.
 *
 * Supports:
 * - Single digit (0-9) for immediate selection
 * - Apostrophe (') followed by multiple digits for multi-digit selection
 * - Arrow keys (up/down or left/right) to cycle through items
 *
 * Example usage:
 *   const { selectedIndex, handleKeyDown } = useArrayItemSelection({
 *     arrayLength: hypotheses.length,
 *     isActive: navigationPath[0] === 'Hypotheses',
 *   });
 */

import { useState, useCallback, useEffect } from 'react';

export interface UseArrayItemSelectionOptions {
  /** Current length of the array */
  arrayLength: number;

  /** Whether this selection system is currently active (e.g., section is focused) */
  isActive: boolean;

  /** Optional: Initial selected index */
  initialIndex?: number | null;

  /** Optional: Callback when selection changes */
  onSelectionChange?: (index: number | null) => void;
}

export interface UseArrayItemSelectionResult {
  /** Currently selected index (null if none selected) */
  selectedIndex: number | null;

  /** Set the selected index manually */
  setSelectedIndex: (index: number | null) => void;

  /** Cycle to next item (wraps around) */
  cycleNext: () => void;

  /** Cycle to previous item (wraps around) */
  cyclePrevious: () => void;

  /** Whether in multi-digit input mode (after pressing ') */
  isInMultiDigitMode: boolean;

  /** Current multi-digit buffer (e.g., "25") */
  multiDigitBuffer: string;
}

export function useArrayItemSelection({
  arrayLength,
  isActive,
  initialIndex = null,
  onSelectionChange,
}: UseArrayItemSelectionOptions): UseArrayItemSelectionResult {
  const [selectedIndex, setSelectedIndexInternal] = useState<number | null>(initialIndex);
  const [isInMultiDigitMode, setIsInMultiDigitMode] = useState(false);
  const [multiDigitBuffer, setMultiDigitBuffer] = useState('');

  // Wrapper to call onChange callback
  const setSelectedIndex = useCallback(
    (index: number | null) => {
      setSelectedIndexInternal(index);
      onSelectionChange?.(index);
    },
    [onSelectionChange]
  );

  // Cycle to next item
  const cycleNext = useCallback(() => {
    if (arrayLength === 0) return;

    setSelectedIndexInternal((prev) => {
      const newIndex = prev === null ? 0 : (prev + 1) % arrayLength;
      onSelectionChange?.(newIndex);
      return newIndex;
    });
  }, [arrayLength, onSelectionChange]);

  // Cycle to previous item
  const cyclePrevious = useCallback(() => {
    if (arrayLength === 0) return;

    setSelectedIndexInternal((prev) => {
      const newIndex = prev === null ? arrayLength - 1 : (prev - 1 + arrayLength) % arrayLength;
      onSelectionChange?.(newIndex);
      return newIndex;
    });
  }, [arrayLength, onSelectionChange]);

  // Handle keyboard input
  useEffect(() => {
    if (!isActive) {
      // Clear multi-digit mode and selection when section becomes inactive
      if (isInMultiDigitMode) {
        setIsInMultiDigitMode(false);
        setMultiDigitBuffer('');
      }
      if (selectedIndex !== null) {
        setSelectedIndex(null);
      }
      return;
    }

    const handleKeyDown = (e: KeyboardEvent) => {
      // Don't handle if user is typing in an input
      const target = e.target as HTMLElement;
      if (target.tagName === 'INPUT' || target.tagName === 'TEXTAREA') {
        return;
      }

      // Arrow keys - cycle through items
      if (e.key === 'ArrowDown' || e.key === 'ArrowRight') {
        cycleNext();
        e.preventDefault();
        return;
      }

      if (e.key === 'ArrowUp' || e.key === 'ArrowLeft') {
        cyclePrevious();
        e.preventDefault();
        return;
      }

      // Apostrophe - enter multi-digit mode
      if (e.key === "'" || e.key === 'Quote') {
        setIsInMultiDigitMode(true);
        setMultiDigitBuffer('');
        e.preventDefault();
        return;
      }

      // Escape - exit multi-digit mode
      if (e.key === 'Escape' && isInMultiDigitMode) {
        setIsInMultiDigitMode(false);
        setMultiDigitBuffer('');
        e.preventDefault();
        return;
      }

      // Digit keys
      if (/^[0-9]$/.test(e.key)) {
        const digit = e.key;

        if (isInMultiDigitMode) {
          // Multi-digit mode: accumulate digits
          const newBuffer = multiDigitBuffer + digit;
          setMultiDigitBuffer(newBuffer);

          // Try to select the item
          const index = parseInt(newBuffer, 10);
          if (index >= 0 && index < arrayLength) {
            setSelectedIndex(index);
          }
          // Note: Don't exit multi-digit mode automatically
          // User can press Escape or another command key to exit
        } else {
          // Single digit mode: immediate selection
          const index = parseInt(digit, 10);
          if (index >= 0 && index < arrayLength) {
            setSelectedIndex(index);
          }
        }

        e.preventDefault();
        return;
      }
    };

    window.addEventListener('keydown', handleKeyDown);
    return () => window.removeEventListener('keydown', handleKeyDown);
  }, [
    isActive,
    arrayLength,
    isInMultiDigitMode,
    multiDigitBuffer,
    cycleNext,
    cyclePrevious,
    setSelectedIndex,
  ]);

  // Clear selection if it's out of bounds (array shrunk)
  useEffect(() => {
    if (selectedIndex !== null && selectedIndex >= arrayLength) {
      setSelectedIndex(null);
    }
  }, [selectedIndex, arrayLength, setSelectedIndex]);

  return {
    selectedIndex,
    setSelectedIndex,
    cycleNext,
    cyclePrevious,
    isInMultiDigitMode,
    multiDigitBuffer,
  };
}
