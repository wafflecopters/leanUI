/**
 * Generic Navigable List Component
 *
 * A reusable list component with keyboard navigation:
 * - Displays items with index numbers
 * - Visual focus indication
 * - Apostrophe mode indicator
 * - Integrates with useNavigableList hook
 */

import React, { ReactNode } from 'react';
import { NavigableListState } from '../hooks/useNavigableList';

export interface NavigableListProps<T> {
  /** Items to display */
  items: { id: string; data: T }[];

  /** List navigation state from useNavigableList hook */
  listState: NavigableListState;

  /** Render function for each item */
  renderItem: (item: T, index: number, isFocused: boolean) => ReactNode;

  /** Optional container style */
  style?: React.CSSProperties;

  /** Optional class name */
  className?: string;
}

export function NavigableList<T>({
  items,
  listState,
  renderItem,
  style,
  className,
}: NavigableListProps<T>) {
  const { focusedIndex, isApostropheMode, numericBuffer, focusIndex } = listState;

  return (
    <div style={{ position: 'relative', ...style }} className={className}>
      {items.map((item, index) => {
        const isFocused = focusedIndex === index;

        return (
          <div
            key={item.id}
            style={{
              display: 'flex',
              alignItems: 'center',
              padding: '8px',
              marginBottom: '4px',
              backgroundColor: isFocused ? '#e3f2fd' : 'transparent',
              border: isFocused ? '2px solid #2196f3' : '2px solid transparent',
              borderRadius: '4px',
              cursor: 'pointer',
              transition: 'all 0.15s ease',
            }}
            onClick={() => focusIndex(index)}
          >
            {/* Index number */}
            <span
              style={{
                minWidth: '24px',
                marginRight: '8px',
                fontSize: '12px',
                color: isFocused ? '#1976d2' : '#999',
                fontFamily: 'monospace',
              }}
            >
              {index}
            </span>

            {/* Item content */}
            <div style={{ flex: 1 }}>
              {renderItem(item.data, index, isFocused)}
            </div>
          </div>
        );
      })}

      {/* Apostrophe mode indicator */}
      {isApostropheMode && (
        <div
          style={{
            position: 'absolute',
            bottom: '-36px',
            left: '0',
            padding: '6px 12px',
            backgroundColor: '#fff3cd',
            border: '1px solid #ffc107',
            borderRadius: '4px',
            fontSize: '13px',
            fontFamily: 'monospace',
            fontWeight: 'bold',
            boxShadow: '0 2px 4px rgba(0, 0, 0, 0.1)',
          }}
        >
          Select: '{numericBuffer}_
        </div>
      )}

      {/* Empty state */}
      {items.length === 0 && (
        <div
          style={{
            padding: '20px',
            textAlign: 'center',
            color: '#999',
            fontStyle: 'italic',
          }}
        >
          No items
        </div>
      )}
    </div>
  );
}
