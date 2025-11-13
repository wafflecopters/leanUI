/**
 * Focusable Section Component
 *
 * A wrapper component that makes a section focusable via keyboard navigation.
 * Provides visual feedback when focused and integrates with the navigation system.
 */

import React, { CSSProperties } from 'react';
import { useFocusableSection } from '../contexts/NavigationContext';

interface FocusableSectionProps {
  /** Unique identifier for this section */
  sectionId: string;

  /** Section content */
  children: React.ReactNode;

  /** Optional custom styles */
  style?: CSSProperties;

  /** Optional class name */
  className?: string;

  /** Label to show when section is focused (optional) */
  label?: string;

  /** Whether to show the focus outline */
  showFocusOutline?: boolean;

  /** Order for arrow key navigation (0 = first) */
  order?: number;
}

export function FocusableSection({
  sectionId,
  children,
  style,
  className,
  label,
  showFocusOutline = true,
  order = 0,
}: FocusableSectionProps) {
  const { ref, isFocused, tabIndex } = useFocusableSection(
    sectionId,
    label || sectionId,
    order
  );

  const focusedStyles: CSSProperties = showFocusOutline && isFocused
    ? {
        outline: '3px solid #2845a7',
        outlineOffset: '2px',
        boxShadow: '0 0 0 4px rgba(40, 69, 167, 0.1)',
      }
    : {};

  return (
    <div
      ref={ref}
      tabIndex={tabIndex}
      className={className}
      style={{
        position: 'relative',
        transition: 'outline 0.2s ease, box-shadow 0.2s ease',
        ...style,
        ...focusedStyles,
      }}
    >
      {/* Optional label badge when focused */}
      {label && isFocused && (
        <div
          style={{
            position: 'absolute',
            top: '-12px',
            left: '12px',
            backgroundColor: '#2845a7',
            color: 'white',
            padding: '2px 8px',
            borderRadius: '4px',
            fontSize: '11px',
            fontWeight: 'bold',
            zIndex: 10,
            boxShadow: '0 2px 4px rgba(0, 0, 0, 0.2)',
          }}
        >
          {label}
        </div>
      )}

      {children}
    </div>
  );
}
