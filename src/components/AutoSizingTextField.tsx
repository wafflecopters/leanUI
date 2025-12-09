/**
 * AutoSizingTextField
 *
 * A text input that automatically adjusts its width to fit the content.
 * Used for inline editing of names, identifiers, etc.
 */

import { useState, useRef, useEffect, useCallback } from 'react';

interface AutoSizingTextFieldProps {
  value: string;
  onChange: (value: string) => void;
  onSubmit?: () => void;
  onCancel?: () => void;
  minWidth?: string;
  placeholder?: string;
  autoFocus?: boolean;
  style?: React.CSSProperties;
  className?: string;
}

export function AutoSizingTextField({
  value,
  onChange,
  onSubmit,
  onCancel,
  minWidth = '3em',
  placeholder = '',
  autoFocus = true,
  style,
  className,
}: AutoSizingTextFieldProps) {
  const inputRef = useRef<HTMLInputElement>(null);
  const measureRef = useRef<HTMLSpanElement>(null);
  const [width, setWidth] = useState<string>(minWidth);

  // Measure the text width and update input width
  const updateWidth = useCallback(() => {
    if (measureRef.current) {
      const textWidth = measureRef.current.offsetWidth;
      // Add a small buffer for cursor and padding
      const newWidth = Math.max(textWidth + 4, parseMinWidth(minWidth));
      setWidth(`${newWidth}px`);
    }
  }, [minWidth]);

  // Update width when value changes
  useEffect(() => {
    updateWidth();
  }, [value, updateWidth]);

  // Auto-focus on mount
  useEffect(() => {
    if (autoFocus && inputRef.current) {
      inputRef.current.focus();
      inputRef.current.select();
    }
  }, [autoFocus]);

  const handleKeyDown = (e: React.KeyboardEvent) => {
    if (e.key === 'Enter') {
      e.preventDefault();
      onSubmit?.();
    } else if (e.key === 'Escape') {
      e.preventDefault();
      onCancel?.();
    }
    // Stop propagation to prevent navigation system from handling these keys
    e.stopPropagation();
  };

  return (
    <span style={{ position: 'relative', display: 'inline-block' }}>
      {/* Hidden span for measuring text width */}
      <span
        ref={measureRef}
        style={{
          position: 'absolute',
          visibility: 'hidden',
          whiteSpace: 'pre',
          font: 'inherit',
          ...style,
        }}
      >
        {value || placeholder || ' '}
      </span>

      {/* Actual input */}
      <input
        ref={inputRef}
        type="text"
        value={value}
        onChange={(e) => onChange(e.target.value)}
        onKeyDown={handleKeyDown}
        placeholder={placeholder}
        className={className}
        style={{
          width,
          minWidth,
          font: 'inherit',
          border: '1px solid #007acc',
          borderRadius: '2px',
          padding: '0 2px',
          margin: 0,
          backgroundColor: 'rgba(0, 122, 204, 0.1)',
          outline: 'none',
          boxSizing: 'content-box',
          ...style,
        }}
      />
    </span>
  );
}

/**
 * Parse a CSS minWidth value to pixels (rough approximation).
 * Supports 'em' and 'px' units.
 */
function parseMinWidth(minWidth: string): number {
  if (minWidth.endsWith('em')) {
    const em = parseFloat(minWidth);
    // Approximate 1em as 14px (monospace font)
    return em * 14;
  } else if (minWidth.endsWith('px')) {
    return parseFloat(minWidth);
  }
  return 42; // Default ~3em
}
