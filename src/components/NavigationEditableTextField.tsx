/**
 * NavigationEditableTextField
 *
 * A reusable text field component that integrates with the navigation system.
 * Features:
 * - Automatic focus when mounted
 * - Cancel button that pops navigation
 * - Set button that calls update callback
 * - Escape key pops navigation (cancels)
 * - Enter key submits (calls update callback)
 */

import React, { useEffect, useRef, useState } from 'react';
import { useNavigation } from '../contexts/NavigationContext';
import { NavigationUtils } from '../types/commands';

export interface NavigationEditableTextFieldProps {
  /** Label for the field */
  label: string;

  /** Placeholder text */
  placeholder?: string;

  /** Initial value */
  initialValue?: string;

  /** Called when user clicks Set or presses Enter */
  onSet: (value: string) => void;

  /** Called when user clicks Cancel or presses Escape (optional - defaults to nav pop) */
  onCancel?: () => void;

  /** Multi-line textarea if true, single-line input if false */
  multiline?: boolean;

  /** Number of rows for textarea (if multiline) */
  rows?: number;
}

export function NavigationEditableTextField({
  label,
  placeholder,
  initialValue = '',
  onSet,
  onCancel,
  multiline = false,
  rows = 3,
}: NavigationEditableTextFieldProps) {
  const navigation = useNavigation();
  const [value, setValue] = useState(initialValue);
  const inputRef = useRef<HTMLInputElement | HTMLTextAreaElement>(null);

  // Auto-focus on mount
  useEffect(() => {
    inputRef.current?.focus();
  }, []);

  const handleCancel = () => {
    if (onCancel) {
      onCancel();
    } else {
      // Default: pop navigation
      navigation.navigateTo(NavigationUtils.popPath(navigation.state.navigationPath));
    }
  };

  const handleSet = () => {
    onSet(value);
    // Pop navigation after setting
    navigation.navigateTo(NavigationUtils.popPath(navigation.state.navigationPath));
  };

  const handleKeyDown = (e: React.KeyboardEvent) => {
    if (e.key === 'Escape') {
      e.preventDefault();
      e.stopPropagation();
      handleCancel();
    } else if (e.key === 'Enter' && !multiline) {
      e.preventDefault();
      e.stopPropagation();
      handleSet();
    } else if (e.key === 'Enter' && e.metaKey && multiline) {
      // Cmd+Enter to submit in multiline mode
      e.preventDefault();
      e.stopPropagation();
      handleSet();
    }
  };

  const inputProps = {
    ref: inputRef as any,
    value,
    onChange: (e: React.ChangeEvent<HTMLInputElement | HTMLTextAreaElement>) => setValue(e.target.value),
    onKeyDown: handleKeyDown,
    placeholder,
    style: {
      width: '100%',
      padding: '8px',
      fontSize: '14px',
      fontFamily: 'monospace',
      border: '2px solid #007bff',
      borderRadius: '4px',
      outline: 'none',
    },
  };

  return (
    <div
      style={{
        padding: '16px',
        backgroundColor: '#f8f9fa',
        border: '2px solid #007bff',
        borderRadius: '8px',
        marginBottom: '16px',
      }}
    >
      <div style={{ marginBottom: '8px', fontWeight: 'bold', color: '#495057' }}>
        {label}
      </div>

      {multiline ? (
        <textarea {...inputProps} rows={rows} />
      ) : (
        <input {...inputProps} type="text" />
      )}

      <div style={{ marginTop: '8px', display: 'flex', gap: '8px' }}>
        <button
          onClick={handleSet}
          style={{
            padding: '6px 12px',
            backgroundColor: '#28a745',
            color: 'white',
            border: 'none',
            borderRadius: '4px',
            cursor: 'pointer',
            fontWeight: 'bold',
          }}
        >
          Set
        </button>
        <button
          onClick={handleCancel}
          style={{
            padding: '6px 12px',
            backgroundColor: '#dc3545',
            color: 'white',
            border: 'none',
            borderRadius: '4px',
            cursor: 'pointer',
          }}
        >
          Cancel
        </button>
        {multiline && (
          <span style={{ marginLeft: 'auto', fontSize: '12px', color: '#6c757d', alignSelf: 'center' }}>
            Cmd+Enter to submit
          </span>
        )}
      </div>
    </div>
  );
}
