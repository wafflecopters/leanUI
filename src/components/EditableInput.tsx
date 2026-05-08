/**
 * Reusable editable input component for inline editing.
 * Shared inline text input for editor widgets that need lightweight rename/edit affordances.
 */

import { useState } from 'react';

interface EditableInputProps {
  initialValue: string;
  onSave: (value: string) => void;
  onCancel: () => void;
  style?: React.CSSProperties;
  placeholder?: string;
}

export function EditableInput({
  initialValue,
  onSave,
  onCancel,
  style,
  placeholder,
}: EditableInputProps) {
  const [value, setValue] = useState(initialValue);

  return (
    <input
      autoFocus
      type="text"
      value={value}
      onChange={(e) => setValue(e.target.value)}
      placeholder={placeholder}
      onKeyDown={(e) => {
        if (e.key === 'Enter') {
          onSave(value);
          e.preventDefault();
        } else if (e.key === 'Escape') {
          onCancel();
          e.preventDefault();
        }
      }}
      style={{
        fontFamily: 'monospace',
        fontSize: '14px',
        padding: '2px 4px',
        border: '1px solid #2845a7',
        borderRadius: '2px',
        ...style,
      }}
    />
  );
}
