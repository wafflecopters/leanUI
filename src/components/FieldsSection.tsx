/**
 * Fields Section for Record Editor
 *
 * Uses the shared NamedItemsSection component to manage a list of record fields
 * with keyboard navigation, selection, and inline editing.
 */

import { NamedItemsSection, NamedTypedItem, generateItemId } from './NamedItemsSection';
import { TTerm, mkType, mkHole } from '../types/tt-core';

// ============================================================================
// Types
// ============================================================================

export interface Field extends NamedTypedItem {
  id: string;
  name: string;
  type: TTerm;
}

// ============================================================================
// Props
// ============================================================================

interface FieldsSectionProps {
  fields: Field[];
  onUpdateField: (id: string, updated: Field) => void;
  onAddField: () => void;
  onDeleteField: (id: string) => void;
}

// ============================================================================
// Component
// ============================================================================

export function FieldsSection({
  fields,
  onUpdateField,
  // Note: onAddField and onDeleteField are passed via navigation metadata
  // eslint-disable-next-line @typescript-eslint/no-unused-vars
  onAddField: _onAddField,
  // eslint-disable-next-line @typescript-eslint/no-unused-vars
  onDeleteField: _onDeleteField,
}: FieldsSectionProps) {
  return (
    <NamedItemsSection<Field>
      items={fields}
      onUpdateItem={onUpdateField}
      config={{
        navigationKey: 'Fields',
        itemPrefix: '•',
        emptyPlaceholder: '(no fields)',
        nameColor: '#2e7d32',  // Green for fields
        showIndices: true,
      }}
    />
  );
}

// ============================================================================
// Helpers
// ============================================================================

/**
 * Generate a unique ID for a new field
 */
export function generateFieldId(): string {
  return generateItemId('field');
}

/**
 * Create a new field with a default type (hole)
 */
export function createDefaultField(baseName: string): Field {
  return {
    id: generateFieldId(),
    name: baseName,
    type: mkHole(`type_${baseName}`, mkType(0), []),
  };
}

