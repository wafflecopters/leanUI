/**
 * Constructors Section for Inductive Type Editor
 *
 * Uses the shared NamedItemsSection component to manage a list of constructors
 * with keyboard navigation, selection, and inline editing.
 */

import { NamedItemsSection, NamedTypedItem, generateItemId } from './NamedItemsSection';
import { TTerm } from '../types/tt-core';
import { createDefaultConstructorType } from '../utils/inductiveTypeUtils';

// ============================================================================
// Types
// ============================================================================

export interface Constructor extends NamedTypedItem {
  id: string;
  name: string;
  type: TTerm;
}

// ============================================================================
// Props
// ============================================================================

interface ConstructorsSectionProps {
  constructors: Constructor[];
  onUpdateConstructor: (id: string, updated: Constructor) => void;
  onAddConstructor: () => void;
  onDeleteConstructor: (id: string) => void;
}

// ============================================================================
// Component
// ============================================================================

export function ConstructorsSection({
  constructors,
  onUpdateConstructor,
  // Note: onAddConstructor and onDeleteConstructor are passed via navigation metadata
  // eslint-disable-next-line @typescript-eslint/no-unused-vars
  onAddConstructor: _onAddConstructor,
  // eslint-disable-next-line @typescript-eslint/no-unused-vars
  onDeleteConstructor: _onDeleteConstructor,
}: ConstructorsSectionProps) {
  return (
    <NamedItemsSection<Constructor>
      items={constructors}
      onUpdateItem={onUpdateConstructor}
      config={{
        navigationKey: 'Constructors',
        itemPrefix: '|',
        emptyPlaceholder: '-',
        nameColor: '#0066cc',
        showIndices: true,
      }}
    />
  );
}

// ============================================================================
// Helpers
// ============================================================================

/**
 * Generate a unique ID for a new constructor
 */
export function generateConstructorId(): string {
  return generateItemId('ctor');
}

/**
 * Create a new constructor with the appropriate default type.
 *
 * The constructor type defaults to the inductive type applied to holes for each argument.
 * E.g., for "Vec : Nat -> Type -> Type", creates "ctor : Vec ?hole_0 ?hole_1"
 */
export function createConstructorForInductive(
  baseName: string,
  inductiveName: string,
  inductiveType: TTerm
): Constructor {
  return {
    id: generateConstructorId(),
    name: baseName,
    type: createDefaultConstructorType(inductiveName, inductiveType),
  };
}
