/**
 * Constructors Section for Inductive Type Editor
 *
 * Similar pattern to HypothesesSection - manages a list of constructors
 * with keyboard navigation, selection, and inline editing.
 */

import { useEffect, useState, useRef } from 'react';
import { useNavigation } from '../contexts/NavigationContext';
import { EditableInput } from './EditableInput';
import { TTermRenderer } from './TTermRenderer';
import { TTerm } from '../types/tt-core';
import { TermFocusPath } from '../utils/termNavigation';
import { createDefaultConstructorType } from '../utils/inductiveTypeUtils';

export interface Constructor {
  id: string;
  name: string;
  type: TTerm;
}

interface ConstructorsSectionProps {
  constructors: Constructor[];
  onUpdateConstructor: (id: string, updated: Constructor) => void;
  onAddConstructor: () => void;
  onDeleteConstructor: (id: string) => void;
}

export function ConstructorsSection({
  constructors,
  onUpdateConstructor,
  // Note: onAddConstructor and onDeleteConstructor are passed via navigation metadata
  // eslint-disable-next-line @typescript-eslint/no-unused-vars
  onAddConstructor: _onAddConstructor,
  // eslint-disable-next-line @typescript-eslint/no-unused-vars
  onDeleteConstructor: _onDeleteConstructor,
}: ConstructorsSectionProps) {
  const navigation = useNavigation();

  // Use ref to avoid dependency on onUpdateConstructor changing
  const onUpdateConstructorRef = useRef(onUpdateConstructor);
  onUpdateConstructorRef.current = onUpdateConstructor;

  // Derive state from navigation path
  const navPath = navigation.state.navigationPath;
  const isInFocusChain = navPath[0] === 'Constructors';
  const isActive = navPath.length === 1 && navPath[0] === 'Constructors';

  // Parse selected index: ['Constructors', '0'] or ['Constructors', '0', 'EditName']
  const selectedIndex = navPath.length >= 2 && navPath[0] === 'Constructors' && /^\d+$/.test(navPath[1])
    ? parseInt(navPath[1], 10)
    : null;

  // Derive edit mode
  const isEditingName = navPath[2] === 'EditName';
  const isEditingType = navPath[2] === 'Type';

  // Local state for type focus path (when editing a constructor's type)
  const [typeFocusPath, setTypeFocusPath] = useState<TermFocusPath>([]);

  // Get selected constructor
  const selectedConstructor = selectedIndex !== null && selectedIndex < constructors.length
    ? constructors[selectedIndex]
    : null;

  // Sync metadata
  useEffect(() => {
    if (selectedConstructor && selectedIndex !== null) {
      navigation.updateMetadata({
        selectedConstructorId: selectedConstructor.id,
        selectedConstructorIndex: selectedIndex,
        constructorTypeFocusPath: typeFocusPath,
        setConstructorTypeFocusPath: setTypeFocusPath,
        selectedConstructorType: selectedConstructor.type,
        setSelectedConstructorType: (newType: TTerm) => {
          onUpdateConstructorRef.current(selectedConstructor.id, { ...selectedConstructor, type: newType });
        },
      });
    }
  }, [selectedConstructor, selectedIndex, typeFocusPath, navigation]);

  // Keyboard handling for selection
  useEffect(() => {
    if (!isActive) return;

    const handleKeyDown = (e: KeyboardEvent) => {
      const target = e.target as HTMLElement;
      if (target.tagName === 'INPUT' || target.tagName === 'TEXTAREA') {
        return;
      }

      // Arrow keys for cycling
      if (e.key === 'ArrowDown' || e.key === 'ArrowRight') {
        if (constructors.length === 0) return;
        const newIndex = selectedIndex === null ? 0 : (selectedIndex + 1) % constructors.length;
        navigation.navigateTo(['Constructors', String(newIndex)]);
        e.preventDefault();
        return;
      }

      if (e.key === 'ArrowUp' || e.key === 'ArrowLeft') {
        if (constructors.length === 0) return;
        const newIndex = selectedIndex === null
          ? constructors.length - 1
          : (selectedIndex - 1 + constructors.length) % constructors.length;
        navigation.navigateTo(['Constructors', String(newIndex)]);
        e.preventDefault();
        return;
      }

      // Digit keys for direct selection
      if (/^[0-9]$/.test(e.key)) {
        const index = parseInt(e.key, 10);
        if (index >= 0 && index < constructors.length) {
          navigation.navigateTo(['Constructors', String(index)]);
        }
        e.preventDefault();
        return;
      }
    };

    window.addEventListener('keydown', handleKeyDown);
    return () => window.removeEventListener('keydown', handleKeyDown);
  }, [isActive, selectedIndex, constructors, navigation]);

  // Handle save name
  const handleSaveName = (value: string) => {
    if (!selectedConstructor) return;
    onUpdateConstructor(selectedConstructor.id, {
      ...selectedConstructor,
      name: value,
    });
    navigation.navigateTo(['Constructors', String(selectedIndex)]);
  };

  // Handle cancel
  const handleCancel = () => {
    navigation.navigateTo(['Constructors', String(selectedIndex)]);
  };

  return (
    <div style={{
      border: isInFocusChain ? '2px solid #007acc' : '2px solid transparent',
      borderRadius: '8px',
      padding: '12px',
      backgroundColor: isInFocusChain ? '#f8fbff' : 'transparent',
      transition: 'all 0.15s ease',
    }}>
      {constructors.length === 0 ? (
        <div style={{
          color: '#999',
          fontStyle: 'italic',
          paddingLeft: '20px',
          fontFamily: 'monospace',
          fontSize: '14px'
        }}>
          -
        </div>
      ) : (
        <div style={{ paddingLeft: '8px' }}>
          {constructors.map((ctor, index) => {
            const isSelected = selectedIndex === index;
            const isEditingNameForThis = isSelected && isEditingName;
            const isEditingTypeForThis = isSelected && isEditingType;

            return (
              <div
                key={ctor.id}
                style={{
                  padding: '4px 8px',
                  display: 'flex',
                  alignItems: 'center',
                  gap: '8px',
                  backgroundColor: isSelected ? '#e6f3ff' : 'transparent',
                  border: isSelected ? '2px solid #2845a7' : '2px solid transparent',
                  borderRadius: '4px',
                  fontFamily: 'monospace',
                  fontSize: '14px',
                  marginBottom: '4px',
                }}
              >
                {/* Pipe prefix */}
                <span style={{ color: '#666' }}>|</span>

                {/* Index (when in focus chain) */}
                {isInFocusChain && (
                  <span style={{
                    fontSize: '12px',
                    color: isSelected ? '#2845a7' : '#999',
                    minWidth: '16px',
                    fontWeight: isSelected ? 'bold' : 'normal',
                  }}>
                    {index}
                  </span>
                )}

                {/* Name */}
                {isEditingNameForThis ? (
                  <EditableInput
                    initialValue={ctor.name}
                    onSave={handleSaveName}
                    onCancel={handleCancel}
                    style={{ minWidth: '100px' }}
                  />
                ) : (
                  <span style={{
                    color: '#0066cc',
                    fontWeight: isSelected ? 'bold' : 'normal',
                  }}>
                    {ctor.name}
                  </span>
                )}

                {/* Colon */}
                <span style={{ color: '#666' }}>:</span>

                {/* Type */}
                <div style={{
                  border: isEditingTypeForThis ? '2px solid #007acc' : '1px solid transparent',
                  borderRadius: '4px',
                  padding: '2px 4px',
                  backgroundColor: isEditingTypeForThis ? '#f0f8ff' : 'transparent'
                }}>
                  <TTermRenderer
                    term={ctor.type}
                    focusPath={isEditingTypeForThis ? typeFocusPath : []}
                    onFocusChange={setTypeFocusPath}
                    isActive={isEditingTypeForThis}
                    readonly={!isEditingTypeForThis}
                    inline={true}
                  />
                </div>
              </div>
            );
          })}
        </div>
      )}
    </div>
  );
}

/**
 * Generate a unique ID for a new constructor
 */
let constructorIdCounter = 0;
export function generateConstructorId(): string {
  return `ctor_${constructorIdCounter++}`;
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
