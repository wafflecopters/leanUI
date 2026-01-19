/**
 * Named Items Section - Shared Component for Editing Lists of Named Typed Items
 *
 * This is a reusable component for editing lists of items that have:
 * - id: unique identifier
 * - name: display name
 * - type: TT type expression
 *
 * Used by:
 * - ConstructorsSection (for inductive type constructors)
 * - FieldsSection (for record fields)
 */

import { useEffect, useState, useRef, useCallback, ReactNode } from 'react';
import { useNavigation } from '../contexts/NavigationContext';
import { EditableInput } from './EditableInput';
import { TTermRenderer } from './TTermRenderer';
import { TTerm } from '../compiler/surface';
import { TermFocusPath } from '../utils/termNavigation';
import { TYPE_EDITING_KEYS } from '../utils/typeEditingCommands';

// ============================================================================
// Types
// ============================================================================

/**
 * A named item with a type (used for constructors, fields, etc.)
 */
export interface NamedTypedItem {
  id: string;
  name: string;
  type: TTerm;
}

/**
 * Configuration for how the section should display and behave
 */
export interface NamedItemsSectionConfig {
  /** Navigation path prefix for this section (e.g., 'Constructors', 'Fields') */
  navigationKey: string;

  /** Prefix character shown before each item (e.g., '|' for constructors, '•' for fields) */
  itemPrefix?: string;

  /** Placeholder text when the list is empty */
  emptyPlaceholder?: string;

  /** Color for item names */
  nameColor?: string;

  /** Whether to show index numbers when focused */
  showIndices?: boolean;

  /** Optional custom renderer for types when not actively editing */
  renderTypeReadonly?: (type: TTerm) => ReactNode;
}

const defaultConfig: Omit<Required<NamedItemsSectionConfig>, 'renderTypeReadonly'> & { renderTypeReadonly?: (type: TTerm) => ReactNode } = {
  navigationKey: 'Items',
  itemPrefix: '|',
  emptyPlaceholder: '-',
  nameColor: '#0066cc',
  showIndices: true,
  renderTypeReadonly: undefined,
};

// ============================================================================
// Props
// ============================================================================

interface NamedItemsSectionProps<T extends NamedTypedItem> {
  /** The list of items to display */
  items: T[];

  /** Callback when an item is updated */
  onUpdateItem: (id: string, updated: T) => void;

  /** Configuration for display and behavior */
  config: NamedItemsSectionConfig;
}

// ============================================================================
// Component
// ============================================================================

export function NamedItemsSection<T extends NamedTypedItem>({
  items,
  onUpdateItem,
  config: userConfig,
}: NamedItemsSectionProps<T>) {
  const config = { ...defaultConfig, ...userConfig };
  const navigation = useNavigation();

  // Use refs to avoid dependency issues
  const onUpdateItemRef = useRef(onUpdateItem);
  onUpdateItemRef.current = onUpdateItem;

  const navigationRef = useRef(navigation);
  navigationRef.current = navigation;

  // Derive state from navigation path
  const navPath = navigation.state.navigationPath;
  const isInFocusChain = navPath[0] === config.navigationKey;
  const isActive = navPath.length === 1 && navPath[0] === config.navigationKey;

  // Parse selected index: ['Items', '0'] or ['Items', '0', 'EditName']
  const selectedIndex = navPath.length >= 2 && navPath[0] === config.navigationKey && /^\d+$/.test(navPath[1])
    ? parseInt(navPath[1], 10)
    : null;

  // Derive edit mode
  const isEditingName = navPath[2] === 'EditName';
  const isEditingType = navPath[2] === 'Type';

  // Local state for type focus path
  const [typeFocusPath, setTypeFocusPath] = useState<TermFocusPath>([]);

  // Get selected item
  const selectedItem = selectedIndex !== null && selectedIndex < items.length
    ? items[selectedIndex]
    : null;

  // Sync metadata - use stable dependencies
  useEffect(() => {
    if (selectedItem && selectedIndex !== null) {
      const setItemType = (newType: TTerm) => {
        onUpdateItemRef.current(selectedItem.id, { ...selectedItem, type: newType } as T);
      };

      navigationRef.current.updateMetadata({
        // Item info for commands
        selectedItemId: selectedItem.id,
        selectedItemIndex: selectedIndex,
        // Standardized TypeEditingContext keys for shared commands
        [TYPE_EDITING_KEYS.term]: selectedItem.type,
        [TYPE_EDITING_KEYS.focusPath]: typeFocusPath,
        [TYPE_EDITING_KEYS.setTerm]: setItemType,
        [TYPE_EDITING_KEYS.setFocusPath]: setTypeFocusPath,
        [TYPE_EDITING_KEYS.returnPath]: [config.navigationKey, String(selectedIndex), 'Type'],
      });
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [selectedItem?.id, selectedIndex, typeFocusPath, config.navigationKey]);

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
        if (items.length === 0) return;
        const newIndex = selectedIndex === null ? 0 : (selectedIndex + 1) % items.length;
        navigation.navigateTo([config.navigationKey, String(newIndex)]);
        e.preventDefault();
        return;
      }

      if (e.key === 'ArrowUp' || e.key === 'ArrowLeft') {
        if (items.length === 0) return;
        const newIndex = selectedIndex === null
          ? items.length - 1
          : (selectedIndex - 1 + items.length) % items.length;
        navigation.navigateTo([config.navigationKey, String(newIndex)]);
        e.preventDefault();
        return;
      }

      // Digit keys for direct selection
      if (/^[0-9]$/.test(e.key)) {
        const index = parseInt(e.key, 10);
        if (index >= 0 && index < items.length) {
          navigation.navigateTo([config.navigationKey, String(index)]);
        }
        e.preventDefault();
        return;
      }
    };

    window.addEventListener('keydown', handleKeyDown);
    return () => window.removeEventListener('keydown', handleKeyDown);
  }, [isActive, selectedIndex, items, navigation, config.navigationKey]);

  // Handle save name
  const handleSaveName = useCallback((value: string) => {
    if (!selectedItem) return;
    onUpdateItem(selectedItem.id, {
      ...selectedItem,
      name: value,
    } as T);
    navigation.navigateTo([config.navigationKey, String(selectedIndex)]);
  }, [selectedItem, onUpdateItem, navigation, config.navigationKey, selectedIndex]);

  // Handle cancel
  const handleCancel = useCallback(() => {
    navigation.navigateTo([config.navigationKey, String(selectedIndex)]);
  }, [navigation, config.navigationKey, selectedIndex]);

  return (
    <div style={{
      border: isInFocusChain ? '2px solid #007acc' : '2px solid transparent',
      borderRadius: '8px',
      padding: '12px',
      backgroundColor: isInFocusChain ? '#f8fbff' : 'transparent',
      transition: 'all 0.15s ease',
    }}>
      {items.length === 0 ? (
        <div style={{
          color: '#999',
          fontStyle: 'italic',
          paddingLeft: '20px',
          fontFamily: 'monospace',
          fontSize: '14px'
        }}>
          {config.emptyPlaceholder}
        </div>
      ) : (
        <div style={{ paddingLeft: '8px' }}>
          {items.map((item, index) => {
            const isSelected = selectedIndex === index;
            const isEditingNameForThis = isSelected && isEditingName;
            const isEditingTypeForThis = isSelected && isEditingType;

            return (
              <div
                key={item.id}
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
                {/* Prefix character */}
                {config.itemPrefix && (
                  <span style={{ color: '#666' }}>{config.itemPrefix}</span>
                )}

                {/* Index (when in focus chain) */}
                {config.showIndices && isInFocusChain && (
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
                    initialValue={item.name}
                    onSave={handleSaveName}
                    onCancel={handleCancel}
                    style={{ minWidth: '100px' }}
                  />
                ) : (
                  <span style={{
                    color: config.nameColor,
                    fontWeight: isSelected ? 'bold' : 'normal',
                  }}>
                    {item.name}
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
                  {isEditingTypeForThis ? (
                    <TTermRenderer
                      term={item.type}
                      focusPath={typeFocusPath}
                      onFocusChange={setTypeFocusPath}
                      onTermChange={(newType) => onUpdateItem(item.id, { ...item, type: newType } as T)}
                      isActive={true}
                      readonly={false}
                      inline={true}
                    />
                  ) : config.renderTypeReadonly ? (
                    config.renderTypeReadonly(item.type)
                  ) : (
                    <TTermRenderer
                      term={item.type}
                      focusPath={[]}
                      onFocusChange={setTypeFocusPath}
                      onTermChange={(newType) => onUpdateItem(item.id, { ...item, type: newType } as T)}
                      isActive={false}
                      readonly={true}
                      inline={true}
                    />
                  )}
                </div>
              </div>
            );
          })}
        </div>
      )}
    </div>
  );
}

// ============================================================================
// Helper: Generate unique IDs
// ============================================================================

let itemIdCounter = 0;

/**
 * Generate a unique ID for a new item
 */
export function generateItemId(prefix: string = 'item'): string {
  return `${prefix}_${itemIdCounter++}`;
}

