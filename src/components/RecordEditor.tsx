/**
 * Record Editor
 *
 * UI component for editing record type definitions (structures).
 * Similar to InductiveTypeEditor but for records with named fields
 * instead of constructors.
 *
 * Keyboard navigation:
 * - n: Edit name
 * - t: Edit type expression
 * - f: Focus on fields section
 *   - a: Add field
 *   - n: Edit selected field name
 *   - t: Edit selected field type
 *   - d: Delete selected field
 *   - Arrow keys: Navigate between fields
 *   - 0-9: Jump to field by index
 * - Escape: Go back one level
 */

import { useState, useMemo, useEffect } from 'react';
import { NavigationProvider, useNavigation } from '../contexts/NavigationContext';
import { NavigationFooter, NavigationFooterSpacer } from './NavigationFooter';
import { buildCommandTree, createCommand, createEscapeCommand, Command } from '../types/commands';
import { TTerm, mkType } from '../types/tt-core';
import { TermFocusPath } from '../utils/termNavigation';
import { TTermRenderer } from './TTermRenderer';
import { FieldsSection, Field, createDefaultField } from './FieldsSection';
import { createTypeEditingCommands as createSharedTypeEditingCommands, TYPE_EDITING_KEYS } from '../utils/typeEditingCommands';
import { TTExamples, TTExampleRecordTypeName } from '../types/tt-examples';

// ============================================================================
// Types
// ============================================================================

interface RecordDef {
  name: string;
  type: TTerm;
  fields: Field[];
}

// ============================================================================
// Example Loading
// ============================================================================

const exampleNames = Object.keys(TTExamples.recordTypes) as TTExampleRecordTypeName[];

/**
 * Convert a TT example to the editor's RecordDef format
 * (adds unique IDs to fields)
 */
function loadExampleAsEditorState(exampleName: TTExampleRecordTypeName): RecordDef {
  const example = TTExamples.recordTypes[exampleName];
  return {
    name: example.name,
    type: example.type,
    fields: example.fields.map((field, idx) => ({
      id: `${example.name.toLowerCase()}-field-${idx}`,
      name: field.name,
      type: field.type,
    })),
  };
}

// ============================================================================
// Inner Component
// ============================================================================

function RecordEditorInner() {
  // Top-level state for a single record definition
  const [recordDef, setRecordDef] = useState<RecordDef>({
    name: 'MyRecord',
    type: mkType(0),
    fields: []
  });

  // Track currently selected example
  const [selectedExample, setSelectedExample] = useState<string>('');

  // Focus path within the type term
  const [typeFocusPath, setTypeFocusPath] = useState<TermFocusPath>([]);

  const navigation = useNavigation();

  // Derive UI state from navigation path
  const isEditingName = navigation.state.navigationPath[0] === 'Name' &&
    navigation.state.navigationPath[1] === 'Editor';
  const isEditingType = navigation.state.navigationPath[0] === 'Type';

  // Handlers
  const handleEditName = () => {
    // Navigation will be set by command
  };

  const handleSaveName = (newName: string) => {
    setRecordDef(prev => ({ ...prev, name: newName }));
    navigation.navigateTo([]);
  };

  const handleEditType = () => {
    setTypeFocusPath([]);
  };

  // Field handlers
  const handleUpdateField = (id: string, updated: Field) => {
    setRecordDef(prev => ({
      ...prev,
      fields: prev.fields.map(f => f.id === id ? updated : f)
    }));
  };

  const handleAddField = () => {
    const newField = createDefaultField(`field${recordDef.fields.length}`);
    setRecordDef(prev => ({
      ...prev,
      fields: [...prev.fields, newField]
    }));
    navigation.navigateTo(['Fields', String(recordDef.fields.length)]);
  };

  const handleDeleteField = (id: string) => {
    setRecordDef(prev => ({
      ...prev,
      fields: prev.fields.filter(f => f.id !== id)
    }));
    navigation.navigateTo(['Fields']);
  };

  // Handler for example dropdown
  const handleExampleChange = (exampleName: string) => {
    setSelectedExample(exampleName);
    if (exampleName && exampleName in TTExamples.recordTypes) {
      const newState = loadExampleAsEditorState(exampleName as TTExampleRecordTypeName);
      setRecordDef(newState);
      setTypeFocusPath([]);
      navigation.navigateTo([]);
    }
  };

  // Update navigation metadata
  useEffect(() => {
    const metadata: Record<string, unknown> = {
      onEditName: handleEditName,
      onEditType: handleEditType,
      typeFocusPath,
      setTypeFocusPath,
      recordType: recordDef.type,
      setRecordType: (newType: TTerm) => setRecordDef(prev => ({ ...prev, type: newType })),
      // Field handlers
      onAddField: handleAddField,
      onDeleteField: handleDeleteField,
    };

    // Populate TYPE_EDITING_KEYS when editing the record type
    if (isEditingType) {
      metadata[TYPE_EDITING_KEYS.term] = recordDef.type;
      metadata[TYPE_EDITING_KEYS.focusPath] = typeFocusPath;
      metadata[TYPE_EDITING_KEYS.setTerm] = (newType: TTerm) => setRecordDef(prev => ({ ...prev, type: newType }));
      metadata[TYPE_EDITING_KEYS.setFocusPath] = setTypeFocusPath;
      metadata[TYPE_EDITING_KEYS.returnPath] = ['Type'];
    }

    navigation.updateMetadata(metadata);
  }, [navigation.updateMetadata, typeFocusPath, recordDef.name, recordDef.type, recordDef.fields, isEditingType]);

  return (
    <NavigationFooterSpacer>
      <div style={{
        padding: '20px',
        fontFamily: 'system-ui, sans-serif',
        maxWidth: '1200px',
        margin: '0 auto'
      }}>
        <div style={{
          display: 'flex',
          justifyContent: 'space-between',
          alignItems: 'center',
          marginBottom: '24px',
          borderBottom: '2px solid #2e7d32',
          paddingBottom: '16px'
        }}>
          <h2 style={{ margin: 0, color: '#2e7d32' }}>Record Editor</h2>
          <div style={{ display: 'flex', alignItems: 'center', gap: '8px' }}>
            <label
              htmlFor="record-example-select"
              style={{
                fontSize: '13px',
                color: '#666',
                fontWeight: 500,
              }}
            >
              Load example:
            </label>
            <select
              id="record-example-select"
              value={selectedExample}
              onChange={(e) => handleExampleChange(e.target.value)}
              style={{
                padding: '6px 12px',
                fontSize: '13px',
                borderRadius: '6px',
                border: '1px solid #ccd',
                backgroundColor: '#fafbfc',
                color: '#333',
                cursor: 'pointer',
                minWidth: '140px',
                outline: 'none',
                transition: 'border-color 0.15s, box-shadow 0.15s',
              }}
              onFocus={(e) => {
                e.target.style.borderColor = '#2e7d32';
                e.target.style.boxShadow = '0 0 0 2px rgba(46, 125, 50, 0.15)';
              }}
              onBlur={(e) => {
                e.target.style.borderColor = '#ccd';
                e.target.style.boxShadow = 'none';
              }}
            >
              <option value="">— Select —</option>
              {exampleNames.map((name) => (
                <option key={name} value={name}>
                  {name}
                </option>
              ))}
            </select>
          </div>
        </div>

        <div style={{
          backgroundColor: 'white',
          border: '2px solid #e9ecef',
          borderRadius: '12px',
          padding: '24px',
          boxShadow: '0 4px 6px rgba(0, 0, 0, 0.05)'
        }}>
          {/* Signature line: structure Name : Type where */}
          <div style={{
            display: 'flex',
            alignItems: 'center',
            gap: '8px',
            marginBottom: '16px',
            fontFamily: 'monospace',
            fontSize: '18px'
          }}>
            <span style={{ color: '#666', fontWeight: 500 }}>structure</span>

            {/* Name */}
            {isEditingName ? (
              <input
                type="text"
                defaultValue={recordDef.name}
                autoFocus
                onKeyDown={(e) => {
                  if (e.key === 'Enter') {
                    handleSaveName(e.currentTarget.value);
                  } else if (e.key === 'Escape') {
                    navigation.navigateTo([]);
                  }
                }}
                onBlur={(e) => handleSaveName(e.currentTarget.value)}
                style={{
                  fontFamily: 'monospace',
                  fontSize: '18px',
                  fontWeight: 'bold',
                  border: '2px solid #2e7d32',
                  borderRadius: '4px',
                  padding: '4px 8px',
                  backgroundColor: '#f0fff0',
                  width: 'auto',
                  minWidth: '100px'
                }}
              />
            ) : (
              <span style={{ fontWeight: 'bold' }}>
                {recordDef.name}
              </span>
            )}

            {/* Colon */}
            <span>:</span>

            {/* Type */}
            <div style={{
              border: isEditingType ? '2px solid #2e7d32' : '1px solid transparent',
              borderRadius: '4px',
              padding: '2px 4px',
              backgroundColor: isEditingType ? '#f0fff0' : 'transparent'
            }}>
              <TTermRenderer
                term={recordDef.type}
                focusPath={typeFocusPath}
                onFocusChange={setTypeFocusPath}
                onTermChange={(newType) => setRecordDef(prev => ({ ...prev, type: newType }))}
                isActive={isEditingType}
                readonly={!isEditingType}
                inline={true}
              />
            </div>

            {/* where keyword */}
            <span style={{ color: '#666', fontWeight: 500 }}>where</span>
          </div>

          {/* Fields */}
          <FieldsSection
            fields={recordDef.fields}
            onUpdateField={handleUpdateField}
            onAddField={handleAddField}
            onDeleteField={handleDeleteField}
          />
        </div>

        <div style={{
          marginTop: '16px',
          padding: '12px',
          backgroundColor: '#f8f9fa',
          borderRadius: '6px',
          fontSize: '12px',
          color: '#666'
        }}>
        </div>
      </div>
    </NavigationFooterSpacer>
  );
}

// ============================================================================
// Commands
// ============================================================================

/**
 * Commands available when in the Fields section
 */
function createFieldCommands(): Command[] {
  return [
    // 'a' - Add field
    createCommand(
      'add-field',
      'a',
      'Add',
      (context) => {
        const onAddField = context.metadata?.onAddField as (() => void) | undefined;
        onAddField?.();
        return { preventDefault: true };
      },
      {
        description: 'Add a new field',
      }
    ),

    // 'n' - Edit selected field name
    createCommand(
      'edit-field-name',
      'n',
      'Name',
      (context) => {
        const selectedIndex = context.metadata?.selectedItemIndex as number | undefined;
        if (selectedIndex === undefined) return { preventDefault: true };

        return {
          navigationPath: ['Fields', String(selectedIndex), 'EditName'],
          preventDefault: true,
        };
      },
      {
        description: 'Edit field name',
        isAvailable: (context) => context.metadata?.selectedItemIndex !== undefined,
      }
    ),

    // 't' - Edit selected field type
    createCommand(
      'edit-field-type',
      't',
      'Type',
      (context) => {
        const selectedIndex = context.metadata?.selectedItemIndex as number | undefined;
        if (selectedIndex === undefined) return { preventDefault: true };

        return {
          navigationPath: ['Fields', String(selectedIndex), 'Type'],
          preventDefault: true,
        };
      },
      {
        description: 'Edit field type',
        isAvailable: (context) => context.metadata?.selectedItemIndex !== undefined,
        children: createSharedTypeEditingCommands(),
      }
    ),

    // 'd' - Delete selected field
    createCommand(
      'delete-field',
      'd',
      'Delete',
      (context) => {
        const selectedId = context.metadata?.selectedItemId as string | undefined;
        const onDeleteField = context.metadata?.onDeleteField as ((id: string) => void) | undefined;
        if (selectedId && onDeleteField) {
          onDeleteField(selectedId);
        }
        return {
          navigationPath: ['Fields'],
          preventDefault: true,
        };
      },
      {
        description: 'Delete selected field',
        isAvailable: (context) => context.metadata?.selectedItemIndex !== undefined,
      }
    ),
  ];
}

/**
 * Command tree for record editor navigation
 */
function createRecordCommandTree() {
  const rootCommands: Command[] = [
    // Escape command
    createEscapeCommand(),

    // 'n' - Edit name
    createCommand(
      'edit-name',
      'n',
      'Name',
      (context) => {
        const onEditName = context.metadata?.onEditName as (() => void) | undefined;
        onEditName?.();

        return {
          navigationPath: ['Name', 'Editor'],
          preventDefault: true,
        };
      },
      {
        description: 'Edit the record name',
      }
    ),

    // 't' - Edit type expression
    createCommand(
      'edit-type',
      't',
      'Type',
      (context) => {
        const onEditType = context.metadata?.onEditType as (() => void) | undefined;
        onEditType?.();

        return {
          navigationPath: ['Type'],
          preventDefault: true,
        };
      },
      {
        description: 'Edit the type expression',
        children: createSharedTypeEditingCommands(),
      }
    ),

    // 'f' - Focus on fields
    createCommand(
      'focus-fields',
      'f',
      'Fields',
      () => ({
        navigationPath: ['Fields'],
        preventDefault: true,
      }),
      {
        description: 'Navigate to fields',
        children: createFieldCommands(),
      }
    ),
  ];

  return buildCommandTree(rootCommands);
}

// ============================================================================
// Main Export
// ============================================================================

/**
 * Record Editor - wrapped with NavigationProvider
 */
export function RecordEditor() {
  const commandTree = useMemo(() => createRecordCommandTree(), []);

  return (
    <NavigationProvider initialCommandTree={commandTree}>
      <RecordEditorInner />
      <NavigationFooter />
    </NavigationProvider>
  );
}

