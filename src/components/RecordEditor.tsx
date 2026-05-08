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
import { buildCommandTree, createCommand, createEscapeCommand, createSectionCommand, Command } from '../types/commands';
import { TTerm, mkTypeTT, RecordDef as TTRecordDef, prettyPrintLatexTT as ttPrettyPrintLatex, LatexPrintOptions } from '../compiler/surface';
import { TermFocusPath } from '../utils/termNavigation';
import { TTermRenderer } from './TTermRenderer';
import { FieldsSection, Field, createDefaultField } from './FieldsSection';
import { createTypeEditingCommands as createSharedTypeEditingCommands, TYPE_EDITING_KEYS } from '../utils/typeEditingCommands';
import { createNamedItemCommands, NAMED_ITEM_KEYS } from '../utils/namedItemCommands';
import { TTExamples, TTExampleRecordTypeName } from '../compiler/examples';
import { inlineExtension, elabRecordFull, createRecordRegistry, type TTKRecordDef } from '../compiler/elab';
import { prettyPrintLatex as ttkPrettyPrintLatex } from '../compiler/kernel';
import { MathJaxRenderer } from './MathJaxRenderer';

// ============================================================================
// Types
// ============================================================================

interface RecordParam {
  name: string;
  type: TTerm;
}

interface RecordDef {
  name: string;
  type: TTerm;
  params: RecordParam[];  // Parameters that scope over all fields
  fields: Field[];
  extends?: string[];  // Names of records this record extends
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
    params: example.params,
    fields: example.fields.map((field, idx) => ({
      id: `${example.name.toLowerCase()}-field-${idx}`,
      name: field.name,
      type: field.type,
    })),
    extends: example.extends,
  };
}

// ============================================================================
// Elaboration Display Component
// ============================================================================

/**
 * Displays the record after inlining extensions (TT) and after full elaboration (TTK)
 */
function ElaborationDisplay({ recordDef }: { recordDef: RecordDef }) {
  // Create a registry from all examples for resolving extends
  const registry = useMemo(() => {
    const allRecords = Object.values(TTExamples.recordTypes) as TTRecordDef[];
    return createRecordRegistry(allRecords);
  }, []);

  // Convert editor RecordDef to TTRecordDef for elaboration
  const ttRecord: TTRecordDef = useMemo(() => ({
    name: recordDef.name,
    type: recordDef.type,
    params: recordDef.params,
    fields: recordDef.fields.map(f => ({ name: f.name, type: f.type })),
    extends: recordDef.extends,
  }), [recordDef]);

  // Compute inlined record (TT with extensions inlined)
  const inlinedResult = useMemo(() => {
    try {
      const inlined = inlineExtension(ttRecord, registry);
      return { ok: true as const, value: inlined };
    } catch (e) {
      return { ok: false as const, error: e instanceof Error ? e.message : String(e) };
    }
  }, [ttRecord, registry]);

  // Compute fully elaborated record (TTK)
  const elaboratedResult = useMemo(() => {
    try {
      const elaborated = elabRecordFull(ttRecord, registry);
      return { ok: true as const, value: elaborated };
    } catch (e) {
      return { ok: false as const, error: e instanceof Error ? e.message : String(e) };
    }
  }, [ttRecord, registry]);

  // Don't show if record has no extends (nothing interesting to show)
  const hasExtends = recordDef.extends && recordDef.extends.length > 0;

  return (
    <div style={{ marginTop: '24px', display: 'flex', flexDirection: 'column', gap: '16px' }}>
      {/* Inlined Record (TT) */}
      <div style={{
        backgroundColor: '#fff8e1',
        border: '1px solid #ffe082',
        borderRadius: '8px',
        padding: '16px',
      }}>
        <h4 style={{
          margin: '0 0 12px 0',
          color: '#f57c00',
          fontSize: '14px',
          fontWeight: 600,
          display: 'flex',
          alignItems: 'center',
          gap: '8px'
        }}>
          <span style={{
            backgroundColor: '#fff3e0',
            padding: '2px 8px',
            borderRadius: '4px',
            border: '1px solid #ffcc80',
            fontFamily: 'monospace',
            fontSize: '12px'
          }}>TT</span>
          After inlineExtension
          {hasExtends && (
            <span style={{
              fontSize: '11px',
              color: '#888',
              fontWeight: 'normal',
              marginLeft: '8px'
            }}>
              (extensions inlined into fields)
            </span>
          )}
        </h4>
        {inlinedResult.ok ? (
          <InlinedRecordView record={inlinedResult.value} />
        ) : (
          <div style={{ color: '#d32f2f', fontFamily: 'monospace', fontSize: '13px' }}>
            Error: {inlinedResult.error}
          </div>
        )}
      </div>

      {/* Elaborated Record (TTK) */}
      <div style={{
        backgroundColor: '#e3f2fd',
        border: '1px solid #90caf9',
        borderRadius: '8px',
        padding: '16px',
      }}>
        <h4 style={{
          margin: '0 0 12px 0',
          color: '#1565c0',
          fontSize: '14px',
          fontWeight: 600,
          display: 'flex',
          alignItems: 'center',
          gap: '8px'
        }}>
          <span style={{
            backgroundColor: '#e1f5fe',
            padding: '2px 8px',
            borderRadius: '4px',
            border: '1px solid #81d4fa',
            fontFamily: 'monospace',
            fontSize: '12px'
          }}>TTK</span>
          After elabToKernel
          <span style={{
            fontSize: '11px',
            color: '#888',
            fontWeight: 'normal',
            marginLeft: '8px'
          }}>
            (kernel representation for type-checking)
          </span>
        </h4>
        {elaboratedResult.ok ? (
          <ElaboratedRecordView record={elaboratedResult.value} />
        ) : (
          <div style={{ color: '#d32f2f', fontFamily: 'monospace', fontSize: '13px' }}>
            Error: {elaboratedResult.error}
          </div>
        )}
      </div>
    </div>
  );
}

/** Global option to toggle equality type subscripts */
const latexOptions: LatexPrintOptions = {
  showEqTypeSubscript: true,  // Set to false for simple "x = y" rendering
};

/**
 * Inline KaTeX renderer for type expressions
 */
function InlineLatex({ tex }: { tex: string }) {
  return (
    <MathJaxRenderer
      tex={tex}
      style={{ display: 'inline-block', verticalAlign: 'middle' }}
    />
  );
}

/**
 * Render params as (A : Type) (B : Type) etc.
 */
function renderParamsTT(params: TTRecordDef['params']): React.ReactNode {
  if (params.length === 0) return null;
  return params.map((p, idx) => (
    <span key={idx}>
      <span style={{ color: '#666' }}>(</span>
      <span style={{ color: '#1565c0' }}>{p.name}</span>
      <span style={{ color: '#666' }}> : </span>
      <InlineLatex tex={ttPrettyPrintLatex(p.type, [], latexOptions)} />
      <span style={{ color: '#666' }}>)</span>
      {idx < params.length - 1 && ' '}
    </span>
  ));
}

/**
 * Read-only view of an inlined TT record
 */
function InlinedRecordView({ record }: { record: TTRecordDef }) {
  // Build context from params for field type printing
  const paramContext = record.params.map(p => p.name);

  return (
    <div style={{ fontFamily: 'monospace', fontSize: '14px' }}>
      <div style={{ marginBottom: '8px', display: 'flex', alignItems: 'center', gap: '4px', flexWrap: 'wrap' }}>
        <span style={{ color: '#666' }}>structure </span>
        <span style={{ fontWeight: 'bold' }}>{record.name}</span>
        {record.params.length > 0 && <span> </span>}
        {renderParamsTT(record.params)}
        <span style={{ color: '#666' }}> where</span>
      </div>
      <div style={{
        marginLeft: '20px',
        borderLeft: '2px solid #ffe082',
        paddingLeft: '12px'
      }}>
        {record.fields.length === 0 ? (
          <span style={{ color: '#999', fontStyle: 'italic' }}>no fields</span>
        ) : (
          record.fields.map((field, idx) => (
            <div key={idx} style={{ marginBottom: '8px', display: 'flex', alignItems: 'center', gap: '4px', flexWrap: 'wrap' }}>
              <span style={{ color: '#6a1b9a' }}>{field.name}</span>
              <span> : </span>
              <InlineLatex tex={ttPrettyPrintLatex(field.type, paramContext, latexOptions)} />
            </div>
          ))
        )}
      </div>
    </div>
  );
}

/**
 * Render params as (A : Type) (B : Type) etc. for TTK
 */
function renderParamsTTK(params: TTKRecordDef['params']): React.ReactNode {
  if (params.length === 0) return null;
  return params.map((p, idx) => (
    <span key={idx}>
      <span style={{ color: '#666' }}>(</span>
      <span style={{ color: '#1565c0' }}>{p.name}</span>
      <span style={{ color: '#666' }}> : </span>
      <InlineLatex tex={ttkPrettyPrintLatex(p.type, [], latexOptions)} />
      <span style={{ color: '#666' }}>)</span>
      {idx < params.length - 1 && ' '}
    </span>
  ));
}

/**
 * Read-only view of an elaborated TTK record
 */
function ElaboratedRecordView({ record }: { record: TTKRecordDef }) {
  // Build context from params for field type printing
  const paramContext = record.params.map(p => p.name);

  return (
    <div style={{ fontFamily: 'monospace', fontSize: '14px' }}>
      <div style={{ marginBottom: '8px', display: 'flex', alignItems: 'center', gap: '4px', flexWrap: 'wrap' }}>
        <span style={{ color: '#666' }}>structure </span>
        <span style={{ fontWeight: 'bold' }}>{record.name}</span>
        {record.params.length > 0 && <span> </span>}
        {renderParamsTTK(record.params)}
        <span style={{ color: '#666' }}> where</span>
      </div>
      <div style={{
        marginLeft: '20px',
        borderLeft: '2px solid #90caf9',
        paddingLeft: '12px'
      }}>
        {record.fields.length === 0 ? (
          <span style={{ color: '#999', fontStyle: 'italic' }}>no fields</span>
        ) : (
          record.fields.map((field, idx) => (
            <div key={idx} style={{ marginBottom: '8px', display: 'flex', alignItems: 'center', gap: '4px', flexWrap: 'wrap' }}>
              <span style={{ color: '#6a1b9a' }}>{field.name}</span>
              <span> : </span>
              <InlineLatex tex={ttkPrettyPrintLatex(field.type, paramContext, latexOptions)} />
            </div>
          ))
        )}
      </div>
    </div>
  );
}

// ============================================================================
// Inner Component
// ============================================================================

function RecordEditorInner() {
  // Top-level state for a single record definition
  const [recordDef, setRecordDef] = useState<RecordDef>({
    name: 'MyRecord',
    type: mkTypeTT(0),
    params: [],
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
      [NAMED_ITEM_KEYS.onAddItem]: handleAddField,
      [NAMED_ITEM_KEYS.onDeleteItem]: handleDeleteField,
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
          {/* Signature line: structure Name [extends Parent1, Parent2] : Type where */}
          <div style={{
            display: 'flex',
            alignItems: 'center',
            gap: '8px',
            marginBottom: '16px',
            fontFamily: 'monospace',
            fontSize: '18px',
            flexWrap: 'wrap'
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

            {/* Parameters */}
            {recordDef.params.length > 0 && (
              <span style={{ display: 'flex', alignItems: 'center', gap: '4px' }}>
                {recordDef.params.map((p, idx) => (
                  <span key={idx} style={{
                    color: '#1565c0',
                    backgroundColor: '#e3f2fd',
                    padding: '2px 8px',
                    borderRadius: '4px',
                    border: '1px solid #90caf9'
                  }}>
                    ({p.name} : <InlineLatex tex={ttPrettyPrintLatex(p.type, [], latexOptions)} />)
                  </span>
                ))}
              </span>
            )}

            {/* Extends clause */}
            {recordDef.extends && recordDef.extends.length > 0 && (
              <>
                <span style={{ color: '#9c27b0', fontWeight: 500 }}>extends</span>
                <span style={{
                  color: '#7b1fa2',
                  fontWeight: 600,
                  backgroundColor: '#f3e5f5',
                  padding: '2px 8px',
                  borderRadius: '4px',
                  border: '1px solid #ce93d8'
                }}>
                  {recordDef.extends.join(', ')}
                </span>
              </>
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
            paramContext={recordDef.params.map(p => p.name)}
          />
        </div>

        {/* Elaboration Display */}
        <ElaborationDisplay recordDef={recordDef} />
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
  return createNamedItemCommands({
    itemKind: 'field',
    sectionName: 'Fields',
  });
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
    createSectionCommand(
      'focus-fields',
      'f',
      'Fields',
      'Fields',
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
