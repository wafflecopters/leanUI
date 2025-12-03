import { useState, useMemo, useEffect } from 'react';
import { NavigationProvider, useNavigation } from '../contexts/NavigationContext';
import { NavigationFooter, NavigationFooterSpacer } from './NavigationFooter';
import { buildCommandTree, createCommand, createEscapeCommand, Command } from '../types/commands';
import { TTerm, mkType } from '../types/tt-core';
import { TermFocusPath, getBinderName, renameBinderAtPath } from '../utils/termNavigation';
import { TTermRenderer } from './TTermRenderer';
import { ConstructorsSection, Constructor, createConstructorForInductive } from './ConstructorsSection';
import { EditableInput } from './EditableInput';
import { createTypeEditingCommands as createSharedTypeEditingCommands, TYPE_EDITING_KEYS } from '../utils/typeEditingCommands';

interface InductiveTypeDef {
  name: string;
  type: TTerm; // TTerm - params will be inferred later (à la Idris)
  constructors: Constructor[];
}

function InductiveTypeEditorInner() {
  // Top-level state for a single inductive type definition
  const [inductiveDef, setInductiveDef] = useState<InductiveTypeDef>({
    name: 'MyInductive',
    type: mkType(0), // Start with Type_0
    constructors: []
  });

  // Focus path within the type term
  const [typeFocusPath, setTypeFocusPath] = useState<TermFocusPath>([]);

  const navigation = useNavigation();

  // Derive UI state from navigation path
  const isEditingName = navigation.state.navigationPath[0] === 'Name' &&
    navigation.state.navigationPath[1] === 'Editor';
  const isEditingType = navigation.state.navigationPath[0] === 'Type';
  const isEditingBinderName = navigation.state.navigationPath[0] === 'Type' &&
    navigation.state.navigationPath[1] === 'EditBinderName';

  // Handlers
  const handleEditName = () => {
    // Navigation will be set by command
  };

  const handleSaveName = (newName: string) => {
    setInductiveDef(prev => ({ ...prev, name: newName }));
    // Pop back to root
    navigation.navigateTo([]);
  };

  const handleEditType = () => {
    // Reset focus to root of type
    setTypeFocusPath([]);
  };

  // Handler for saving binder name
  const handleSaveBinderName = (newName: string) => {
    const newType = renameBinderAtPath(inductiveDef.type, typeFocusPath, newName);
    if (newType) {
      setInductiveDef(prev => ({ ...prev, type: newType }));
    }
    // Go back to Type editing
    navigation.navigateTo(['Type']);
  };

  const handleCancelBinderName = () => {
    navigation.navigateTo(['Type']);
  };

  // Get current binder name if editing
  const currentBinderName = isEditingBinderName
    ? getBinderName(inductiveDef.type, typeFocusPath) ?? ''
    : '';

  // Constructor handlers
  const handleUpdateConstructor = (id: string, updated: Constructor) => {
    setInductiveDef(prev => ({
      ...prev,
      constructors: prev.constructors.map(c => c.id === id ? updated : c)
    }));
  };

  const handleAddConstructor = () => {
    const newCtor = createConstructorForInductive(
      `ctor${inductiveDef.constructors.length}`,
      inductiveDef.name,
      inductiveDef.type
    );
    setInductiveDef(prev => ({
      ...prev,
      constructors: [...prev.constructors, newCtor]
    }));
    // Navigate to the new constructor
    navigation.navigateTo(['Constructors', String(inductiveDef.constructors.length)]);
  };

  const handleDeleteConstructor = (id: string) => {
    setInductiveDef(prev => ({
      ...prev,
      constructors: prev.constructors.filter(c => c.id !== id)
    }));
    navigation.navigateTo(['Constructors']);
  };

  // Update navigation metadata with handlers
  // Only set TYPE_EDITING_KEYS when we're editing the inductive type (not constructor types)
  useEffect(() => {
    const metadata: Record<string, unknown> = {
      onEditName: handleEditName,
      onEditType: handleEditType,
      // Legacy keys (for any remaining old code)
      typeFocusPath,
      setTypeFocusPath,
      inductiveType: inductiveDef.type,
      setInductiveType: (newType: TTerm) => setInductiveDef(prev => ({ ...prev, type: newType })),
      // Constructor handlers
      onAddConstructor: handleAddConstructor,
      onDeleteConstructor: handleDeleteConstructor,
    };

    // Only populate TYPE_EDITING_KEYS when we're at the inductive type level
    // (not when editing constructor types - ConstructorsSection handles that)
    if (isEditingType) {
      metadata[TYPE_EDITING_KEYS.term] = inductiveDef.type;
      metadata[TYPE_EDITING_KEYS.focusPath] = typeFocusPath;
      metadata[TYPE_EDITING_KEYS.setTerm] = (newType: TTerm) => setInductiveDef(prev => ({ ...prev, type: newType }));
      metadata[TYPE_EDITING_KEYS.setFocusPath] = setTypeFocusPath;
      metadata[TYPE_EDITING_KEYS.returnPath] = ['Type'];
      metadata[TYPE_EDITING_KEYS.editBinderNamePath] = ['Type', 'EditBinderName'];
    }

    navigation.updateMetadata(metadata);
  }, [navigation.updateMetadata, typeFocusPath, inductiveDef.type, inductiveDef.constructors, isEditingType]);

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
          borderBottom: '2px solid #007acc',
          paddingBottom: '16px'
        }}>
          <h2 style={{ margin: 0, color: '#007acc' }}>Inductive Type Editor</h2>
        </div>

        <div style={{
          backgroundColor: 'white',
          border: '2px solid #e9ecef',
          borderRadius: '12px',
          padding: '24px',
          boxShadow: '0 4px 6px rgba(0, 0, 0, 0.05)'
        }}>
          {/* Signature line: Name Params : Type */}
          <div style={{
            display: 'flex',
            alignItems: 'center',
            gap: '8px',
            marginBottom: '24px',
            fontFamily: 'monospace',
            fontSize: '18px'
          }}>
            {/* Name */}
            {isEditingName ? (
              <input
                type="text"
                defaultValue={inductiveDef.name}
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
                  border: '2px solid #007acc',
                  borderRadius: '4px',
                  padding: '4px 8px',
                  backgroundColor: '#f0f8ff',
                  width: 'auto',
                  minWidth: '100px'
                }}
              />
            ) : (
              <span style={{ fontWeight: 'bold' }}>
                {inductiveDef.name}
              </span>
            )}

            {/* Colon */}
            <span>:</span>

            {/* Type */}
            <div style={{
              border: isEditingType ? '2px solid #007acc' : '1px solid transparent',
              borderRadius: '4px',
              padding: '2px 4px',
              backgroundColor: isEditingType ? '#f0f8ff' : 'transparent'
            }}>
              <TTermRenderer
                term={inductiveDef.type}
                focusPath={typeFocusPath}
                onFocusChange={setTypeFocusPath}
                isActive={isEditingType && !isEditingBinderName}
                readonly={!isEditingType || isEditingBinderName}
                inline={true}
              />
            </div>

            {/* Binder name editor */}
            {isEditingBinderName && (
              <div style={{
                marginLeft: '8px',
                display: 'flex',
                alignItems: 'center',
                gap: '4px',
              }}>
                <span style={{ color: '#666', fontSize: '12px' }}>name:</span>
                <EditableInput
                  initialValue={currentBinderName}
                  onSave={handleSaveBinderName}
                  onCancel={handleCancelBinderName}
                  style={{ minWidth: '80px' }}
                />
              </div>
            )}
          </div>

          {/* Constructors */}
          <ConstructorsSection
            constructors={inductiveDef.constructors}
            onUpdateConstructor={handleUpdateConstructor}
            onAddConstructor={handleAddConstructor}
            onDeleteConstructor={handleDeleteConstructor}
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


/**
 * Commands available when in the Constructors section
 */
function createConstructorCommands(): Command[] {
  return [
    // 'a' - Add constructor
    createCommand(
      'add-constructor',
      'a',
      'Add',
      (context) => {
        const onAddConstructor = context.metadata?.onAddConstructor as (() => void) | undefined;
        onAddConstructor?.();
        return { preventDefault: true };
      },
      {
        description: 'Add a new constructor',
      }
    ),

    // 'n' - Edit selected constructor name
    createCommand(
      'edit-constructor-name',
      'n',
      'Name',
      (context) => {
        const selectedIndex = context.metadata?.selectedConstructorIndex as number | undefined;
        if (selectedIndex === undefined) return { preventDefault: true };

        return {
          navigationPath: ['Constructors', String(selectedIndex), 'EditName'],
          preventDefault: true,
        };
      },
      {
        description: 'Edit constructor name',
        isAvailable: (context) => context.metadata?.selectedConstructorIndex !== undefined,
      }
    ),

    // 't' - Edit selected constructor type
    createCommand(
      'edit-constructor-type',
      't',
      'Type',
      (context) => {
        const selectedIndex = context.metadata?.selectedConstructorIndex as number | undefined;
        if (selectedIndex === undefined) return { preventDefault: true };

        return {
          navigationPath: ['Constructors', String(selectedIndex), 'Type'],
          preventDefault: true,
        };
      },
      {
        description: 'Edit constructor type',
        isAvailable: (context) => context.metadata?.selectedConstructorIndex !== undefined,
        children: createSharedTypeEditingCommands(),
      }
    ),

    // 'd' - Delete selected constructor
    createCommand(
      'delete-constructor',
      'd',
      'Delete',
      (context) => {
        const selectedId = context.metadata?.selectedConstructorId as string | undefined;
        const onDeleteConstructor = context.metadata?.onDeleteConstructor as ((id: string) => void) | undefined;
        if (selectedId && onDeleteConstructor) {
          onDeleteConstructor(selectedId);
        }
        return {
          navigationPath: ['Constructors'],
          preventDefault: true,
        };
      },
      {
        description: 'Delete selected constructor',
        isAvailable: (context) => context.metadata?.selectedConstructorIndex !== undefined,
      }
    ),
  ];
}


/**
 * Command tree for inductive type editor navigation
 */
function createInductiveTypeCommandTree() {
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
        description: 'Edit the inductive type name',
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

    // 'c' - Focus on constructors
    createCommand(
      'focus-constructors',
      'c',
      'Constructors',
      () => ({
        navigationPath: ['Constructors'],
        preventDefault: true,
      }),
      {
        description: 'Navigate to constructors',
        children: createConstructorCommands(),
      }
    ),
  ];

  return buildCommandTree(rootCommands);
}

/**
 * Main export - InductiveTypeEditor wrapped with NavigationProvider
 */
export function InductiveTypeEditor() {
  const commandTree = useMemo(() => createInductiveTypeCommandTree(), []);

  return (
    <NavigationProvider initialCommandTree={commandTree}>
      <InductiveTypeEditorInner />
      <NavigationFooter />
    </NavigationProvider>
  );
}
