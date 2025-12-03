import { useState, useMemo, useEffect } from 'react';
import { NavigationProvider, useNavigation } from '../contexts/NavigationContext';
import { NavigationFooter, NavigationFooterSpacer } from './NavigationFooter';
import { buildCommandTree, createCommand, createEscapeCommand, Command } from '../types/commands';
import { TTerm, mkType, mkPi, mkHole } from '../types/tt-core';
import { TermFocusPath, getTermAtPath, setTermAtPath, freshHoleId, navigateUp, navigateDown, navigateLeft, navigateRight } from '../utils/termNavigation';
import { TTermRenderer } from './TTermRenderer';
import { ConstructorsSection, Constructor, createConstructorForInductive } from './ConstructorsSection';

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
  useEffect(() => {
    navigation.updateMetadata({
      onEditName: handleEditName,
      onEditType: handleEditType,
      typeFocusPath,
      setTypeFocusPath,
      inductiveType: inductiveDef.type,
      setInductiveType: (newType: TTerm) => setInductiveDef(prev => ({ ...prev, type: newType })),
      // Constructor handlers
      onAddConstructor: handleAddConstructor,
      onDeleteConstructor: handleDeleteConstructor,
    });
  }, [navigation.updateMetadata, typeFocusPath, inductiveDef.type, inductiveDef.constructors]);

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
                isActive={isEditingType}
                readonly={!isEditingType}
                inline={true}
              />
            </div>
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
 * Commands available when editing the type expression
 */
function createTypeEditingCommands(): Command[] {
  return [
    // Arrow key navigation
    createCommand(
      'nav-up',
      'ArrowUp',
      '↑',
      (context) => {
        const typeFocusPath = context.metadata?.typeFocusPath as TermFocusPath | undefined;
        const setTypeFocusPath = context.metadata?.setTypeFocusPath as ((path: TermFocusPath) => void) | undefined;

        if (typeFocusPath === undefined || !setTypeFocusPath) {
          return { preventDefault: true };
        }

        const newPath = navigateUp(typeFocusPath);
        if (newPath !== null) {
          setTypeFocusPath(newPath);
        }

        return {
          navigationPath: ['Type'],
          preventDefault: true,
        };
      },
      {
        description: 'Navigate up to parent',
      }
    ),

    createCommand(
      'nav-down',
      'ArrowDown',
      '↓',
      (context) => {
        const inductiveType = context.metadata?.inductiveType as TTerm | undefined;
        const typeFocusPath = context.metadata?.typeFocusPath as TermFocusPath | undefined;
        const setTypeFocusPath = context.metadata?.setTypeFocusPath as ((path: TermFocusPath) => void) | undefined;

        if (!inductiveType || typeFocusPath === undefined || !setTypeFocusPath) {
          return { preventDefault: true };
        }

        const newPath = navigateDown(inductiveType, typeFocusPath);
        if (newPath !== null) {
          setTypeFocusPath(newPath);
        }

        return {
          navigationPath: ['Type'],
          preventDefault: true,
        };
      },
      {
        description: 'Navigate down to first child',
      }
    ),

    createCommand(
      'nav-left',
      'ArrowLeft',
      '←',
      (context) => {
        const inductiveType = context.metadata?.inductiveType as TTerm | undefined;
        const typeFocusPath = context.metadata?.typeFocusPath as TermFocusPath | undefined;
        const setTypeFocusPath = context.metadata?.setTypeFocusPath as ((path: TermFocusPath) => void) | undefined;

        if (!inductiveType || typeFocusPath === undefined || !setTypeFocusPath) {
          return { preventDefault: true };
        }

        const newPath = navigateLeft(inductiveType, typeFocusPath);
        if (newPath !== null) {
          setTypeFocusPath(newPath);
        }

        return {
          navigationPath: ['Type'],
          preventDefault: true,
        };
      },
      {
        description: 'Navigate to previous sibling or up',
      }
    ),

    createCommand(
      'nav-right',
      'ArrowRight',
      '→',
      (context) => {
        const inductiveType = context.metadata?.inductiveType as TTerm | undefined;
        const typeFocusPath = context.metadata?.typeFocusPath as TermFocusPath | undefined;
        const setTypeFocusPath = context.metadata?.setTypeFocusPath as ((path: TermFocusPath) => void) | undefined;

        if (!inductiveType || typeFocusPath === undefined || !setTypeFocusPath) {
          return { preventDefault: true };
        }

        const newPath = navigateRight(inductiveType, typeFocusPath);
        if (newPath !== null) {
          setTypeFocusPath(newPath);
        }

        return {
          navigationPath: ['Type'],
          preventDefault: true,
        };
      },
      {
        description: 'Navigate to next sibling or up',
      }
    ),

    // 'w' - Wrap menu (then 'a' for arg/pi)
    createCommand(
      'wrap',
      'w',
      'Wrap',
      () => ({ navigationPath: ['Type', 'Wrap'], preventDefault: true }),
      {
        description: 'Wrap current term',
        children: [
          createCommand(
            'wrap-arg',
            'a',
            'Arg (Pi)',
            (context) => {
              const inductiveType = context.metadata?.inductiveType as TTerm | undefined;
              const typeFocusPath = context.metadata?.typeFocusPath as TermFocusPath | undefined;
              const setInductiveType = context.metadata?.setInductiveType as ((type: TTerm) => void) | undefined;
              const setTypeFocusPath = context.metadata?.setTypeFocusPath as ((path: TermFocusPath) => void) | undefined;

              if (!inductiveType || !setInductiveType || !setTypeFocusPath || typeFocusPath === undefined) {
                return { preventDefault: true };
              }

              // Get the currently focused term
              const focusedTerm = getTermAtPath(inductiveType, typeFocusPath);
              if (!focusedTerm) return { preventDefault: true };

              // Create new Pi: ?hole -> focusedTerm
              const holeId = freshHoleId();
              const hole = mkHole(holeId, mkType(0), []);
              const newPi = mkPi(hole, focusedTerm, '');

              // Replace focused term with the new Pi
              const newType = setTermAtPath(inductiveType, typeFocusPath, newPi);
              if (!newType) return { preventDefault: true };

              setInductiveType(newType);

              // Focus on the new hole (domain of the new Pi)
              setTypeFocusPath([...typeFocusPath, 'domain']);

              return {
                navigationPath: ['Type'],
                preventDefault: true,
              };
            },
            {
              description: 'Wrap as Pi argument (?hole -> current)',
            }
          ),
        ],
      }
    ),

    // 't' - Replace with Type_0
    createCommand(
      'replace-type',
      't',
      'Type_0',
      (context) => {
        const inductiveType = context.metadata?.inductiveType as TTerm | undefined;
        const typeFocusPath = context.metadata?.typeFocusPath as TermFocusPath | undefined;
        const setInductiveType = context.metadata?.setInductiveType as ((type: TTerm) => void) | undefined;

        if (!inductiveType || !setInductiveType || typeFocusPath === undefined) {
          return { preventDefault: true };
        }

        // Replace focused term with Type_0
        const newType = setTermAtPath(inductiveType, typeFocusPath, mkType(0));
        if (!newType) return { preventDefault: true };

        setInductiveType(newType);

        return {
          navigationPath: ['Type'],
          preventDefault: true,
        };
      },
      {
        description: 'Replace current term with Type_0',
      }
    ),
  ];
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
        children: createConstructorTypeEditingCommands(),
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
 * Commands for editing a constructor's type (reuses term navigation)
 */
function createConstructorTypeEditingCommands(): Command[] {
  return [
    // Arrow key navigation
    createCommand(
      'ctor-nav-up',
      'ArrowUp',
      '↑',
      (context) => {
        const typeFocusPath = context.metadata?.constructorTypeFocusPath as TermFocusPath | undefined;
        const setTypeFocusPath = context.metadata?.setConstructorTypeFocusPath as ((path: TermFocusPath) => void) | undefined;

        if (typeFocusPath === undefined || !setTypeFocusPath) {
          return { preventDefault: true };
        }

        const newPath = navigateUp(typeFocusPath);
        if (newPath !== null) {
          setTypeFocusPath(newPath);
        }

        return { preventDefault: true };
      },
      { description: 'Navigate up to parent' }
    ),

    createCommand(
      'ctor-nav-down',
      'ArrowDown',
      '↓',
      (context) => {
        const ctorType = context.metadata?.selectedConstructorType as TTerm | undefined;
        const typeFocusPath = context.metadata?.constructorTypeFocusPath as TermFocusPath | undefined;
        const setTypeFocusPath = context.metadata?.setConstructorTypeFocusPath as ((path: TermFocusPath) => void) | undefined;

        if (!ctorType || typeFocusPath === undefined || !setTypeFocusPath) {
          return { preventDefault: true };
        }

        const newPath = navigateDown(ctorType, typeFocusPath);
        if (newPath !== null) {
          setTypeFocusPath(newPath);
        }

        return { preventDefault: true };
      },
      { description: 'Navigate down to first child' }
    ),

    createCommand(
      'ctor-nav-left',
      'ArrowLeft',
      '←',
      (context) => {
        const ctorType = context.metadata?.selectedConstructorType as TTerm | undefined;
        const typeFocusPath = context.metadata?.constructorTypeFocusPath as TermFocusPath | undefined;
        const setTypeFocusPath = context.metadata?.setConstructorTypeFocusPath as ((path: TermFocusPath) => void) | undefined;

        if (!ctorType || typeFocusPath === undefined || !setTypeFocusPath) {
          return { preventDefault: true };
        }

        const newPath = navigateLeft(ctorType, typeFocusPath);
        if (newPath !== null) {
          setTypeFocusPath(newPath);
        }

        return { preventDefault: true };
      },
      { description: 'Navigate to previous sibling or up' }
    ),

    createCommand(
      'ctor-nav-right',
      'ArrowRight',
      '→',
      (context) => {
        const ctorType = context.metadata?.selectedConstructorType as TTerm | undefined;
        const typeFocusPath = context.metadata?.constructorTypeFocusPath as TermFocusPath | undefined;
        const setTypeFocusPath = context.metadata?.setConstructorTypeFocusPath as ((path: TermFocusPath) => void) | undefined;

        if (!ctorType || typeFocusPath === undefined || !setTypeFocusPath) {
          return { preventDefault: true };
        }

        const newPath = navigateRight(ctorType, typeFocusPath);
        if (newPath !== null) {
          setTypeFocusPath(newPath);
        }

        return { preventDefault: true };
      },
      { description: 'Navigate to next sibling or up' }
    ),

    // 'w' - Wrap menu
    createCommand(
      'ctor-wrap',
      'w',
      'Wrap',
      () => ({ preventDefault: true }),
      {
        description: 'Wrap current term',
        children: [
          createCommand(
            'ctor-wrap-arg',
            'a',
            'Arg (Pi)',
            (context) => {
              const ctorType = context.metadata?.selectedConstructorType as TTerm | undefined;
              const typeFocusPath = context.metadata?.constructorTypeFocusPath as TermFocusPath | undefined;
              const setCtorType = context.metadata?.setSelectedConstructorType as ((type: TTerm) => void) | undefined;
              const setTypeFocusPath = context.metadata?.setConstructorTypeFocusPath as ((path: TermFocusPath) => void) | undefined;

              if (!ctorType || !setCtorType || !setTypeFocusPath || typeFocusPath === undefined) {
                return { preventDefault: true };
              }

              const focusedTerm = getTermAtPath(ctorType, typeFocusPath);
              if (!focusedTerm) return { preventDefault: true };

              const holeId = freshHoleId();
              const hole = mkHole(holeId, mkType(0), []);
              const newPi = mkPi(hole, focusedTerm, '');

              const newType = setTermAtPath(ctorType, typeFocusPath, newPi);
              if (!newType) return { preventDefault: true };

              setCtorType(newType);
              setTypeFocusPath([...typeFocusPath, 'domain']);

              return { preventDefault: true };
            },
            { description: 'Wrap as Pi argument (?hole -> current)' }
          ),
        ],
      }
    ),

    // 't' - Replace with Type_0
    createCommand(
      'ctor-replace-type',
      't',
      'Type_0',
      (context) => {
        const ctorType = context.metadata?.selectedConstructorType as TTerm | undefined;
        const typeFocusPath = context.metadata?.constructorTypeFocusPath as TermFocusPath | undefined;
        const setCtorType = context.metadata?.setSelectedConstructorType as ((type: TTerm) => void) | undefined;

        if (!ctorType || !setCtorType || typeFocusPath === undefined) {
          return { preventDefault: true };
        }

        const newType = setTermAtPath(ctorType, typeFocusPath, mkType(0));
        if (!newType) return { preventDefault: true };

        setCtorType(newType);

        return { preventDefault: true };
      },
      { description: 'Replace current term with Type_0' }
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
        children: createTypeEditingCommands(),
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
