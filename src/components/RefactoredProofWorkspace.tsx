/**
 * RefactoredProofWorkspace: Clean implementation using new architecture
 *
 * This replaces EnhancedProofWorkspace with:
 * - EditableTerm for state management
 * - DefinitionFocus for navigation
 * - Minimal React state
 * - Dispatch-based updates
 */

import { useCallback, useEffect, useMemo } from 'react';
import {
  Assumption,
  parseExpressionToAST,
} from '../types/enhanced-focus';
import {
  TTerm,
  EditableTerm,
  createRootTermDefinition,
  mkProp,
  mkType,
  prettyPrint,
  flattenLetBindings
} from '../types/tt-core';
import {
  expressionNodeToTTerm,
} from '../types/tt-bridge';
import { useEditableTerm } from '../hooks/useEditableTerm';
import { useDefinitionNavigation } from '../hooks/useDefinitionNavigation';
import { NavigationProvider, useNavigation } from '../contexts/NavigationContext';
import { NavigationFooter, NavigationFooterSpacer } from './NavigationFooter';
import { NavigationEditableTextField } from './NavigationEditableTextField';
import { createApplicationCommandTree } from '../config/navigationCommands';

// ============================================================================
// Helper Functions
// ============================================================================

/**
 * Convert a TT Pi-binder to a UI Assumption.
 */
function piBinderToAssumption([name, type]: [string, TTerm], index: number): Assumption {
  let typeStr = prettyPrint(type);

  return {
    id: `hyp_${index}`,
    name,
    type: {
      id: `type-hyp_${index}`,
      type: 'variable' as const,
      raw: typeStr,
      children: [],
    },
    description: `Hypothesis: ${name} has type ${typeStr}`,
    introducedBy: 'user'
  };
}

// Removed assumptionToPiBinder - not needed in refactored version

// ============================================================================
// Main Component
// ============================================================================

function RefactoredProofWorkspaceInner() {
  // ============================================================================
  // NEW ARCHITECTURE: Single EditableTerm as source of truth
  // ============================================================================

  // Initialize with empty workspace
  const initialTerm = useMemo(() => {
    const def = createRootTermDefinition('_root', [], mkProp(), 'proof', []);
    return EditableTerm.fromTermDefinition(def);
  }, []);

  const { term, dispatch } = useEditableTerm(initialTerm, {
    enableHistory: true,
    onChange: (newTerm) => {
      console.log('Term updated:', newTerm);
    }
  });

  // Navigation state
  const defNav = useDefinitionNavigation({
    numHypotheses: term.hypotheses.length,
    enableKeyboard: false, // We'll use NavigationContext for keyboard
    onFocusChange: (focus) => {
      console.log('Focus changed:', focus);
    }
  });

  // Get navigation context for integration with existing command system
  const navigation = useNavigation();

  // ============================================================================
  // DERIVED STATE: Convert TT to UI
  // ============================================================================

  // Convert hypotheses to Assumptions for UI
  const assumptions = useMemo((): Assumption[] => {
    return term.hypotheses.map((hyp, i) => piBinderToAssumption(hyp, i));
  }, [term.hypotheses]);

  // Extract let-bindings from body (for display)
  const letBindings = useMemo((): Array<[string, TTerm, TTerm]> => {
    return flattenLetBindings(term.body);
  }, [term.body]);

  // ============================================================================
  // UI STATE (minimal - only for tracking which editor is shown)
  // ============================================================================

  // No local state needed! Navigation path determines what's shown

  // ============================================================================
  // COMMAND HANDLERS (using dispatch)
  // ============================================================================

  const handleAddHypothesis = useCallback((value: string) => {
    // Expected format: "name : type" (e.g., "a : Type" or "p : Prop")
    const parts = value.split(':').map(s => s.trim());
    if (parts.length !== 2) {
      alert('Format should be: name : type');
      return;
    }

    const [name, typeStr] = parts;

    // Parse type string to TTerm
    const typeTerm = typeStr === 'Type' ? mkType(1) :
                     typeStr === 'Prop' ? mkProp() :
                     { tag: 'Const' as const, name: typeStr, type: mkProp() };

    dispatch({
      type: 'addHypothesis',
      index: term.hypotheses.length,
      name,
      hypothesisType: typeTerm
    });
  }, [dispatch, term.hypotheses.length]);

  const handleDeleteHypothesis = useCallback((index: number) => {
    try {
      dispatch({ type: 'removeHypothesis', index });
    } catch (error) {
      alert(error instanceof Error ? error.message : String(error));
    }
  }, [dispatch]);

  const handleSetGoal = useCallback((value: string) => {
    try {
      // Parse goal expression
      const exprNode = parseExpressionToAST(value);
      const goalTerm = expressionNodeToTTerm(exprNode, new Map());

      dispatch({ type: 'updateGoal', goal: goalTerm });
    } catch (error) {
      alert(`Failed to parse goal: ${error instanceof Error ? error.message : String(error)}`);
    }
  }, [dispatch]);

  // ============================================================================
  // SETUP COMMAND TREE
  // ============================================================================

  useEffect(() => {
    const commandTree = createApplicationCommandTree();
    navigation.setCommandTree(commandTree);
    // No metadata needed! Navigation path controls everything
  }, [navigation]);

  // ============================================================================
  // RENDERING
  // ============================================================================

  const focusedOnHypothesis = defNav.focus?.tag === 'hypothesis' ? defNav.focus.hypothesisIndex : null;
  const focusedOnGoal = defNav.focus?.tag === 'goal';
  const focusedOnBody = defNav.focus?.tag === 'body';

  // Check navigation path to see which editors are shown
  const navPath = navigation.state.navigationPath;
  const showEditGoal = navPath.includes('Goals') && navPath.includes('Editor');
  const showAddHypothesis = navPath.includes('Hypotheses') && navPath.includes('Editor');

  // Debug logging
  console.log('Navigation path:', navPath);
  console.log('showEditGoal:', showEditGoal);
  console.log('showAddHypothesis:', showAddHypothesis);

  return (
    <div style={{ padding: '20px', maxWidth: '1200px', margin: '0 auto' }}>
      <h1>Proof Workspace (Refactored)</h1>

      {/* Status Bar */}
      <div style={{
        marginBottom: '20px',
        padding: '10px',
        backgroundColor: '#f5f5f5',
        borderRadius: '4px',
        fontSize: '14px'
      }}>
        <div><strong>Focus:</strong> {defNav.getFocusDescription()}</div>
        <div><strong>Hypotheses:</strong> {term.hypotheses.length}</div>
        <div><strong>Goal:</strong> {prettyPrint(term.goal)}</div>
      </div>

      {/* Hypotheses Section */}
      <section style={{ marginBottom: '30px' }}>
        <h2 style={{
          fontSize: '20px',
          marginBottom: '12px',
          borderBottom: '2px solid #0066cc',
          paddingBottom: '8px'
        }}>
          Hypotheses
        </h2>

        {assumptions.length === 0 ? (
          <div style={{ padding: '12px', color: '#999', fontStyle: 'italic' }}>
            No hypotheses yet
          </div>
        ) : (
          assumptions.map((_assumption, i) => {
            const isFocused = focusedOnHypothesis === i;
            const [name, type] = term.hypotheses[i];

            return (
              <div
                key={i}
                style={{
                  padding: '12px',
                  margin: '8px 0',
                  border: isFocused ? '2px solid blue' : '1px solid #ccc',
                  borderRadius: '4px',
                  backgroundColor: isFocused ? '#e6f3ff' : 'white',
                  cursor: 'pointer'
                }}
                onClick={() => defNav.focusHypothesis(i)}
              >
                <div style={{ display: 'flex', gap: '12px', alignItems: 'center' }}>
                  <span style={{ fontWeight: 'bold', color: '#666', minWidth: '30px' }}>
                    {i}.
                  </span>
                  <span style={{ fontFamily: 'monospace', color: '#0066cc', fontWeight: 'bold' }}>
                    {name}
                  </span>
                  <span style={{ color: '#999' }}>:</span>
                  <span style={{ fontFamily: 'monospace' }}>
                    {prettyPrint(type)}
                  </span>
                </div>
                {isFocused && (
                  <div style={{ marginTop: '8px' }}>
                    <button
                      onClick={(e) => {
                        e.stopPropagation();
                        handleDeleteHypothesis(i);
                      }}
                      style={{
                        padding: '4px 12px',
                        fontSize: '12px',
                        backgroundColor: '#dc3545',
                        color: 'white',
                        border: 'none',
                        borderRadius: '4px',
                        cursor: 'pointer'
                      }}
                    >
                      Remove
                    </button>
                  </div>
                )}
              </div>
            );
          })
        )}

        {/* Add Hypothesis Form */}
        {showAddHypothesis && (
          <NavigationEditableTextField
            label="Add Hypothesis"
            placeholder="name : type (e.g., a : Type)"
            onSet={handleAddHypothesis}
            multiline={false}
          />
        )}
      </section>

      {/* Goal Section */}
      <section style={{ marginBottom: '30px' }}>
        <h2 style={{
          fontSize: '20px',
          marginBottom: '12px',
          borderBottom: '2px solid #28a745',
          paddingBottom: '8px'
        }}>
          Goal
        </h2>

        <div
          style={{
            padding: '16px',
            border: focusedOnGoal ? '2px solid green' : '1px solid #ccc',
            borderRadius: '4px',
            backgroundColor: focusedOnGoal ? '#e6ffe6' : 'white',
            cursor: 'pointer',
            fontFamily: 'monospace',
            fontSize: '16px'
          }}
          onClick={() => defNav.focusGoal()}
        >
          {prettyPrint(term.goal)}
        </div>

        {/* Edit Goal Form */}
        {showEditGoal && (
          <NavigationEditableTextField
            label="Set Goal"
            placeholder="e.g., a + b = b + a"
            onSet={handleSetGoal}
            multiline={false}
          />
        )}
      </section>

      {/* Body Section */}
      <section style={{ marginBottom: '30px' }}>
        <h2 style={{
          fontSize: '20px',
          marginBottom: '12px',
          borderBottom: '2px solid #6f42c1',
          paddingBottom: '8px'
        }}>
          Proof Body
        </h2>

        <div
          style={{
            padding: '16px',
            border: focusedOnBody ? '2px solid purple' : '1px solid #ccc',
            borderRadius: '4px',
            backgroundColor: focusedOnBody ? '#f3e6ff' : 'white',
            cursor: 'pointer'
          }}
          onClick={() => defNav.focusBody()}
        >
          <h3 style={{ fontSize: '14px', marginBottom: '8px', color: '#666' }}>
            Let-Bindings ({letBindings.length})
          </h3>
          {letBindings.length === 0 ? (
            <div style={{ fontStyle: 'italic', color: '#999' }}>No let-bindings yet</div>
          ) : (
            letBindings.map(([name, type, value], i) => (
              <div
                key={i}
                style={{
                  marginBottom: '8px',
                  padding: '8px',
                  backgroundColor: '#f5f5f5',
                  borderRadius: '4px',
                  fontFamily: 'monospace',
                  fontSize: '14px'
                }}
              >
                <div><strong>let</strong> {name} : {prettyPrint(type)} :=</div>
                <div style={{ marginLeft: '20px', marginTop: '4px' }}>
                  {prettyPrint(value)}
                </div>
              </div>
            ))
          )}

          <div style={{ marginTop: '12px', fontSize: '14px', color: '#666' }}>
            <strong>Final term:</strong>
          </div>
          <div style={{
            marginTop: '4px',
            padding: '8px',
            backgroundColor: '#fff8e1',
            borderRadius: '4px',
            fontFamily: 'monospace',
            fontSize: '14px'
          }}>
            {prettyPrint(term.body)}
          </div>
        </div>
      </section>

      <NavigationFooterSpacer>
        <div />
      </NavigationFooterSpacer>
      <NavigationFooter />
    </div>
  );
}

export function RefactoredProofWorkspace() {
  return (
    <NavigationProvider>
      <RefactoredProofWorkspaceInner />
    </NavigationProvider>
  );
}
