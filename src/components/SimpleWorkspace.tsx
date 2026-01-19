/**
 * SimpleWorkspace: A clean, minimal workspace component using the new architecture.
 *
 * This demonstrates the simplified approach:
 * - EditableTerm for state management
 * - DefinitionFocus for navigation
 * - Minimal React state (just EditableTerm + focus)
 * - Flux-like updates via dispatch
 */

import React from 'react';
import { EditableTerm, TTerm, createRootTermDefinition, mkType, prettyPrint } from '../compiler/surface';
import { useEditableTerm } from '../hooks/useEditableTerm';
import { useDefinitionNavigation } from '../hooks/useDefinitionNavigation';

// ============================================================================
// Component
// ============================================================================

export interface SimpleWorkspaceProps {
  /** Initial term to edit */
  initialTerm?: EditableTerm;
}

export function SimpleWorkspace({ initialTerm }: SimpleWorkspaceProps) {
  // Initialize with a default term if none provided
  const defaultTerm = React.useMemo(() => {
    if (initialTerm) return initialTerm;

    // Create a simple proof: (a: Type) → (b: Type) → ?goal
    const typeSort = mkType(0);
    const def = createRootTermDefinition('example', [['a', typeSort], ['b', typeSort]], typeSort, 'proof');
    return EditableTerm.fromTermDefinition(def);
  }, [initialTerm]);

  // Term state management
  const { term, dispatch } = useEditableTerm(defaultTerm);

  // Navigation state management
  const navigation = useDefinitionNavigation({
    numHypotheses: term.hypotheses.length,
    onFocusChange: (focus) => {
      console.log('Focus changed:', focus);
    },
  });

  // Render helpers
  const renderHypothesis = (hyp: [string, TTerm], index: number) => {
    const isFocused =
      navigation.focus?.tag === 'hypothesis' &&
      navigation.focus.hypothesisIndex === index;

    return (
      <div
        key={index}
        style={{
          padding: '8px',
          margin: '4px 0',
          border: isFocused ? '2px solid blue' : '1px solid #ccc',
          borderRadius: '4px',
          backgroundColor: isFocused ? '#e6f3ff' : 'white',
          cursor: 'pointer',
        }}
        onClick={() => navigation.focusHypothesis(index)}
      >
        <div style={{ display: 'flex', gap: '8px', alignItems: 'center' }}>
          <span style={{ fontWeight: 'bold', color: '#666' }}>{index}.</span>
          <span style={{ fontFamily: 'monospace', color: '#0066cc' }}>{hyp[0]}</span>
          <span style={{ color: '#999' }}>:</span>
          <span style={{ fontFamily: 'monospace' }}>{prettyPrint(hyp[1])}</span>
        </div>
        {isFocused && (
          <div style={{ marginTop: '4px', fontSize: '12px', color: '#666' }}>
            <button
              onClick={(e) => {
                e.stopPropagation();
                try {
                  dispatch({ type: 'removeHypothesis', index });
                } catch (err) {
                  alert(err instanceof Error ? err.message : String(err));
                }
              }}
              style={{ marginRight: '4px' }}
            >
              Remove
            </button>
          </div>
        )}
      </div>
    );
  };

  const renderGoal = () => {
    const isFocused = navigation.focus?.tag === 'goal';

    return (
      <div
        style={{
          padding: '12px',
          margin: '8px 0',
          border: isFocused ? '2px solid green' : '1px solid #ccc',
          borderRadius: '4px',
          backgroundColor: isFocused ? '#e6ffe6' : 'white',
          cursor: 'pointer',
        }}
        onClick={() => navigation.focusGoal()}
      >
        <div style={{ fontWeight: 'bold', marginBottom: '4px', color: '#666' }}>
          Goal ({navigation.currentSection === 'goal' ? 'focused' : 'unfocused'})
        </div>
        <div style={{ fontFamily: 'monospace', fontSize: '14px' }}>
          {prettyPrint(term.goal)}
        </div>
      </div>
    );
  };

  const renderBody = () => {
    const isFocused = navigation.focus?.tag === 'body';

    return (
      <div
        style={{
          padding: '12px',
          margin: '8px 0',
          border: isFocused ? '2px solid purple' : '1px solid #ccc',
          borderRadius: '4px',
          backgroundColor: isFocused ? '#f3e6ff' : 'white',
          cursor: 'pointer',
        }}
        onClick={() => navigation.focusBody()}
      >
        <div style={{ fontWeight: 'bold', marginBottom: '4px', color: '#666' }}>
          Body ({navigation.currentSection === 'body' ? 'focused' : 'unfocused'})
        </div>
        <div style={{ fontFamily: 'monospace', fontSize: '14px' }}>
          {prettyPrint(term.body)}
        </div>
      </div>
    );
  };

  return (
    <div style={{ padding: '20px', maxWidth: '800px', margin: '0 auto' }}>
      <h1>Simple Workspace (New Architecture)</h1>

      <div style={{ marginBottom: '20px', padding: '10px', backgroundColor: '#f5f5f5', borderRadius: '4px' }}>
        <div><strong>Term:</strong> {term.name}</div>
        <div><strong>Focus:</strong> {navigation.getFocusDescription()}</div>
        <div style={{ fontSize: '12px', color: '#666', marginTop: '4px' }}>
          Use ↑/↓ or j/k to navigate, 0-9 to select by number, Escape to clear focus
        </div>
      </div>

      <section style={{ marginBottom: '20px' }}>
        <h2 style={{ fontSize: '18px', marginBottom: '8px' }}>
          Hypotheses ({term.hypotheses.length})
        </h2>
        {term.hypotheses.length === 0 ? (
          <div style={{ padding: '8px', color: '#999', fontStyle: 'italic' }}>
            No hypotheses
          </div>
        ) : (
          term.hypotheses.map((hyp, i) => renderHypothesis(hyp, i))
        )}
        <button
          onClick={() => {
            const name = prompt('Hypothesis name:');
            if (!name) return;
            // For now, just add a Type hole
            const typeSort = mkType(0);
            dispatch({
              type: 'addHypothesis',
              index: term.hypotheses.length,
              name,
              hypothesisType: typeSort,
            });
          }}
          style={{ marginTop: '8px' }}
        >
          Add Hypothesis
        </button>
      </section>

      <section style={{ marginBottom: '20px' }}>
        <h2 style={{ fontSize: '18px', marginBottom: '8px' }}>Goal</h2>
        {renderGoal()}
      </section>

      <section style={{ marginBottom: '20px' }}>
        <h2 style={{ fontSize: '18px', marginBottom: '8px' }}>Body (Proof Term)</h2>
        {renderBody()}
      </section>

      <section style={{ marginTop: '30px', padding: '10px', backgroundColor: '#f9f9f9', borderRadius: '4px' }}>
        <h3 style={{ fontSize: '16px', marginBottom: '8px' }}>Debug Info</h3>
        <pre style={{ fontSize: '11px', overflow: 'auto' }}>
          {JSON.stringify(
            {
              name: term.name,
              numHypotheses: term.hypotheses.length,
              hypotheses: term.hypotheses.map(([name, type]) => [
                name,
                prettyPrint(type),
              ]),
              goal: prettyPrint(term.goal),
              body: prettyPrint(term.body),
            },
            null,
            2
          )}
        </pre>
      </section>
    </div>
  );
}
