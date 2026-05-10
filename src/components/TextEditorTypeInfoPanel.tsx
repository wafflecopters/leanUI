import React from 'react';
import { prettyPrint as prettyPrintTTK } from '../compiler/kernel';
import type { CursorInfoAtPosition } from './textEditorModel';

const styles = {
  panel: {
    height: '120px',
    flexShrink: 0,
    borderBottom: '1px solid #30363d',
    backgroundColor: '#161b22',
    padding: '8px 16px',
    fontFamily: "'JetBrains Mono', 'Fira Code', 'Consolas', monospace",
    fontSize: '12px',
    color: '#c9d1d9',
    overflow: 'auto',
  },
  label: {
    color: '#8b949e',
    fontSize: '10px',
    fontWeight: 600 as const,
    textTransform: 'uppercase' as const,
    letterSpacing: '0.5px',
    marginBottom: '2px',
  },
  value: {
    color: '#79c0ff',
    marginBottom: '6px',
  },
  context: {
    color: '#c9d1d9',
    marginBottom: '2px',
  },
  contextName: {
    color: '#d2a8ff',
  },
  contextType: {
    color: '#79c0ff',
  },
  empty: {
    color: '#484f58',
  },
};

function renderTacticGoals(typeInfoAtCursor: Extract<CursorInfoAtPosition, { kind: 'tactic' }>) {
  if (typeInfoAtCursor.goalStates.length === 0) {
    return <div style={styles.value}>No goals (proof complete)</div>;
  }

  return typeInfoAtCursor.goalStates.map((goal, idx) => {
    const contextNames = goal.hypotheses.map(h => h.name);

    return (
      <div key={goal.id} style={{ marginBottom: idx < typeInfoAtCursor.goalStates.length - 1 ? '12px' : '0' }}>
        {(typeInfoAtCursor.goalStates.length > 1 || goal.caseTag) && (
          <div style={styles.label}>
            {typeInfoAtCursor.goalStates.length > 1 && `Goal ${idx + 1}/${typeInfoAtCursor.goalStates.length}`}
            {typeInfoAtCursor.goalStates.length > 1 && goal.caseTag && ' '}
            {goal.caseTag && `(${goal.caseTag})`}
          </div>
        )}

        {goal.hypotheses.length > 0 && (
          <div style={{ marginTop: (typeInfoAtCursor.goalStates.length > 1 || goal.caseTag) ? '8px' : '0' }}>
            <div style={styles.label}>Hypotheses</div>
            {goal.hypotheses.map((hyp, i) => (
              <div key={i} style={styles.context}>
                <span style={styles.contextName}>{hyp.name}</span>
                <span style={{ color: '#8b949e' }}> : </span>
                <span style={styles.contextType}>
                  {prettyPrintTTK(hyp.type, contextNames.slice(0, i), new Map())}
                </span>
              </div>
            ))}
          </div>
        )}

        <div style={{ marginTop: '8px' }}>
          <div style={styles.label}>Goal</div>
          <span style={styles.value}>
            {prettyPrintTTK(goal.target, contextNames, new Map())}
          </span>
        </div>
      </div>
    );
  });
}

export function TextEditorTypeInfoPanel({
  typeInfoAtCursor,
}: {
  typeInfoAtCursor: CursorInfoAtPosition | undefined;
}) {
  return (
    <div style={styles.panel}>
      {typeInfoAtCursor ? (
        <>
          {typeInfoAtCursor.kind === 'term' && (
            <>
              <div>
                <span style={styles.value}>
                  {typeInfoAtCursor.expression
                    ? `${typeInfoAtCursor.expression} : ${typeInfoAtCursor.info.prettyType}`
                    : typeInfoAtCursor.info.prettyType}
                </span>
              </div>
              {typeInfoAtCursor.info.expectedType &&
                typeInfoAtCursor.info.surfacePath.includes('clauses[') && (
                  <div>
                    <span style={styles.label}>Expected </span>
                    <span style={styles.value}>{typeInfoAtCursor.info.expectedType}</span>
                  </div>
                )}
              {typeInfoAtCursor.info.context.length > 0 && (
                <div>
                  <div style={styles.label}>Context</div>
                  {typeInfoAtCursor.info.context.map((entry, i) => (
                    <div key={i} style={styles.context}>
                      <span style={styles.contextName}>{entry.name}</span>
                      <span style={{ color: '#8b949e' }}> : </span>
                      <span style={styles.contextType}>{entry.type}</span>
                    </div>
                  ))}
                </div>
              )}
            </>
          )}

          {typeInfoAtCursor.kind === 'tactic' && renderTacticGoals(typeInfoAtCursor)}
        </>
      ) : (
        <span style={styles.empty}>Move cursor over an expression or tactic to see info</span>
      )}
    </div>
  );
}
