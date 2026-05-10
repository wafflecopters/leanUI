import React from 'react';
import type { TotalityResult } from '../compiler/compile';

const caseTreeStyles = {
  container: {
    marginTop: '12px',
    padding: '12px',
    backgroundColor: '#0d1117',
    borderRadius: '4px',
    border: '1px solid #30363d',
    fontSize: '12px',
    fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
  },
  header: {
    display: 'flex',
    alignItems: 'center',
    gap: '8px',
    marginBottom: '8px',
    color: '#8b949e',
    fontSize: '11px',
    fontWeight: 600,
    textTransform: 'uppercase' as const,
    letterSpacing: '0.5px',
  },
  exhaustiveBadge: {
    padding: '2px 6px',
    borderRadius: '3px',
    fontSize: '10px',
    fontWeight: 600,
  },
  exhaustiveYes: {
    backgroundColor: 'rgba(63, 185, 80, 0.2)',
    color: '#3fb950',
  },
  exhaustiveNo: {
    backgroundColor: 'rgba(248, 81, 73, 0.2)',
    color: '#f85149',
  },
  ctorName: {
    color: '#ffa657',
  },
  frozenCtorName: {
    color: '#6e7681',
    fontStyle: 'italic' as const,
  },
  leafClause: {
    color: '#7ee787',
  },
  uncovered: {
    color: '#f85149',
    fontStyle: 'italic' as const,
  },
  unreachableWarning: {
    marginTop: '8px',
    padding: '8px',
    backgroundColor: 'rgba(248, 81, 73, 0.1)',
    borderRadius: '4px',
    color: '#f85149',
    fontSize: '11px',
  },
};

function collectNoSplitLabels(tree: any, count: number): [string[], any] {
  const labels: string[] = [];
  let current = tree;
  for (let i = 0; i < count; i++) {
    if (current.tag === 'NoSplit') {
      labels.push(current.debugLabel);
      current = current.branch;
    } else {
      labels.push('_');
    }
  }
  return [labels, current];
}

function caseTreeRows(tree: any, frozenRemaining = 0): JSX.Element[] {
  if (tree.tag === 'Split') {
    const branches = Array.from(tree.branches.entries()) as Array<[string, any]>;
    return branches.map(([ctorName, subTree]) => {
      const arity = tree.ctorArities.get(ctorName) ?? 0;
      const [argLabels, remainingTree] = collectNoSplitLabels(subTree, arity);
      const ctorDisplay = arity === 0 ? ctorName : `(${ctorName} ${argLabels.join(' ')})`;
      const childRows = caseTreeRows(remainingTree, frozenRemaining);
      return (
        <tr key={ctorName}>
          <td><span style={caseTreeStyles.ctorName}>{ctorDisplay}</span></td>
          <td>{childRows.length > 0 && <table style={{ borderCollapse: 'collapse' }}><tbody>{childRows}</tbody></table>}</td>
        </tr>
      );
    });
  }

  if (tree.tag === 'NoSplit') {
    const childRows = caseTreeRows(tree.branch, frozenRemaining > 0 ? frozenRemaining - 1 : 0);
    const style = frozenRemaining > 0 ? caseTreeStyles.frozenCtorName : caseTreeStyles.ctorName;
    return [
      <tr key={tree.debugLabel}>
        <td><span style={style}>{tree.debugLabel}</span></td>
        <td>{childRows.length > 0 && <table style={{ borderCollapse: 'collapse' }}><tbody>{childRows}</tbody></table>}</td>
      </tr>,
    ];
  }

  if (tree.tag === 'Leaf') {
    return [<tr key={tree.clauseIndex}><td><span style={caseTreeStyles.leafClause}>→ clause {tree.clauseIndex}</span></td></tr>];
  }

  if (tree.tag === 'Uncovered') {
    return [<tr key="uncovered"><td><span style={caseTreeStyles.uncovered}>⚠ uncovered</span></td></tr>];
  }

  return [];
}

export function TextEditorCaseTree({ result }: { result: TotalityResult }) {
  if (!result.caseTree) return null;

  return (
    <div style={caseTreeStyles.container}>
      <div style={caseTreeStyles.header}>
        <span>Case Tree</span>
        <span style={{
          ...caseTreeStyles.exhaustiveBadge,
          ...(result.isExhaustive ? caseTreeStyles.exhaustiveYes : caseTreeStyles.exhaustiveNo),
        }}>
          {result.isExhaustive ? 'Exhaustive' : 'Non-exhaustive'}
        </span>
      </div>
      <table><tbody>{caseTreeRows(result.caseTree, result.frozenPositionCount ?? 0)}</tbody></table>
      {result.unreachableClauses.length > 0 && (
        <div style={caseTreeStyles.unreachableWarning}>
          Warning: Unreachable clause(s): {result.unreachableClauses.map(i => i.clauseIndex + 1).join(', ')}
        </div>
      )}
    </div>
  );
}
