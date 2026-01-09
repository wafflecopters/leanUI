/**
 * SplitTreeViewer - Visual display of pattern matching case trees
 *
 * This component renders the split tree from totality checking as an
 * interactive, collapsible visualization showing:
 * - Which clauses handle which cases (Leaf nodes)
 * - Which cases are uncovered (Missing nodes)
 * - The branching structure on constructors (Split nodes)
 */

import React, { useState } from 'react';
import { SplitTree, SplitNode, LeafNode, MissingNode, formatMissingCase } from '../types/ttk-totality-check';

// ============================================================================
// Styles
// ============================================================================

const styles = {
  container: {
    fontFamily: 'monospace',
    fontSize: '12px',
    backgroundColor: '#161b22',
    border: '1px solid #30363d',
    borderRadius: '6px',
    padding: '12px',
    marginTop: '8px',
  } as React.CSSProperties,

  header: {
    display: 'flex',
    alignItems: 'center',
    justifyContent: 'space-between',
    cursor: 'pointer',
    userSelect: 'none',
    marginBottom: '8px',
  } as React.CSSProperties,

  headerTitle: {
    fontWeight: 600,
    color: '#c9d1d9',
    display: 'flex',
    alignItems: 'center',
    gap: '8px',
  } as React.CSSProperties,

  toggleIcon: {
    fontSize: '10px',
    color: '#8b949e',
    width: '12px',
  } as React.CSSProperties,

  treeContainer: {
    marginLeft: '4px',
    borderLeft: '1px solid #30363d',
    paddingLeft: '12px',
  } as React.CSSProperties,

  nodeRow: {
    display: 'flex',
    alignItems: 'center',
    padding: '2px 0',
    gap: '6px',
  } as React.CSSProperties,

  splitNode: {
    color: '#58a6ff',
    fontWeight: 500,
  } as React.CSSProperties,

  leafNode: {
    color: '#3fb950',
    display: 'flex',
    alignItems: 'center',
    gap: '6px',
  } as React.CSSProperties,

  missingNode: {
    color: '#f85149',
    display: 'flex',
    alignItems: 'center',
    gap: '6px',
  } as React.CSSProperties,

  branchLabel: {
    color: '#d2a8ff',
    fontWeight: 500,
  } as React.CSSProperties,

  defaultBranchLabel: {
    color: '#8b949e',
    fontStyle: 'italic',
  } as React.CSSProperties,

  impossibleBranchLabel: {
    color: '#8b949e',
    textDecoration: 'line-through',
    opacity: 0.7,
  } as React.CSSProperties,

  impossibleBadge: {
    backgroundColor: '#6e7681',
    color: '#ffffff',
    padding: '1px 6px',
    borderRadius: '10px',
    fontSize: '10px',
    fontWeight: 600,
  } as React.CSSProperties,

  clauseIndex: {
    backgroundColor: '#238636',
    color: '#ffffff',
    padding: '1px 6px',
    borderRadius: '10px',
    fontSize: '10px',
    fontWeight: 600,
  } as React.CSSProperties,

  missingBadge: {
    backgroundColor: '#da3633',
    color: '#ffffff',
    padding: '1px 6px',
    borderRadius: '10px',
    fontSize: '10px',
    fontWeight: 600,
  } as React.CSSProperties,

  missingPattern: {
    color: '#f85149',
    marginLeft: '4px',
  } as React.CSSProperties,

  icon: {
    width: '14px',
    textAlign: 'center' as const,
  } as React.CSSProperties,

  collapsibleBranch: {
    cursor: 'pointer',
  } as React.CSSProperties,

  legend: {
    display: 'flex',
    gap: '16px',
    marginBottom: '12px',
    paddingBottom: '8px',
    borderBottom: '1px solid #30363d',
    fontSize: '11px',
  } as React.CSSProperties,

  legendItem: {
    display: 'flex',
    alignItems: 'center',
    gap: '4px',
  } as React.CSSProperties,
};

// ============================================================================
// Component Props
// ============================================================================

interface SplitTreeViewerProps {
  tree: SplitTree;
  functionName?: string;
  /** Clause source snippets for display (index -> snippet) */
  clauseSnippets?: Map<number, string>;
}

// ============================================================================
// Sub-Components
// ============================================================================

interface TreeNodeProps {
  node: SplitTree;
  depth: number;
  functionName?: string;
  parentPath?: string[];
}

const TreeNode: React.FC<TreeNodeProps> = ({ node, depth, functionName, parentPath = [] }) => {
  const [isExpanded, setIsExpanded] = useState(depth < 3); // Auto-expand first 3 levels

  switch (node.tag) {
    case 'Leaf':
      return (
        <div style={styles.nodeRow}>
          <span style={styles.icon}>✓</span>
          <span style={styles.leafNode}>
            <span>Clause</span>
            <span style={styles.clauseIndex}>{node.clauseIndex + 1}</span>
          </span>
        </div>
      );

    case 'Missing':
      const missingDisplay = functionName
        ? formatMissingCase(functionName, node.patterns)
        : node.path.join(' → ') || '_';
      return (
        <div style={styles.nodeRow}>
          <span style={styles.icon}>✗</span>
          <span style={styles.missingNode}>
            <span style={styles.missingBadge}>MISSING</span>
            <code style={styles.missingPattern}>{missingDisplay}</code>
          </span>
        </div>
      );

    case 'Split':
      const branches = Array.from(node.branches.entries());
      const hasDefault = node.defaultBranch !== undefined;
      const impossibleBranches = node.impossibleBranches || [];
      const totalBranches = branches.length + (hasDefault ? 1 : 0);
      const hasImpossible = impossibleBranches.length > 0;

      return (
        <div>
          <div
            style={{ ...styles.nodeRow, ...styles.collapsibleBranch }}
            onClick={() => setIsExpanded(!isExpanded)}
          >
            <span style={styles.toggleIcon}>{isExpanded ? '▼' : '▶'}</span>
            <span style={styles.splitNode}>
              Split on arg {node.argIndex + 1}
            </span>
            <span style={{ color: '#8b949e', fontSize: '11px' }}>
              ({totalBranches} branch{totalBranches !== 1 ? 'es' : ''}
              {hasImpossible ? `, ${impossibleBranches.length} impossible` : ''})
            </span>
          </div>

          {isExpanded && (
            <div style={styles.treeContainer}>
              {branches.map(([ctorName, subtree]) => (
                <div key={ctorName}>
                  <div style={styles.nodeRow}>
                    <span style={styles.icon}>├</span>
                    <span style={styles.branchLabel}>{ctorName}</span>
                    <span style={{ color: '#8b949e' }}>→</span>
                  </div>
                  <div style={{ marginLeft: '20px' }}>
                    <TreeNode
                      node={subtree}
                      depth={depth + 1}
                      functionName={functionName}
                      parentPath={[...parentPath, ctorName]}
                    />
                  </div>
                </div>
              ))}

              {/* Show impossible branches (constructors that can't match due to type constraints) */}
              {impossibleBranches.map((ctorName) => (
                <div key={`impossible-${ctorName}`}>
                  <div style={styles.nodeRow}>
                    <span style={styles.icon}>├</span>
                    <span style={styles.impossibleBranchLabel}>{ctorName}</span>
                    <span style={styles.impossibleBadge}>impossible</span>
                  </div>
                </div>
              ))}

              {hasDefault && node.defaultBranch && (
                <div>
                  <div style={styles.nodeRow}>
                    <span style={styles.icon}>└</span>
                    <span style={styles.defaultBranchLabel}>_ (default)</span>
                    <span style={{ color: '#8b949e' }}>→</span>
                  </div>
                  <div style={{ marginLeft: '20px' }}>
                    <TreeNode
                      node={node.defaultBranch}
                      depth={depth + 1}
                      functionName={functionName}
                      parentPath={[...parentPath, '_']}
                    />
                  </div>
                </div>
              )}
            </div>
          )}
        </div>
      );
  }
};

// ============================================================================
// Summary Component
// ============================================================================

interface TreeSummaryProps {
  tree: SplitTree;
}

function countNodes(tree: SplitTree): { leaves: number; missing: number; splits: number; impossible: number } {
  switch (tree.tag) {
    case 'Leaf':
      return { leaves: 1, missing: 0, splits: 0, impossible: 0 };
    case 'Missing':
      return { leaves: 0, missing: 1, splits: 0, impossible: 0 };
    case 'Split': {
      let leaves = 0, missing = 0, splits = 1, impossible = tree.impossibleBranches?.length || 0;
      for (const subtree of tree.branches.values()) {
        const sub = countNodes(subtree);
        leaves += sub.leaves;
        missing += sub.missing;
        splits += sub.splits;
        impossible += sub.impossible;
      }
      if (tree.defaultBranch) {
        const sub = countNodes(tree.defaultBranch);
        leaves += sub.leaves;
        missing += sub.missing;
        splits += sub.splits;
        impossible += sub.impossible;
      }
      return { leaves, missing, splits, impossible };
    }
  }
}

const TreeSummary: React.FC<TreeSummaryProps> = ({ tree }) => {
  const counts = countNodes(tree);
  const isExhaustive = counts.missing === 0;

  return (
    <div style={styles.legend}>
      <div style={styles.legendItem}>
        <span style={{ color: '#3fb950' }}>✓</span>
        <span style={{ color: '#8b949e' }}>Covered: {counts.leaves}</span>
      </div>
      {counts.missing > 0 && (
        <div style={styles.legendItem}>
          <span style={{ color: '#f85149' }}>✗</span>
          <span style={{ color: '#f85149' }}>Missing: {counts.missing}</span>
        </div>
      )}
      {counts.impossible > 0 && (
        <div style={styles.legendItem}>
          <span style={{ color: '#8b949e' }}>⊘</span>
          <span style={{ color: '#8b949e' }}>Impossible: {counts.impossible}</span>
        </div>
      )}
      <div style={styles.legendItem}>
        <span style={{
          color: isExhaustive ? '#3fb950' : '#f85149',
          fontWeight: 600,
        }}>
          {isExhaustive ? 'Exhaustive ✓' : 'Non-exhaustive ✗'}
        </span>
      </div>
    </div>
  );
};

// ============================================================================
// Main Component
// ============================================================================

export const SplitTreeViewer: React.FC<SplitTreeViewerProps> = ({
  tree,
  functionName,
}) => {
  const [isExpanded, setIsExpanded] = useState(false);
  const counts = countNodes(tree);
  const isExhaustive = counts.missing === 0;

  // Don't show for trivial cases (0 or 1 clause)
  const totalCases = counts.leaves + counts.missing;
  if (totalCases < 2) {
    return null;
  }

  return (
    <div style={styles.container}>
      <div style={styles.header} onClick={() => setIsExpanded(!isExpanded)}>
        <div style={styles.headerTitle}>
          <span style={styles.toggleIcon}>{isExpanded ? '▼' : '▶'}</span>
          <span>Case Tree</span>
          <span style={{
            fontSize: '11px',
            fontWeight: 400,
            color: isExhaustive ? '#3fb950' : '#f85149',
          }}>
            ({counts.leaves} case{counts.leaves !== 1 ? 's' : ''} covered
            {counts.missing > 0 ? `, ${counts.missing} missing` : ''})
          </span>
        </div>
        <span style={{
          fontSize: '11px',
          color: isExhaustive ? '#3fb950' : '#f85149',
          fontWeight: 600,
        }}>
          {isExhaustive ? '✓' : '✗'}
        </span>
      </div>

      {isExpanded && (
        <>
          <TreeSummary tree={tree} />
          <TreeNode node={tree} depth={0} functionName={functionName} />
        </>
      )}
    </div>
  );
};

export default SplitTreeViewer;
