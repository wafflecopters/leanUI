import React, { useState } from 'react';
import type { CompiledBlock, CompileResult } from '../compiler/compile';
import { TextEditorDeclarationCard } from './TextEditorDeclarationCard';

const styles = {
  blockCard: {
    backgroundColor: '#161b22',
    borderTopWidth: '1px',
    borderRightWidth: '1px',
    borderBottomWidth: '1px',
    borderLeftWidth: '1px',
    borderStyle: 'solid',
    borderColor: '#30363d',
    borderRadius: '6px',
    marginBottom: '12px',
    overflow: 'hidden',
  },
  blockHeader: {
    padding: '8px 12px',
    backgroundColor: '#21262d',
    borderBottom: '1px solid #30363d',
    display: 'flex',
    alignItems: 'center',
    gap: '8px',
  },
  blockBadge: {
    padding: '2px 8px',
    borderRadius: '4px',
    fontSize: '11px',
    fontWeight: 600,
  },
  blockBadgeComment: {
    backgroundColor: 'rgba(110, 118, 129, 0.2)',
    color: '#6e7681',
  },
  blockBadgeError: {
    backgroundColor: 'rgba(248, 81, 73, 0.2)',
    color: '#f85149',
  },
  blockBody: {
    padding: '12px',
  },
  errorText: {
    color: '#f85149',
  },
};

function BlockCard(props: {
  header: React.ReactNode;
  body: React.ReactNode;
  initiallyExpanded?: boolean;
  hasError?: boolean;
}) {
  const [expanded, setExpanded] = useState(props.initiallyExpanded ?? true);

  return (
    <div
      style={{
        ...styles.blockCard,
        ...(props.hasError ? { borderLeftColor: '#f85149', borderLeftWidth: '3px' } : {}),
      }}
    >
      <div style={styles.blockHeader} onClick={() => setExpanded(e => !e)}>
        {props.header}
      </div>
      {expanded && <div style={styles.blockBody}>{props.body}</div>}
    </div>
  );
}

export function TextEditorCompiledBlock({
  block,
  showNamedArgsWithLabels,
  showNamedParamsWithBraces,
  definitions,
}: {
  block: CompiledBlock;
  showNamedArgsWithLabels: boolean;
  showNamedParamsWithBraces: boolean;
  definitions: CompileResult['definitions'];
}) {
  if (block.isComment) {
    return (
      <BlockCard
        header={<span style={{ ...styles.blockBadge, ...styles.blockBadgeComment }}>Comment</span>}
        body={<pre style={{ margin: 0, color: '#6e7681' }}>{block.sourceLines.join('\n')}</pre>}
        initiallyExpanded={false}
      />
    );
  }

  if (!block.parseSuccess) {
    return (
      <BlockCard
        header={<span style={{ ...styles.blockBadge, ...styles.blockBadgeError }}>Parse Error</span>}
        body={block.parseErrors.map((err, i) => (
          <div key={i} style={styles.errorText}>
            Line {err.line}, Col {err.col}: {err.message}
          </div>
        ))}
        initiallyExpanded={false}
        hasError={true}
      />
    );
  }

  if (!block.nameResolutionSuccess) {
    return (
      <BlockCard
        header={<span style={{ ...styles.blockBadge, ...styles.blockBadgeError }}>Name Error</span>}
        body={block.nameResolutionErrors.map((err, i) => (
          <div key={i} style={styles.errorText}>
            {err.message}
          </div>
        ))}
        initiallyExpanded={false}
        hasError={true}
      />
    );
  }

  return (
    <div style={styles.blockCard}>
      {block.declarations.map((decl, i) => (
        <TextEditorDeclarationCard
          key={i}
          declaration={decl}
          showNamedArgsWithLabels={showNamedArgsWithLabels}
          showNamedParamsWithBraces={showNamedParamsWithBraces}
          definitions={definitions}
        />
      ))}
    </div>
  );
}
