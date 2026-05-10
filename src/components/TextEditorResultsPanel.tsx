import React from 'react';
import type { CompileResult } from '../compiler/compile';
import { getCompileResultsErrorCount } from './textEditorResultsModel';
import { TextEditorCompiledBlock } from './TextEditorCompiledBlock';
import { TextEditorRenderOptions } from './TextEditorRenderOptions';

const styles = {
  resultsSection: {
    flex: 1,
    minHeight: 0,
    display: 'flex',
    flexDirection: 'column' as const,
    overflow: 'hidden',
  },
  sectionHeader: {
    padding: '8px 16px',
    fontSize: '11px',
    fontWeight: 600,
    color: '#8b949e',
    textTransform: 'uppercase' as const,
    letterSpacing: '0.5px',
    backgroundColor: '#161b22',
    borderBottom: '1px solid #30363d',
  },
  resultsContent: {
    flex: 1,
    overflow: 'auto',
    padding: '16px',
    fontFamily: "'JetBrains Mono', 'Fira Code', 'Consolas', monospace",
    fontSize: '13px',
  },
};

export function TextEditorResultsPanel({
  compileResult,
  showNamedArgsWithLabels,
  showNamedParamsWithBraces,
  setShowNamedArgsWithLabels,
  setShowNamedParamsWithBraces,
}: {
  compileResult: CompileResult;
  showNamedArgsWithLabels: boolean;
  showNamedParamsWithBraces: boolean;
  setShowNamedArgsWithLabels: React.Dispatch<React.SetStateAction<boolean>>;
  setShowNamedParamsWithBraces: React.Dispatch<React.SetStateAction<boolean>>;
}) {
  return (
    <div style={styles.resultsSection}>
      <div style={styles.sectionHeader}>
        <span>
          Compile Results
          {!compileResult.success && (
            <span style={{ marginLeft: '8px', color: '#f85149' }}>
              ({getCompileResultsErrorCount(compileResult)} errors)
            </span>
          )}
        </span>
        <TextEditorRenderOptions
          showNamedArgsWithLabels={showNamedArgsWithLabels}
          showNamedParamsWithBraces={showNamedParamsWithBraces}
          setShowNamedArgsWithLabels={setShowNamedArgsWithLabels}
          setShowNamedParamsWithBraces={setShowNamedParamsWithBraces}
        />
      </div>

      <div style={styles.resultsContent}>
        {compileResult.blocks.map((block, i) => (
          <TextEditorCompiledBlock
            key={i}
            block={block}
            showNamedArgsWithLabels={showNamedArgsWithLabels}
            showNamedParamsWithBraces={showNamedParamsWithBraces}
            definitions={compileResult.definitions}
          />
        ))}
      </div>
    </div>
  );
}
