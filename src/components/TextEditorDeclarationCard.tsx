import React, { useCallback, useMemo, useState } from 'react';
import type { CompiledDeclaration } from '../compiler/compile';
import {
  prettyPrintFormatted,
  type NamedArgMap,
  type PrettyPrintOptions,
  type TTKTerm,
} from '../compiler/kernel';
import { createNamedArgLookup, type DefinitionsMap } from '../compiler/term';
import { TextEditorCaseTree } from './TextEditorCaseTree';
import {
  extractParamIndexInfo,
  getDeclarationStatusSummary,
} from './textEditorResultsModel';

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
  blockBody: {
    padding: '12px',
  },
  blockBadge: {
    padding: '2px 8px',
    borderRadius: '4px',
    fontSize: '11px',
    fontWeight: 600,
  },
  blockBadgeInductive: {
    backgroundColor: 'rgba(136, 198, 190, 0.2)',
    color: '#88c6be',
  },
  blockBadgeTerm: {
    backgroundColor: 'rgba(88, 166, 255, 0.2)',
    color: '#58a6ff',
  },
  declName: {
    color: '#e6edf3',
    fontWeight: 600,
    marginBottom: '4px',
  },
  typeRow: {
    display: 'flex',
    gap: '8px',
    marginBottom: '4px',
  },
  typeLabel: {
    color: '#8b949e',
    minWidth: '50px',
  },
  typeValue: {
    color: '#7ee787',
  },
  valueValue: {
    color: '#d2a8ff',
    whiteSpace: 'pre-wrap' as const,
  },
  ctorRow: {
    marginLeft: '16px',
    marginBottom: '2px',
  },
  ctorName: {
    color: '#ffa657',
  },
  projectionName: {
    color: '#58a6ff',
  },
  errorText: {
    color: '#f85149',
  },
  warningText: {
    color: '#d29922',
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
    <div style={{
      ...styles.blockCard,
      ...(props.hasError ? { borderLeftColor: '#f85149', borderLeftWidth: '3px' } : {}),
    }}>
      <div style={styles.blockHeader} onClick={() => setExpanded((value) => !value)}>
        {props.header}
      </div>
      {expanded && <div style={styles.blockBody}>{props.body}</div>}
    </div>
  );
}

export function TextEditorDeclarationCard({
  declaration,
  showNamedArgsWithLabels,
  showNamedParamsWithBraces,
  definitions,
}: {
  declaration: CompiledDeclaration;
  showNamedArgsWithLabels: boolean;
  showNamedParamsWithBraces: boolean;
  definitions: DefinitionsMap;
}) {
  const namedArgLookup = useMemo(() => createNamedArgLookup(definitions), [definitions]);
  const paramIndexInfo = declaration.kind === 'inductive'
    ? extractParamIndexInfo(declaration.kernelType, declaration.indexPositions)
    : [];
  const statusSummary = getDeclarationStatusSummary(declaration);

  const getPrettyType = useCallback((kernelType: TTKTerm | undefined, namedArgMap?: NamedArgMap) => {
    if (!kernelType) return undefined;
    const options: PrettyPrintOptions = {
      namedArgLookup,
      showNamedArgsWithLabels,
      signatureNamedArgMap: showNamedParamsWithBraces ? namedArgMap : undefined,
    };
    return prettyPrintFormatted(kernelType, [], undefined, options);
  }, [namedArgLookup, showNamedArgsWithLabels, showNamedParamsWithBraces]);

  const getPrettyValue = useCallback((kernelValue: TTKTerm | undefined) => {
    if (!kernelValue) return undefined;
    const options: PrettyPrintOptions = { namedArgLookup, showNamedArgsWithLabels };
    return prettyPrintFormatted(kernelValue, [], undefined, options);
  }, [namedArgLookup, showNamedArgsWithLabels]);

  return (
    <BlockCard
      initiallyExpanded={declaration.checkSuccess === false}
      hasError={declaration.checkSuccess === false}
      header={
        <>
          <span style={{
            ...styles.blockBadge,
            ...(declaration.kind === 'inductive' ? styles.blockBadgeInductive : styles.blockBadgeTerm),
          }}>
            {declaration.kind === 'inductive' ? 'Inductive' : 'Term'}
          </span>
          {declaration.name && <span style={styles.declName}>{declaration.name}</span>}
          {paramIndexInfo.length > 0 && (
            <span style={{ marginLeft: '12px', fontSize: '11px', color: '#8b949e' }}>
              {paramIndexInfo.map((info, index) => (
                <span key={index} style={{ marginRight: '8px' }}>
                  <span style={{ color: info.isIndex ? '#f0883e' : '#7ee787' }}>
                    [{info.isIndex ? 'index' : 'param'} {info.name} : {info.type}]
                  </span>
                </span>
              ))}
            </span>
          )}
          <span
            style={{
              marginLeft: 'auto',
              fontSize: '12px',
              color: statusSummary.kind === 'success'
                ? '#3fb950'
                : statusSummary.kind === 'warning'
                  ? '#d29922'
                  : '#f85149',
            }}
          >
            {statusSummary.text}
          </span>
        </>
      }
      body={
        <>
          {declaration.kernelType && (
            <div style={styles.typeRow}>
              <span style={styles.typeLabel}>Type:</span>
              <span style={styles.typeValue}>
                {getPrettyType(declaration.kernelType, declaration.name ? namedArgLookup(declaration.name) : undefined)}
              </span>
            </div>
          )}
          {declaration.kernelValue && (
            <div style={styles.typeRow}>
              <span style={styles.typeLabel}>Value:</span>
              <span style={styles.valueValue}>{getPrettyValue(declaration.kernelValue)}</span>
            </div>
          )}
          {declaration.kernelConstructors && declaration.kernelConstructors.length > 0 && (
            <div>
              <div style={{ ...styles.typeLabel, marginBottom: '4px' }}>Constructors:</div>
              {declaration.kernelConstructors.map((ctor, index) => (
                <div key={index} style={styles.ctorRow}>
                  <span style={styles.ctorName}>{ctor.name}</span>
                  <span style={{ color: '#8b949e' }}> : </span>
                  <span style={styles.typeValue}>{getPrettyType(ctor.type, ctor.namedArgMap)}</span>
                </div>
              ))}
            </div>
          )}
          {declaration.prettyProjections && declaration.prettyProjections.length > 0 && (
            <div style={{ marginTop: '8px' }}>
              <div style={{ ...styles.typeLabel, marginBottom: '4px' }}>Projections:</div>
              {declaration.prettyProjections.map((proj, index) => (
                <div key={index} style={styles.ctorRow}>
                  <span style={styles.projectionName}>{proj.name}</span>
                  <span style={{ color: '#8b949e' }}> : </span>
                  <span style={styles.typeValue}>{proj.prettyType}</span>
                </div>
              ))}
            </div>
          )}
          {declaration.checkErrors && declaration.checkErrors.length > 0 && (
            <div style={{ marginTop: '8px' }}>
              {declaration.checkErrors.map((error, index) => (
                <div key={index} style={error.severity === 'warning' ? styles.warningText : styles.errorText}>
                  {error.message}
                </div>
              ))}
            </div>
          )}
          {declaration.withClauseErrors && declaration.withClauseErrors.length > 0 && (
            <div style={{ marginTop: '8px' }}>
              {declaration.withClauseErrors.map((error, index) => (
                <div key={`with-${index}`} style={styles.errorText}>{error.message}</div>
              ))}
            </div>
          )}
          {declaration.totalityResult && <TextEditorCaseTree result={declaration.totalityResult} />}
        </>
      }
    />
  );
}
