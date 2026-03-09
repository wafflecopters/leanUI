import React, { useEffect, useMemo, useRef, useState } from 'react';
import katex from 'katex';
import { CompiledDeclaration } from '../compiler/compile';
import { DefinitionsMap, createDefinitionsMap, addDefinition, addInductiveDefinition } from '../compiler/term';
import { DualMathEditor } from './DualMathEditor';
import { ProofTreeEditor } from './ProofTreeEditor';
import { SyntaxRegistry, SyntaxEntry, patternToDisplayLatex, SyntaxAnnotation, buildRegistryFromAnnotations } from '../math-editor/syntax-registry';
import { surfaceTypeToMathRow } from '../math-editor/tt-to-math';
import { MathRow } from '../math-editor/types';
import { ProofTreeHistory, createHistory, createInitialState } from '../proof-tree/proof-tree';
import { InductiveMap, InductiveInfo } from '../proof-tree/goal-computation';

export interface WYSIWYGPanelProps {
  /** Compiled declarations for display (zonked kernel terms — no unsolved metas) */
  declarations: CompiledDeclaration[];
  /** All compiled declarations (for building syntax registry from @syntax annotations) */
  allDeclarations: CompiledDeclaration[];
}

/** Color for the declaration kind badge */
function declKindColor(decl: CompiledDeclaration): string {
  if (decl.kind === 'inductive') {
    if (decl.isRecord) return '#a371f7';
    return '#3fb950';
  }
  return '#58a6ff';
}

/**
 * Extract SyntaxAnnotation[] from compiled declarations.
 * Each declaration's @syntax and its constructors' @syntax become annotations.
 */
function extractAnnotations(decls: CompiledDeclaration[]): SyntaxAnnotation[] {
  const annotations: SyntaxAnnotation[] = [];
  for (const decl of decls) {
    if (decl.syntax && decl.name) {
      annotations.push({ declName: decl.name, pattern: decl.syntax, isRecord: decl.isRecord });
    }
    if (decl.constructorSyntax) {
      for (const cs of decl.constructorSyntax) {
        annotations.push({ declName: cs.name, pattern: cs.syntax });
      }
    }
  }
  return annotations;
}

export function WYSIWYGPanel({ declarations, allDeclarations }: WYSIWYGPanelProps) {
  // Build per-declaration registries scoped to syntax defined BEFORE each declaration
  const registries = useMemo(() => {
    const allAnnotations = extractAnnotations(allDeclarations);
    if (allAnnotations.length === 0) {
      return declarations.map(() => ({ symbolMap: new Map(), entries: [] } as SyntaxRegistry));
    }

    // For each displayed declaration, find its index in allDeclarations,
    // then build a registry from annotations of allDeclarations[0..index-1]
    return declarations.map(decl => {
      const idx = allDeclarations.indexOf(decl);
      if (idx <= 0) {
        return { symbolMap: new Map(), entries: [] } as SyntaxRegistry;
      }
      const precedingAnnotations = extractAnnotations(allDeclarations.slice(0, idx));
      if (precedingAnnotations.length === 0) {
        return { symbolMap: new Map(), entries: [] } as SyntaxRegistry;
      }
      return buildRegistryFromAnnotations(precedingAnnotations);
    });
  }, [declarations, allDeclarations]);

  // Compute initial type roots from surfaceType for pre-filling editors
  const initialTypeRoots = useMemo<(MathRow | undefined)[]>(() => {
    return declarations.map((decl, i) => {
      if (!decl.surfaceType) return undefined;
      try {
        return surfaceTypeToMathRow(decl.surfaceType, registries[i]);
      } catch {
        return undefined;
      }
    });
  }, [declarations, registries]);

  // Build DefinitionsMap from all compiled declarations (for unfold tactic)
  const definitionsMap = useMemo<DefinitionsMap>(() => {
    let defs = createDefinitionsMap();
    for (const decl of allDeclarations) {
      if (!decl.name) continue;
      if (decl.kind === 'inductive' && decl.kernelType && decl.kernelConstructors) {
        defs = addInductiveDefinition(
          defs, decl.name, decl.kernelType,
          decl.kernelConstructors,
          decl.indexPositions ?? [],
          decl.namedArgMap,
        );
        // Also add constructors to terms map so ExactTactic can find them
        for (const ctor of decl.kernelConstructors) {
          defs = addDefinition(defs, ctor.name, ctor.type, undefined, ctor.namedArgMap);
        }
      } else if (decl.kind === 'term' && decl.kernelType) {
        defs = addDefinition(
          defs, decl.name, decl.kernelType,
          decl.kernelValue, decl.namedArgMap,
        );
      }
    }
    return defs;
  }, [allDeclarations]);

  // Build InductiveMap from all compiled declarations
  const inductiveMap = useMemo<InductiveMap>(() => {
    const map = new Map<string, InductiveInfo>();
    for (const decl of allDeclarations) {
      if (decl.kind === 'inductive' && decl.name && decl.surfaceConstructors) {
        map.set(decl.name, {
          name: decl.name,
          constructors: decl.surfaceConstructors,
        });
      }
    }
    return map;
  }, [allDeclarations]);

  // Per-box editable name
  const [localNames, setLocalNames] = useState<string[]>(() =>
    declarations.map(d => d.name || '')
  );
  const handleNameChange = (index: number, value: string) => {
    setLocalNames(prev => {
      const next = [...prev];
      next[index] = value;
      return next;
    });
  };

  // Per-declaration proof tree history
  const [proofHistories, setProofHistories] = useState<ProofTreeHistory[]>(() =>
    declarations.map(() => createHistory(createInitialState()))
  );
  const handleProofHistoryChange = (index: number, h: ProofTreeHistory) => {
    setProofHistories(prev => {
      const next = [...prev];
      next[index] = h;
      return next;
    });
  };

  return (
    <div style={{
      padding: '16px',
      color: '#c9d1d9',
      fontFamily: '-apple-system, BlinkMacSystemFont, "Segoe UI", Helvetica, Arial, sans-serif',
    }}>
      <h3 style={{
        margin: '0 0 16px 0',
        color: '#e6edf3',
        fontSize: '14px',
        fontWeight: 600,
        letterSpacing: '0.02em',
      }}>
        WYSIWYG Editor
      </h3>

      {declarations.map((decl, i) => (
        <div key={i} style={{
          marginBottom: '12px',
          border: '1px solid #30363d',
          borderRadius: '6px',
          overflow: 'hidden',
          backgroundColor: '#161b22',
        }}>
          {/* Header: kind badge + editable name */}
          <div style={{
            display: 'flex',
            alignItems: 'center',
            padding: '6px 10px',
            backgroundColor: '#21262d',
            borderBottom: '1px solid #30363d',
            gap: '8px',
          }}>
            <span style={{
              fontSize: '11px',
              fontWeight: 600,
              color: declKindColor(decl),
              textTransform: 'uppercase',
              letterSpacing: '0.04em',
              flexShrink: 0,
            }}>
              definition
            </span>
            <input
              type="text"
              value={localNames[i] ?? decl.name ?? ''}
              onChange={(e) => handleNameChange(i, e.target.value)}
              spellCheck={false}
              style={{
                flex: 1,
                background: 'none',
                border: 'none',
                outline: 'none',
                color: '#e6edf3',
                fontFamily: '"JetBrains Mono", "Fira Code", Menlo, Consolas, monospace',
                fontSize: '13px',
                fontWeight: 500,
                padding: '2px 4px',
                borderRadius: '3px',
              }}
              onFocus={(e) => {
                e.currentTarget.style.backgroundColor = '#0d1117';
              }}
              onBlur={(e) => {
                e.currentTarget.style.backgroundColor = 'transparent';
              }}
            />
          </div>

          {/* Structured math editors (type + proof) */}
          <div style={{ padding: '6px 10px', borderTop: '1px solid #30363d' }}>
            <SyntaxReferencePanel registry={registries[i]} />
            <DualMathEditor placeholder="type signature" registry={registries[i]} initialTypeRoot={initialTypeRoots[i]} />
          </div>

          {/* Structured proof tree editor */}
          <div style={{ padding: '6px 10px', borderTop: '1px solid #30363d' }}>
            <div style={{ fontSize: '10px', color: '#484f58', marginBottom: '4px', letterSpacing: '0.03em' }}>
              PROOF
            </div>
            <ProofTreeEditor
              history={proofHistories[i] ?? createHistory(createInitialState())}
              onHistoryChange={(h) => handleProofHistoryChange(i, h)}
              surfaceType={decl.surfaceType}
              kernelType={decl.kernelType}
              definitions={definitionsMap}
              registry={registries[i]}
              inductiveMap={inductiveMap}
            />
          </div>
        </div>
      ))}
    </div>
  );
}

// ============================================================================
// Syntax Reference Panel — compact display of available syntax patterns
// ============================================================================

function SyntaxReferenceEntry({ entry }: { entry: SyntaxEntry }) {
  const ref = useRef<HTMLSpanElement>(null);
  const latex = useMemo(() => patternToDisplayLatex(entry.pattern), [entry.pattern]);

  useEffect(() => {
    if (!ref.current) return;
    try {
      katex.render(latex, ref.current, {
        displayMode: false,
        throwOnError: false,
        trust: (context) => ['\\htmlId', '\\class', '\\textcolor'].includes(context.command),
        strict: false,
      });
    } catch {
      ref.current.textContent = latex;
    }
  }, [latex]);

  // Clean template for display: \$x => body → λx => body, $$a → a, $a → a
  const displayTemplate = entry.template
    .replace(/\\\$/g, 'λ')       // \$ (lambda binder) → λ
    .replace(/\$\$/g, '$')       // $$ (auto-paren sigil) → $ (temporary)
    .replace(/\$/g, '');          // strip all remaining $ sigils

  return (
    <>
      <span ref={ref} style={{ fontSize: '11px', justifySelf: 'end' }} />
      <span style={{ color: '#30363d', fontSize: '10px' }}>{'\u2192'}</span>
      <span style={{
        fontFamily: '"JetBrains Mono", "Fira Code", Menlo, Consolas, monospace',
        color: '#8b949e',
        fontSize: '10px',
      }}>
        {displayTemplate}
      </span>
    </>
  );
}

function SymbolMapEntry({ symbol, source }: { symbol: string; source: string }) {
  const ref = useRef<HTMLSpanElement>(null);

  useEffect(() => {
    if (!ref.current) return;
    try {
      katex.render(symbol, ref.current, {
        displayMode: false,
        throwOnError: false,
        strict: false,
      });
    } catch {
      ref.current.textContent = symbol;
    }
  }, [symbol]);

  return (
    <>
      <span ref={ref} style={{ fontSize: '11px', justifySelf: 'end' }} />
      <span style={{ color: '#30363d', fontSize: '10px' }}>{'\u2192'}</span>
      <span style={{
        fontFamily: '"JetBrains Mono", "Fira Code", Menlo, Consolas, monospace',
        color: '#8b949e',
        fontSize: '10px',
      }}>
        {source}
      </span>
    </>
  );
}

function SyntaxReferencePanel({ registry }: { registry: SyntaxRegistry }) {
  const [expanded, setExpanded] = useState(false);

  const symbolEntries = useMemo(() =>
    [...registry.symbolMap.entries()],
    [registry.symbolMap]
  );

  return (
    <div style={{
      marginBottom: '4px',
      borderRadius: '4px',
      border: '1px solid #21262d',
      backgroundColor: '#0d1117',
      overflow: 'hidden',
    }}>
      <div
        onClick={() => setExpanded(prev => !prev)}
        style={{
          display: 'flex',
          alignItems: 'center',
          gap: '6px',
          padding: '3px 8px',
          cursor: 'pointer',
          userSelect: 'none',
          fontSize: '10px',
          color: '#484f58',
          letterSpacing: '0.03em',
        }}
      >
        <span style={{ fontSize: '8px' }}>{expanded ? '\u25BC' : '\u25B6'}</span>
        <span>Syntax ({registry.entries.length + symbolEntries.length})</span>
      </div>

      {expanded && (
        <div style={{
          padding: '4px 8px 6px',
          display: 'grid',
          gridTemplateColumns: 'auto auto 1fr',
          rowGap: '2px',
          columnGap: '8px',
          alignItems: 'center',
          borderTop: '1px solid #21262d',
        }}>
          {symbolEntries.map(([sym, { source }]) => (
            <SymbolMapEntry key={sym} symbol={sym} source={source} />
          ))}
          {registry.entries.map(entry => (
            <SyntaxReferenceEntry key={entry.name} entry={entry} />
          ))}
        </div>
      )}
    </div>
  );
}
