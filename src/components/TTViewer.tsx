/**
 * TT (Typed Term) Viewer Component
 *
 * This component displays the underlying TT proof term being constructed.
 * It shows:
 * 1. The complete proof term with proper De Bruijn indices
 * 2. Holes (metavariables) that need to be filled
 * 3. Type information
 * 4. Pretty-printed version for readability
 *
 * This is the "ground truth" of what we're actually constructing,
 * separate from the UI representation.
 */

import { TTerm, TContext, mapTTerm, TermDefinition, prettyPrintTT, TTermApp, prettyPrintLevelTermTT, mkULitTT } from '../compiler/surface';

// Helper to convert TTerm to plain text string
function ttermToString(term: TTerm): string {
  return prettyPrintTT(term);
}

export interface TTViewerProps {
  /** The current proof term (OLD - will be deprecated) */
  proofTerm?: TTerm | null;

  /** The term definition (NEW) */
  termDefinition?: TermDefinition | null;

  /** Context for the proof (variable names and types) */
  context?: TContext;

  /** Whether to show the raw AST structure */
  showRawAST?: boolean;
}

export function TTViewer({ proofTerm, termDefinition, context = [] }: TTViewerProps) {
  // NEW: Prefer termDefinition if provided
  if (termDefinition) {
    return (
      <div style={{
        padding: '20px',
        backgroundColor: '#fafafa',
        border: '2px solid #007acc',
        borderRadius: '8px',
        fontFamily: 'monospace',
        fontSize: '14px',
        maxHeight: '600px',
        overflow: 'auto'
      }}>
        {/* Header */}
        <div style={{
          fontWeight: 'bold',
          fontSize: '16px',
          color: '#007acc',
          marginBottom: '16px',
          borderBottom: '2px solid #007acc',
          paddingBottom: '8px'
        }}>
          TT Term Definition
        </div>

        {/* Type Declaration */}
        <div style={{
          padding: '12px',
          backgroundColor: '#e6f3ff',
          borderLeft: '4px solid #007acc',
          borderRadius: '4px',
          marginBottom: '12px',
          position: 'relative'
        }}>
          <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center', marginBottom: '8px' }}>
            <div style={{ fontWeight: 'bold', color: '#007acc' }}>
              Declaration:
            </div>
            <button
              onClick={() => {
                const text = `${termDefinition.name} : ${ttermToString(termDefinition.type)}`;
                navigator.clipboard.writeText(text);
              }}
              style={{
                padding: '4px 8px',
                backgroundColor: '#007acc',
                color: 'white',
                border: 'none',
                borderRadius: '4px',
                cursor: 'pointer',
                fontSize: '11px',
                fontWeight: 'bold'
              }}
              title="Copy to clipboard"
            >
              📋 Copy
            </button>
          </div>
          <div style={{ fontFamily: 'monospace', fontSize: '13px' }}>
            {termDefinition.name} : <PrintedTerm term={termDefinition.type} context={context} />
          </div>
        </div>

        {/* Value Definition */}
        <div style={{
          padding: '12px',
          backgroundColor: '#f5e3f3',
          borderLeft: '4px solid #8e24aa',
          borderRadius: '4px',
          marginBottom: '12px',
          position: 'relative'
        }}>
          <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center', marginBottom: '8px' }}>
            <div style={{ fontWeight: 'bold', color: '#8e24aa' }}>
              Definition:
            </div>
            <button
              onClick={() => {
                const text = `${termDefinition.name} = ${ttermToString(termDefinition.value)}`;
                navigator.clipboard.writeText(text);
              }}
              style={{
                padding: '4px 8px',
                backgroundColor: '#8e24aa',
                color: 'white',
                border: 'none',
                borderRadius: '4px',
                cursor: 'pointer',
                fontSize: '11px',
                fontWeight: 'bold'
              }}
              title="Copy to clipboard"
            >
              📋 Copy
            </button>
          </div>
          <div style={{ fontFamily: 'monospace', fontSize: '13px' }}>
            {termDefinition.name} = <PrintedTerm term={termDefinition.value} context={context} />
          </div>
        </div>

        {/* Full AST */}
        <div style={{
          padding: '12px',
          backgroundColor: '#e8f5e9',
          borderLeft: '4px solid #4caf50',
          borderRadius: '4px',
          position: 'relative'
        }}>
          <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center', marginBottom: '8px' }}>
            <div style={{ fontWeight: 'bold', color: '#2e7d32' }}>
              Full AST:
            </div>
            <button
              onClick={() => {
                const text = JSON.stringify(termDefinition, null, 2);
                navigator.clipboard.writeText(text);
              }}
              style={{
                padding: '4px 8px',
                backgroundColor: '#4caf50',
                color: 'white',
                border: 'none',
                borderRadius: '4px',
                cursor: 'pointer',
                fontSize: '11px',
                fontWeight: 'bold'
              }}
              title="Copy to clipboard"
            >
              📋 Copy
            </button>
          </div>
          <pre style={{
            margin: 0,
            fontFamily: 'monospace',
            fontSize: '11px',
            color: '#1b5e20',
            whiteSpace: 'pre-wrap',
            wordBreak: 'break-word',
            overflow: 'auto',
            maxHeight: '500px'
          }}>
            {JSON.stringify(termDefinition, null, 2)}
          </pre>
        </div>
      </div>
    );
  }

  // OLD: Fall back to proofTerm
  if (!proofTerm) {
    return (
      <div style={{
        padding: '20px',
        backgroundColor: '#f5f5f5',
        border: '2px solid #ddd',
        borderRadius: '8px',
        fontFamily: 'monospace',
        color: '#888'
      }}>
        <div style={{ fontWeight: 'bold', marginBottom: '8px', color: '#666' }}>
          TT Proof Term
        </div>
        <div style={{ fontStyle: 'italic' }}>
          No proof term constructed yet.
        </div>
      </div>
    );
  }

  return (
    <div style={{
      padding: '20px',
      backgroundColor: '#fafafa',
      border: '2px solid #007acc',
      borderRadius: '8px',
      fontFamily: 'monospace',
      fontSize: '14px',
      maxHeight: '600px',
      overflow: 'auto'
    }}>
      {/* Header */}
      <div style={{
        fontWeight: 'bold',
        fontSize: '16px',
        color: '#007acc',
        marginBottom: '16px',
        borderBottom: '2px solid #007acc',
        paddingBottom: '8px'
      }}>
        TT Proof Term
      </div>

      <div style={{
        padding: '12px',
        backgroundColor: '#f5e3f3',
        borderLeft: '4px solid #8e24aa',
        borderRadius: '4px',
        marginBottom: '12px',
      }}>
        <div style={{ fontWeight: 'bold', marginBottom: '8px', color: '#8e24aa' }}>
          Term:
        </div>
        <PrintedTerm term={proofTerm} context={context} />
      </div>

      <div style={{
        padding: '12px',
        backgroundColor: '#e8f5e9',
        borderLeft: '4px solid #4caf50',
        borderRadius: '4px'
      }}>
        <div style={{ fontWeight: 'bold', marginBottom: '8px', color: '#2e7d32' }}>
          Full AST:
        </div>
        <pre style={{
          margin: 0,
          fontFamily: 'monospace',
          fontSize: '11px',
          color: '#1b5e20',
          whiteSpace: 'pre-wrap',
          wordBreak: 'break-word',
          overflow: 'auto',
          maxHeight: '500px'
        }}>
          {JSON.stringify(proofTerm, null, 2)}
        </pre>
      </div>
    </div>
  );
}

function PrintedTerm({ term, context = [] }: { term: TTerm; context?: TContext }) {
  return (
    <div>{mapTTerm(term, {
      Var: (term) => {
        const binding = context[term.index];
        return <span>{binding ? binding.name : `Var-${term.index}`}</span>;
      },
      Sort: (term) => <span>Sort<sub>{prettyPrintLevelTermTT(term.level)}</sub></span>,
      ULevel: () => <span>ULevel</span>,
      ULit: (term) => <span>{term.n}</span>,
      UOmega: () => <span>ω</span>,
      Binder: (term) => <PrintedBinderTerm binderTerm={term} context={context} />,
      App: (term) => <PrintedAppTerm term={term} context={context} />,
      Const: (term) => <span>{term.name}</span>,
      Hole: (term) => <span style={{
        backgroundColor: '#ffeb3b',
        color: '#000',
        padding: '2px 6px',
        borderRadius: '4px',
        fontWeight: 'bold',
        border: '2px solid #ffc107'
      }}>?{term.id}</span>,
      Annot: () => <div>ANNOT</div>,
      Match: (term) => <div>MATCH({term.clauses.length} clauses)</div>,
      MultiBinder: (term) => <span>({term.names.join(' ')} : <PrintedTerm term={term.domain} context={context} />) {term.binderKind.tag === 'BPiTT' ? '→' : '=>'} <PrintedTerm term={term.body} context={context} /></span>,
      AbsurdMarker: () => <span style={{ color: '#888', fontStyle: 'italic' }}>#absurd</span>,
      WithClause: () => <span style={{ color: '#888', fontStyle: 'italic' }}>#with</span>
    })}
    </div>
  )
}

function PrintedAppTerm({ term, context = [] }: { term: TTermApp; context?: TContext }) {
  // if (term.fn.tag === 'App' && term.fn.fn.tag === 'Const') {
  //   const info = ttconstInfo(term.fn.fn)
  //   if (info) {
  //     return (
  //       <PrintedInfixBinopTerm fn={term.fn.fn} arg0={term.fn.arg} arg1={term.arg} info={info} context={context} />
  //     )
  //   }
  // }

  return (
    <div style={{ display: 'flex', flexDirection: 'row', alignItems: 'center' }}>
      (<PrintedTerm term={term.fn} context={context} /><div style={{ width: '4px' }}></div><PrintedTerm term={term.arg} context={context} />)
    </div>
  )
}

// function PrintedInfixBinopTerm({ fn, arg0, arg1, info, context = [] }: { fn: TTermConst, arg0: TTerm, arg1: TTerm, info: TTConstantInfo; context?: TContext }) {
//   return (
//     <div style={{ display: 'flex', flexDirection: 'row', alignItems: 'center' }}>
//       (<PrintedTerm term={arg0} context={context} /><div>{info.infixName ?? fn.name}</div><PrintedTerm term={arg1} context={context} />)
//     </div>
//   )
// }

function PrintedBinderTerm({ binderTerm, context }: { binderTerm: Extract<TTerm, { tag: "Binder" }>; context: TContext }) {
  // Extend context with this binding for the body
  // For let bindings without type annotation, use a placeholder type
  const bindingType = binderTerm.domain ?? { tag: 'Hole' as const, id: '_', type: { tag: 'Sort' as const, level: mkULitTT(0) }, context: [] };
  const extendedContext: TContext = [{ name: binderTerm.name, type: bindingType }, ...context];

  if (binderTerm.binderKind.tag === 'BLetTT') {
    return (
      <div>
        <div style={{ display: 'flex', flexDirection: 'row', gap: '4px', alignItems: 'center' }}>
          let {binderTerm.name}{binderTerm.domain !== undefined && <> : <PrintedTerm term={binderTerm.domain} context={context} /></>} = <PrintedTerm term={binderTerm.binderKind.defVal} context={context} /> in
        </div>
        <div style={{ marginLeft: '16px' }}>
          <PrintedTerm term={binderTerm.body} context={extendedContext} />
        </div>
      </div>
    )
  } else if (binderTerm.binderKind.tag === 'BPiTT') {
    // Pi binders always have domain
    return (
      <div>
        <div style={{ display: 'flex', flexDirection: 'row', gap: '4px', alignItems: 'center' }}>
          ({binderTerm.name} : <PrintedTerm term={binderTerm.domain!} context={context} />) → <PrintedTerm term={binderTerm.body} context={extendedContext} />
        </div>
      </div>
    )
  } else {
    return <div>{`TODO-Binder-${binderTerm.binderKind.tag}`}</div>
  }
}