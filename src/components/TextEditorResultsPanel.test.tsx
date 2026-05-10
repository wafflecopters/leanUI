import { describe, expect, test } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { TextEditorResultsPanel } from './TextEditorResultsPanel';

describe('TextEditorResultsPanel', () => {
  test('renders compile error summary and parse-error headers', () => {
    const markup = renderToStaticMarkup(
      <TextEditorResultsPanel
        compileResult={{
          success: false,
          totalParseErrors: 1,
          totalNameErrors: 0,
          totalCheckErrors: 2,
          definitions: {
            terms: new Map(),
            inductiveTypes: new Map(),
            inductiveNameOfConstructor: new Map(),
            natImplByCtor: new Map(),
            ofNatByTargetHead: new Map(),
            natOpByFn: new Map(),
          },
          blocks: [{
            isComment: false,
            parseSuccess: false,
            parseErrors: [{ line: 3, col: 4, message: 'unexpected token' }],
            nameResolutionSuccess: true,
            nameResolutionErrors: [],
            declarations: [],
            sourceLines: ['bad source'],
          }],
        } as any}
        showNamedArgsWithLabels={true}
        showNamedParamsWithBraces={false}
        setShowNamedArgsWithLabels={() => {}}
        setShowNamedParamsWithBraces={() => {}}
      />
    );

    expect(markup).toContain('Compile Results');
    expect(markup).toContain('(3 errors)');
    expect(markup).toContain('Parse Error');
    expect(markup).toContain('Show named args as');
  });

  test('renders declaration details and totality output', () => {
    const markup = renderToStaticMarkup(
      <TextEditorResultsPanel
        compileResult={{
          success: true,
          totalParseErrors: 0,
          totalNameErrors: 0,
          totalCheckErrors: 0,
          definitions: {
            terms: new Map(),
            inductiveTypes: new Map(),
            inductiveNameOfConstructor: new Map(),
            natImplByCtor: new Map(),
            ofNatByTargetHead: new Map(),
            natOpByFn: new Map(),
          },
          blocks: [{
            isComment: false,
            parseSuccess: true,
            parseErrors: [],
            nameResolutionSuccess: true,
            nameResolutionErrors: [],
            sourceLines: ['foo : Nat', 'foo = Zero'],
            declarations: [{
              kind: 'term',
              name: 'foo',
              checkSuccess: false,
              checkErrors: [],
              kernelType: { tag: 'Const', name: 'Nat' },
              kernelValue: { tag: 'Const', name: 'Zero' },
              prettyProjections: [{ name: 'Point.x', prettyType: 'Nat' }],
              totalityResult: {
                isExhaustive: true,
                frozenPositionCount: 0,
                unreachableClauses: [{ clauseIndex: 1 }],
                caseTree: { tag: 'Leaf', clauseIndex: 0 },
              },
            }],
          }],
        } as any}
        showNamedArgsWithLabels={true}
        showNamedParamsWithBraces={false}
        setShowNamedArgsWithLabels={() => {}}
        setShowNamedParamsWithBraces={() => {}}
      />
    );

    expect(markup).toContain('foo');
    expect(markup).toContain('Type:');
    expect(markup).toContain('Nat');
    expect(markup).toContain('Value:');
    expect(markup).toContain('Zero');
    expect(markup).toContain('Projections:');
    expect(markup).toContain('Point.x');
    expect(markup).toContain('Case Tree');
    expect(markup).toContain('Exhaustive');
    expect(markup).toContain('Unreachable clause(s): 2');
  });
});
