import { describe, expect, test } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { TextEditorDeclarationCard } from './TextEditorDeclarationCard';

function emptyDefinitions() {
  return {
    terms: new Map(),
    inductiveTypes: new Map(),
    inductiveNameOfConstructor: new Map(),
    natImplByCtor: new Map(),
    ofNatByTargetHead: new Map(),
    natOpByFn: new Map(),
  };
}

describe('TextEditorDeclarationCard', () => {
  test('renders constructors, projections, and with-clause errors', () => {
    const markup = renderToStaticMarkup(
      <TextEditorDeclarationCard
        declaration={{
          kind: 'inductive',
          name: 'Vec',
          checkSuccess: false,
          checkErrors: [{ severity: 'error', message: 'bad index' }],
          withClauseErrors: [{ severity: 'error', message: 'with-clause failed' }],
          kernelType: { tag: 'Const', name: 'Type' },
          kernelConstructors: [{ name: 'VNil', type: { tag: 'Const', name: 'Vec' } }],
          prettyProjections: [{ name: 'Vec.head', prettyType: 'Nat' }],
        } as any}
        showNamedArgsWithLabels={true}
        showNamedParamsWithBraces={false}
        definitions={emptyDefinitions() as any}
      />
    );

    expect(markup).toContain('Inductive');
    expect(markup).toContain('Vec');
    expect(markup).toContain('Constructors:');
    expect(markup).toContain('VNil');
    expect(markup).toContain('Projections:');
    expect(markup).toContain('Vec.head');
    expect(markup).toContain('bad index');
    expect(markup).toContain('with-clause failed');
  });

  test('renders warning-only status without forcing FAIL text', () => {
    const markup = renderToStaticMarkup(
      <TextEditorDeclarationCard
        declaration={{
          kind: 'term',
          name: 'warnOnly',
          checkSuccess: false,
          checkErrors: [{ severity: 'warning', message: 'unused pattern variable' }],
          kernelType: { tag: 'Const', name: 'Nat' },
          kernelValue: { tag: 'Const', name: 'Zero' },
        } as any}
        showNamedArgsWithLabels={true}
        showNamedParamsWithBraces={false}
        definitions={emptyDefinitions() as any}
      />
    );

    expect(markup).toContain('1 warning');
    expect(markup).not.toContain('FAIL');
    expect(markup).toContain('unused pattern variable');
    expect(markup).toContain('Zero');
  });
});
