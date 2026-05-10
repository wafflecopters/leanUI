import { describe, expect, test } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { TextEditorTypeInfoPanel } from './TextEditorTypeInfoPanel';

describe('TextEditorTypeInfoPanel', () => {
  test('renders the empty placeholder when there is no cursor info', () => {
    const markup = renderToStaticMarkup(<TextEditorTypeInfoPanel typeInfoAtCursor={undefined} />);

    expect(markup).toContain('Move cursor over an expression or tactic to see info');
  });

  test('renders term expression, expected type, and context entries', () => {
    const markup = renderToStaticMarkup(
      <TextEditorTypeInfoPanel
        typeInfoAtCursor={{
          kind: 'term',
          expression: 'x',
          info: {
            prettyType: 'Nat',
            expectedType: 'Nat',
            surfacePath: 'value.clauses[0].rhs',
            context: [{ name: 'x', type: 'Nat' }],
          },
        } as any}
      />
    );

    expect(markup).toContain('x : Nat');
    expect(markup).toContain('Expected');
    expect(markup).toContain('Context');
    expect(markup).toContain('x');
    expect(markup).toContain('Nat');
  });

  test('renders tactic goals and hypotheses', () => {
    const markup = renderToStaticMarkup(
      <TextEditorTypeInfoPanel
        typeInfoAtCursor={{
          kind: 'tactic',
          goalStates: [{
            id: 'goal-1',
            caseTag: 'Succ',
            hypotheses: [{
              name: 'n',
              type: { tag: 'Const', name: 'Nat' },
            }],
            target: { tag: 'Const', name: 'Nat' },
          }],
        } as any}
      />
    );

    expect(markup).toContain('Hypotheses');
    expect(markup).toContain('Goal');
    expect(markup).toContain('(Succ)');
    expect(markup).toContain('n');
    expect(markup).toContain('Nat');
  });
});
