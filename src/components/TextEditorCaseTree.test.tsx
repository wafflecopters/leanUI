import { describe, expect, test } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { TextEditorCaseTree } from './TextEditorCaseTree';

describe('TextEditorCaseTree', () => {
  test('renders totality status and unreachable clause warnings', () => {
    const markup = renderToStaticMarkup(
      <TextEditorCaseTree
        result={{
          isExhaustive: false,
          frozenPositionCount: 1,
          unreachableClauses: [{ clauseIndex: 1, patterns: [] }],
          caseTree: {
            tag: 'NoSplit',
            debugLabel: 'ctx',
            branch: { tag: 'Leaf', clauseIndex: 0 },
          },
        } as any}
      />
    );

    expect(markup).toContain('Case Tree');
    expect(markup).toContain('Non-exhaustive');
    expect(markup).toContain('ctx');
    expect(markup).toContain('→ clause 0');
    expect(markup).toContain('Unreachable clause(s): 2');
  });

  test('renders split branches with constructor arguments and uncovered leaves', () => {
    const markup = renderToStaticMarkup(
      <TextEditorCaseTree
        result={{
          isExhaustive: true,
          unreachableClauses: [],
          caseTree: {
            tag: 'Split',
            branches: new Map([
              ['Succ', { tag: 'NoSplit', debugLabel: 'n', branch: { tag: 'Uncovered' } }],
            ]),
            ctorArities: new Map([['Succ', 1]]),
            missingCtors: new Set(),
            typeName: 'Nat',
            remainingPatternsAfterContructorCount: 0,
          },
        } as any}
      />
    );

    expect(markup).toContain('(Succ n)');
    expect(markup).toContain('⚠ uncovered');
    expect(markup).toContain('Exhaustive');
  });
});
