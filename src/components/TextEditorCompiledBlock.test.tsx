import { describe, expect, test } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { ParseError } from '../parser/parser';
import { TextEditorCompiledBlock } from './TextEditorCompiledBlock';

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

describe('TextEditorCompiledBlock', () => {
  test('renders collapsed comment blocks with their badge and hidden body', () => {
    const markup = renderToStaticMarkup(
      <TextEditorCompiledBlock
        block={{
          blockIndex: 0,
          sourceLines: ['-- note', '-- more context'],
          startLine: 1,
          codeStartLine: 1,
          parseSuccess: true,
          parseErrors: [],
          nameResolutionSuccess: true,
          nameResolutionErrors: [],
          declarations: [],
          isComment: true,
        }}
        showNamedArgsWithLabels={true}
        showNamedParamsWithBraces={false}
        definitions={emptyDefinitions() as any}
      />
    );

    expect(markup).toContain('Comment');
    expect(markup).not.toContain('-- note');
    expect(markup).not.toContain('-- more context');
  });

  test('renders collapsed parse-error blocks with an error badge', () => {
    const markup = renderToStaticMarkup(
      <TextEditorCompiledBlock
        block={{
          blockIndex: 0,
          sourceLines: ['bad source'],
          startLine: 3,
          codeStartLine: 3,
          parseSuccess: false,
          parseErrors: [new ParseError('unexpected token', 3, 4)],
          nameResolutionSuccess: true,
          nameResolutionErrors: [],
          declarations: [],
          isComment: false,
        }}
        showNamedArgsWithLabels={true}
        showNamedParamsWithBraces={false}
        definitions={emptyDefinitions() as any}
      />
    );

    expect(markup).toContain('Parse Error');
    expect(markup).not.toContain('Line 3, Col 4: unexpected token');
  });

  test('renders name-resolution error badges without falling through to declaration cards', () => {
    const markup = renderToStaticMarkup(
      <TextEditorCompiledBlock
        block={{
          blockIndex: 0,
          sourceLines: ['missing : Foo'],
          startLine: 5,
          codeStartLine: 5,
          parseSuccess: true,
          parseErrors: [],
          nameResolutionSuccess: false,
          nameResolutionErrors: [{ message: 'Unknown name Foo', range: null } as any],
          declarations: [{
            kind: 'term',
            name: 'shouldNotRender',
            checkSuccess: true,
            checkErrors: [],
          } as any],
          isComment: false,
        }}
        showNamedArgsWithLabels={true}
        showNamedParamsWithBraces={false}
        definitions={emptyDefinitions() as any}
      />
    );

    expect(markup).toContain('Name Error');
    expect(markup).not.toContain('Unknown name Foo');
    expect(markup).not.toContain('shouldNotRender');
  });

  test('renders declaration cards for successful blocks', () => {
    const markup = renderToStaticMarkup(
      <TextEditorCompiledBlock
        block={{
          blockIndex: 0,
          sourceLines: ['foo : Nat', 'foo = Zero'],
          startLine: 1,
          codeStartLine: 1,
          parseSuccess: true,
          parseErrors: [],
          nameResolutionSuccess: true,
          nameResolutionErrors: [],
          declarations: [{
            kind: 'term',
            name: 'foo',
            checkSuccess: true,
            checkErrors: [],
            kernelType: { tag: 'Const', name: 'Nat' },
            kernelValue: { tag: 'Const', name: 'Zero' },
          } as any],
          isComment: false,
        }}
        showNamedArgsWithLabels={true}
        showNamedParamsWithBraces={false}
        definitions={emptyDefinitions() as any}
      />
    );

    expect(markup).toContain('foo');
    expect(markup).toContain('OK');
    expect(markup).not.toContain('Type:');
    expect(markup).not.toContain('Zero');
  });
});
