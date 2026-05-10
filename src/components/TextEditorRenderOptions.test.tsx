import { describe, expect, test } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { TextEditorRenderOptions } from './TextEditorRenderOptions';

describe('TextEditorRenderOptions', () => {
  test('renders both pretty-print toggles', () => {
    const markup = renderToStaticMarkup(
      <TextEditorRenderOptions
        showNamedArgsWithLabels={true}
        showNamedParamsWithBraces={false}
        setShowNamedArgsWithLabels={() => {}}
        setShowNamedParamsWithBraces={() => {}}
      />
    );

    expect(markup).toContain('Show named args as');
    expect(markup).toContain('Show named params as');
    expect(markup).toContain('checked=""');
  });
});
