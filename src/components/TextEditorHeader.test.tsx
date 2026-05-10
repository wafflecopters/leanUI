import { describe, expect, test } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { TextEditorHeader } from './TextEditorHeader';

describe('TextEditorHeader', () => {
  test('renders title and toggles WYSIWYG label based on state', () => {
    const markup = renderToStaticMarkup(
      <TextEditorHeader
        presets={[]}
        showWYSIWYG={false}
        presetMenuOpen={false}
        onToggleWYSIWYG={() => {}}
        onTogglePresetMenu={() => {}}
        onLoadPreset={() => {}}
      />
    );

    expect(markup).toContain('Text Editor');
    expect(markup).toContain('Edit code and view compilation results');
    expect(markup).toContain('Show WYSIWYG');
    expect(markup).toContain('Load Preset');
  });

  test('renders preset menu entries when the menu is open', () => {
    const markup = renderToStaticMarkup(
      <TextEditorHeader
        presets={[
          { name: 'Grab Bag', code: 'foo' },
          { name: 'Real Analysis', code: 'bar' },
        ]}
        showWYSIWYG={true}
        presetMenuOpen={true}
        onToggleWYSIWYG={() => {}}
        onTogglePresetMenu={() => {}}
        onLoadPreset={() => {}}
      />
    );

    expect(markup).toContain('Hide WYSIWYG');
    expect(markup).toContain('Grab Bag');
    expect(markup).toContain('Real Analysis');
  });
});
