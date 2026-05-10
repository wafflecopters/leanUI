import { describe, expect, test } from 'vitest';
import {
  toggleWysiwygRouteState,
  withEditorParams,
  withPresetParam,
} from './textEditorUrlState';

describe('textEditorUrlState', () => {
  test('withPresetParam updates only the preset slug', () => {
    const next = withPresetParam(new URLSearchParams('editor=true&symbol=plus'), 'real-analysis');

    expect(next.toString()).toBe('editor=true&symbol=plus&preset=real-analysis');
  });

  test('withEditorParams keeps editor and symbol params in sync', () => {
    const enabled = withEditorParams(new URLSearchParams('preset=nat'), true, 'sum');
    expect(enabled.toString()).toBe('preset=nat&editor=true&symbol=sum');

    const disabled = withEditorParams(enabled, false, null);
    expect(disabled.toString()).toBe('preset=nat');
  });

  test('toggleWysiwygRouteState clears expanded symbol only when hiding the panel', () => {
    expect(toggleWysiwygRouteState({
      showWysiwyg: true,
      expandedSymbol: 'sum',
    })).toEqual({
      showWysiwyg: false,
      expandedSymbol: null,
    });

    expect(toggleWysiwygRouteState({
      showWysiwyg: false,
      expandedSymbol: 'sum',
    })).toEqual({
      showWysiwyg: true,
      expandedSymbol: 'sum',
    });
  });
});
