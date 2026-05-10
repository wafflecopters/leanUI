export interface TextEditorRouteState {
  showWysiwyg: boolean;
  expandedSymbol: string | null;
}

export function withPresetParam(
  current: URLSearchParams,
  presetSlug: string
): URLSearchParams {
  const next = new URLSearchParams(current);
  next.set('preset', presetSlug);
  return next;
}

export function withEditorParams(
  current: URLSearchParams,
  showWysiwyg: boolean,
  expandedSymbol: string | null
): URLSearchParams {
  const next = new URLSearchParams(current);
  if (showWysiwyg) {
    next.set('editor', 'true');
  } else {
    next.delete('editor');
  }

  if (expandedSymbol) {
    next.set('symbol', expandedSymbol);
  } else {
    next.delete('symbol');
  }

  return next;
}

export function toggleWysiwygRouteState(
  current: TextEditorRouteState
): TextEditorRouteState {
  if (current.showWysiwyg) {
    return { showWysiwyg: false, expandedSymbol: null };
  }

  return {
    showWysiwyg: true,
    expandedSymbol: current.expandedSymbol,
  };
}
