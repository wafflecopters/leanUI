import { afterEach, beforeEach, describe, expect, test, vi } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { MemoryRouter } from 'react-router-dom';

vi.mock('./components/TextEditorPage', () => ({
  TextEditorPage: () => <div>Mock Text Editor Page</div>,
}));
vi.mock('./components/LeanEditorPage', () => ({
  LeanEditorPage: () => <div>Mock Lean Editor Page</div>,
}));

import { AppRoutes } from './App';

function render(path: string): string {
  return renderToStaticMarkup(
    <MemoryRouter initialEntries={[path]}>
      <AppRoutes />
    </MemoryRouter>,
  );
}

describe('App routes', () => {
  beforeEach(() => {
    vi.spyOn(console, 'error').mockImplementation(() => {});
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  test('the Lean editor is the default route', () => {
    expect(render('/')).toContain('Mock Lean Editor Page');
  });

  test('/lean renders the Lean editor', () => {
    expect(render('/lean')).toContain('Mock Lean Editor Page');
  });

  test('unknown routes fall through to the Lean editor', () => {
    expect(render('/inductive')).toContain('Mock Lean Editor Page');
  });

  test('the legacy TT editor stays reachable at /tt-legacy', () => {
    expect(render('/tt-legacy')).toContain('Mock Text Editor Page');
  });

  test('the legacy TT editor stays reachable at /text-editor', () => {
    expect(render('/text-editor')).toContain('Mock Text Editor Page');
  });
});
