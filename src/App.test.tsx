import { afterEach, beforeEach, describe, expect, test, vi } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { MemoryRouter } from 'react-router-dom';

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

  // M5 deleted the TT engine and its page: the old routes must not 404 or
  // render something else — they fall through to the Lean editor like any
  // unknown path.
  test('the retired TT routes now land on the Lean editor', () => {
    expect(render('/tt-legacy')).toContain('Mock Lean Editor Page');
    expect(render('/text-editor')).toContain('Mock Lean Editor Page');
  });
});
