import { afterEach, beforeEach, describe, expect, test, vi } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { MemoryRouter } from 'react-router-dom';

vi.mock('./components/TextEditorPage', () => ({
  TextEditorPage: () => <div>Mock Text Editor Page</div>,
}));

import { AppRoutes } from './App';

describe('App routes', () => {
  beforeEach(() => {
    vi.spyOn(console, 'error').mockImplementation(() => {});
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  test('renders the text editor on /text-editor', () => {
    const markup = renderToStaticMarkup(
      <MemoryRouter initialEntries={['/text-editor']}>
        <AppRoutes />
      </MemoryRouter>
    );

    expect(markup).toContain('Mock Text Editor Page');
  });

  test('legacy routes fall through to the same text editor page', () => {
    const markup = renderToStaticMarkup(
      <MemoryRouter initialEntries={['/inductive']}>
        <AppRoutes />
      </MemoryRouter>
    );

    expect(markup).toContain('Mock Text Editor Page');
  });
});
