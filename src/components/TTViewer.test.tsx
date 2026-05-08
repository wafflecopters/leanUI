import { describe, expect, test } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { TTViewer } from './TTViewer';
import { mkLambdaTT, mkPiTT, mkVarTT, mkTypeTT } from '../compiler/surface';

describe('TTViewer', () => {
  test('renders lambda binders without TODO fallback', () => {
    const markup = renderToStaticMarkup(
      <TTViewer proofTerm={mkLambdaTT(mkTypeTT(0), mkVarTT(0), 'x')} context={[]} />
    );

    expect(markup).toContain('λ');
    expect(markup).toContain('=&gt;');
    expect(markup).not.toContain('TODO-Binder-BLamTT');
  });

  test('continues to render pi binders alongside lambda binders', () => {
    const markup = renderToStaticMarkup(
      <TTViewer proofTerm={mkPiTT(mkTypeTT(0), mkLambdaTT(mkTypeTT(0), mkVarTT(0), 'x'), 'A')} context={[]} />
    );

    expect(markup).toContain('→');
    expect(markup).toContain('λ');
  });
});
