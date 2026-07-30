/**
 * Deep-link auto-expand: `?symbol=<name>` must open that declaration's card
 * EXPANDED (the large modal view) when the panel renders. Static-markup render
 * — the initializer path — mirrors the real flow, where cards first mount only
 * after the async analyze delivers declarations (autoExpand known at mount).
 */
import { describe, expect, test } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { LeanWysiwygPanel } from './LeanWysiwygPanel';
import type { LeanDeclaration } from '../lean/types';

/** A plain value def (no proof) — keeps the card body to type/value math. */
function decl(name: string, line: number): LeanDeclaration {
  return {
    name,
    kind: 'def',
    prettyType: 'MyNat',
    typeTagged: { t: 'text', s: 'MyNat' },
    prettyValue: '5',
    valueTagged: { t: 'text', s: '5' },
    line,
    col: 0,
  };
}

const SOURCE = 'def foo : MyNat := 5\n\ndef bar : MyNat := 5\n';

function renderPanel(autoExpandSymbol: string | null): string {
  return renderToStaticMarkup(
    <LeanWysiwygPanel
      declarations={[decl('foo', 1), decl('bar', 3)]}
      goals={[]}
      source={SOURCE}
      autoExpandSymbol={autoExpandSymbol}
    />,
  );
}

describe('LeanWysiwygPanel deep-link auto-expand', () => {
  test('no symbol → no card is expanded (no modal)', () => {
    const html = renderPanel(null);
    expect(html).not.toContain('collapse'); // modal-only button
    expect(html).toContain('expand'); // inline header button present
  });

  test('matching symbol renders that card expanded (modal with collapse)', () => {
    const html = renderPanel('bar');
    expect(html).toContain('collapse');
    // The inline body of the expanded card is replaced by the placeholder.
    expect(html).toContain('Opened in expanded view…');
  });

  test('non-matching symbol expands nothing', () => {
    const html = renderPanel('baz');
    expect(html).not.toContain('collapse');
  });
});
