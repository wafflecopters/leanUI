/**
 * URL-parameter → preset/symbol resolution (pure; no React, no window).
 *
 * Supports deep links like `/?preset=real-analysis&symbol=limitAdd`:
 *   - `preset` is matched against slugified preset names ("Real Analysis
 *     (chain rule)" → "real-analysis-chain-rule"), exact first, then unique
 *     prefix — so the natural short form `real-analysis` works without
 *     encoding the full display name in the URL.
 *   - `symbol` names a declaration to auto-expand in the WYSIWYG editor. The
 *     declaration list only exists after the async Lean analyze round-trip, so
 *     the page holds the pending symbol until declarations arrive, resolves it
 *     here (exact, then case-insensitive), and expands that card one-shot.
 */
import type { LeanPreset } from './presets';

/** Kebab-case slug of a preset display name: lowercase alphanumeric runs
 *  joined by `-` ("Nat Math (from scratch)" → "nat-math-from-scratch",
 *  "Mathlib (∑, ring)" → "mathlib-ring"). */
export function presetSlug(name: string): string {
  return name
    .toLowerCase()
    .split(/[^a-z0-9]+/)
    .filter(Boolean)
    .join('-');
}

/**
 * Find the preset a `?preset=` param refers to. Matching, most to least
 * specific: exact slug first, then slug prefix (`real-analysis` →
 * `real-analysis-chain-rule`). Prefix ties go to the first preset in
 * declaration order — stable and predictable. Returns null when nothing
 * matches.
 */
export function findPresetBySlug(presets: readonly LeanPreset[], param: string): LeanPreset | null {
  const want = presetSlug(param);
  if (want.length === 0) return null;
  const slugged = presets.map((p) => ({ p, slug: presetSlug(p.name) }));
  const exact = slugged.find((s) => s.slug === want);
  if (exact) return exact.p;
  const prefix = slugged.find((s) => s.slug.startsWith(want));
  return prefix ? prefix.p : null;
}

export interface EditorUrlParams {
  /** Preset the URL asks for (resolved), or null. */
  preset: LeanPreset | null;
  /** Raw declaration name to auto-expand, or null. */
  symbol: string | null;
}

/** Parse `?preset=…&symbol=…` (accepts a search string or URLSearchParams). */
export function parseEditorUrlParams(
  search: string | URLSearchParams,
  presets: readonly LeanPreset[],
): EditorUrlParams {
  const params = typeof search === 'string' ? new URLSearchParams(search) : search;
  const presetParam = params.get('preset')?.trim() ?? '';
  const symbolParam = params.get('symbol')?.trim() ?? '';
  return {
    preset: presetParam ? findPresetBySlug(presets, presetParam) : null,
    symbol: symbolParam || null,
  };
}

/**
 * Resolve a `?symbol=` param against the analyzed declaration names: exact
 * match first, then case-insensitive (URLs get hand-typed). Returns the
 * CANONICAL declaration name (so downstream comparisons are exact), or null.
 */
export function resolveSymbolName(
  declarations: ReadonlyArray<{ name: string }>,
  symbol: string,
): string | null {
  const exact = declarations.find((d) => d.name === symbol);
  if (exact) return exact.name;
  const lower = symbol.toLowerCase();
  const ci = declarations.find((d) => d.name.toLowerCase() === lower);
  return ci ? ci.name : null;
}
