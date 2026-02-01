/**
 * Type-at-Cursor Infrastructure
 *
 * Provides two layers:
 * 1. TypeInfoMap — collected during type checking, maps kernel IndexPaths to type info
 * 2. Cursor-to-path — maps cursor positions/selections to the most specific IndexPath
 *
 * Together these enable: cursor position → surface path → kernel path → type info
 */

import { TTKTerm, TTKContext, prettyPrint } from "./kernel";
import { SourceMap, SourceRange, ElabMap, serializeIndexPath, IndexPath } from "../types/source-position";
import { DefinitionsMap } from "./term";
import { whnf, WhnfContext } from "./whnf";
import { subst } from "./subst";

// ============================================================================
// Layer 1: Type Info Collection (populated during type checking)
// ============================================================================

/**
 * Type information for a single sub-expression, collected during type checking.
 */
export interface TypeInfoEntry {
  /** The inferred type of this sub-expression */
  type: TTKTerm;
  /** The typing context at this point (variables in scope with their types) */
  context: TTKContext;
  /** If this sub-expression was checked against an expected type, that type */
  expectedType?: TTKTerm;
  /** Serialized kernel IndexPath */
  kernelPath: string;
}

/**
 * Maps serialized kernel IndexPaths to type info entries.
 * Built during type checking by TCEnv.recordTypeInfo().
 */
export type TypeInfoMap = Map<string, TypeInfoEntry>;

// ============================================================================
// Layer 2: Cursor Position → IndexPath
// ============================================================================

/**
 * Find the most specific surface path containing the given cursor position.
 *
 * Iterates all entries in the SourceMap and returns the one with the smallest
 * span that contains the cursor. This gives the most specific (deepest) sub-expression.
 */
export function findPathAtCursor(
  pos: number,
  sourceMap: SourceMap,
): string | undefined {
  let bestPath: string | undefined;
  let bestSpan = Infinity;

  for (const [surfacePath, range] of sourceMap) {
    if (range.start.pos <= pos && pos < range.end.pos) {
      const span = range.end.pos - range.start.pos;
      if (span < bestSpan) {
        bestSpan = span;
        bestPath = surfacePath;
      }
    }
  }

  return bestPath;
}

/**
 * Find the most specific surface path fully containing the given selection range.
 *
 * The source range must fully contain [startPos, endPos].
 * Returns the smallest such range (most specific sub-expression).
 */
export function findPathForSelection(
  startPos: number,
  endPos: number,
  sourceMap: SourceMap,
): string | undefined {
  const selSpan = endPos - startPos;

  // Containing entries: entry fully contains the selection. Pick the smallest.
  let bestContaining: string | undefined;
  let bestContainingSpan = Infinity;

  // Contained-by entries: selection fully contains the entry.
  // Only consider these as fallback when the entry covers most of the selection
  // (e.g. user selected "(expr)" including parens — the entry "expr" covers ~80%).
  // Pick the largest such entry.
  let bestContained: string | undefined;
  let bestContainedSpan = -1;

  for (const [surfacePath, range] of sourceMap) {
    const span = range.end.pos - range.start.pos;
    const entryContainsSel = range.start.pos <= startPos && endPos <= range.end.pos;
    const selContainsEntry = startPos <= range.start.pos && range.end.pos <= endPos;

    if (entryContainsSel) {
      if (span < bestContainingSpan) {
        bestContainingSpan = span;
        bestContaining = surfacePath;
      }
    } else if (selContainsEntry && span >= selSpan * 0.5) {
      // Only consider contained-by entries that cover at least 50% of the selection.
      // This handles sloppy selections with extra whitespace/parens, but rejects
      // small fragments like "a" when the user selected "a b".
      if (span > bestContainedSpan) {
        bestContainedSpan = span;
        bestContained = surfacePath;
      }
    }
  }

  // If we have both, prefer the one whose span is closer to the selection span.
  // This handles sloppy selection like "(expr)" — contained "expr" is closer
  // in span than the larger containing entry.
  if (bestContaining && bestContained) {
    const containingDist = bestContainingSpan - selSpan;
    const containedDist = selSpan - bestContainedSpan;
    return containedDist <= containingDist ? bestContained : bestContaining;
  }
  return bestContaining ?? bestContained;
}

// ============================================================================
// Reverse ElabMap (surface path → kernel path)
// ============================================================================

/**
 * Build a reverse mapping from surface paths to kernel paths.
 * The ElabMap maps kernel→surface; we need surface→kernel for cursor lookups.
 */
export function buildReverseElabMap(elabMap: ElabMap): Map<string, string> {
  const reverse = new Map<string, string>();
  for (const [kernelPath, surfacePath] of elabMap) {
    reverse.set(surfacePath, kernelPath);
  }
  return reverse;
}

/**
 * Check if a surface path refers to a pattern that was explicitly written with
 * implicit braces (e.g., {A} in "right {A} b = ..."). These patterns have
 * matching kernel indices (no index shifting from auto-inserted implicits).
 *
 * Detected by the presence of openBrace/closeBrace entries in the sourceMap
 * for the pattern's parent path.
 */
function isExplicitlyImplicitPattern(surfacePath: string, sourceMap: SourceMap): boolean {
  // Extract the pattern parent path (e.g., "value.clauses[0].patterns[0]" from
  // "value.clauses[0].patterns[0].name")
  const patternMatch = surfacePath.match(/^(.*\.patterns\[\d+\])/);
  if (!patternMatch) return false;
  const patternParent = patternMatch[1];
  return sourceMap.has(patternParent + '.openBrace');
}

/**
 * Find the kernel path corresponding to a surface path.
 * If no exact match, walks up the path hierarchy (removing the last segment)
 * until finding a mapped ancestor.
 */
export function findKernelPathForSurface(
  surfacePath: string,
  reverseElabMap: Map<string, string>,
): string | undefined {
  let path = surfacePath;
  while (path !== '') {
    const kernelPath = reverseElabMap.get(path);
    if (kernelPath !== undefined) {
      // Append any suffix that was stripped during the walk-up.
      // This handles cases where the elabMap has a prefix mapping
      // (e.g. with-clause remapping) and the full sub-path isn't in the map.
      const suffix = surfacePath.substring(path.length);
      return kernelPath + suffix;
    }
    // Remove the last segment (after last '.' or '[')
    const lastDot = path.lastIndexOf('.');
    const lastBracket = path.lastIndexOf('[');
    const cutPoint = Math.max(lastDot, lastBracket);
    if (cutPoint <= 0) break;
    path = path.substring(0, cutPoint);
  }
  // Try the root path
  return reverseElabMap.get('');
}

// ============================================================================
// Top-level Query API
// ============================================================================

/**
 * Result of a type-at-cursor query.
 */
export interface TypeAtCursorResult {
  /** The inferred type (kernel term) */
  type: TTKTerm;
  /** Pretty-printed type */
  prettyType: string;
  /** Variables in scope at this point */
  context: Array<{ name: string; type: string }>;
  /** Pretty-printed expected type (if in checking position) */
  expectedType?: string;
  /** Source range of the focused sub-expression */
  sourceRange?: SourceRange;
  /** The surface and kernel paths */
  surfacePath: string;
  kernelPath: string;
}

/**
 * Query type information at a cursor position.
 *
 * Flow: cursor pos → sourceMap lookup (surface path) → reverse elabMap (kernel path)
 *       → typeInfoMap lookup → pretty-printed result
 */
export function getTypeAtCursor(
  pos: number,
  sourceMap: SourceMap,
  elabMap: ElabMap | undefined,
  typeInfoMap: TypeInfoMap | undefined,
  definitions?: DefinitionsMap,
): TypeAtCursorResult | undefined {
  if (!typeInfoMap) return undefined;

  // Try both pos and pos-1 (end-of-token), pick the smallest span
  const path1 = findPathAtCursor(pos, sourceMap);
  const path2 = pos > 0 ? findPathAtCursor(pos - 1, sourceMap) : undefined;

  let surfacePath: string | undefined;
  if (path1 !== undefined && path2 !== undefined) {
    const range1 = sourceMap.get(path1);
    const range2 = sourceMap.get(path2);
    const span1 = range1 ? range1.end.pos - range1.start.pos : Infinity;
    const span2 = range2 ? range2.end.pos - range2.start.pos : Infinity;
    surfacePath = span2 < span1 ? path2 : path1;
  } else {
    surfacePath = path1 ?? path2;
  }

  if (surfacePath === undefined) return undefined;

  return resolveTypeInfo(surfacePath, sourceMap, elabMap, typeInfoMap, definitions);
}

/**
 * Query type information for a text selection range.
 */
export function getTypeAtSelection(
  startPos: number,
  endPos: number,
  sourceMap: SourceMap,
  elabMap: ElabMap | undefined,
  typeInfoMap: TypeInfoMap | undefined,
  definitions?: DefinitionsMap,
): TypeAtCursorResult | undefined {
  if (!typeInfoMap) return undefined;

  const surfacePath = findPathForSelection(startPos, endPos, sourceMap);
  if (surfacePath === undefined) return undefined;

  return resolveTypeInfo(surfacePath, sourceMap, elabMap, typeInfoMap, definitions);
}

/**
 * Given a surface path, resolve it to type info via the elab map and type info map.
 */
function resolveTypeInfo(
  surfacePath: string,
  sourceMap: SourceMap,
  elabMap: ElabMap | undefined,
  typeInfoMap: TypeInfoMap,
  definitions?: DefinitionsMap,
): TypeAtCursorResult | undefined {
  // Try multiple strategies to find the kernel path for this surface path.
  // When implicit patterns are auto-inserted, kernel indices shift relative to
  // surface indices. The elabMap provides the correct mapping in those cases.
  // However, when the user explicitly writes an implicit pattern (e.g., {A}),
  // the surface and kernel indices align and the elabMap may be unreliable.
  //
  // Strategy: if the surface pattern is explicitly implicit (has openBrace/closeBrace
  // in sourceMap), prefer the direct surface path. Otherwise prefer the elabMap.
  const candidateKernelPaths: string[] = [];

  let elabKernelPath: string | undefined;
  if (elabMap) {
    const reverseMap = buildReverseElabMap(elabMap);
    elabKernelPath = findKernelPathForSurface(surfacePath, reverseMap);
  }

  // Check if the surface pattern was explicitly written as implicit ({...}).
  // If so, surface indices match kernel indices and the elabMap may be unreliable.
  const isExplicitImplicit = isExplicitlyImplicitPattern(surfacePath, sourceMap);

  // With-clause paths (e.g., withClauses[0].rhs.fn) have their type info merged
  // into the main declaration's typeInfoMap under the surface path key. The direct
  // surface path must be tried first, since the elabMap resolves to the main
  // declaration's kernel paths (for the auxiliary call, not the with-clause body).
  const isWithClausePath = surfacePath.includes('.withClauses[');

  if (isExplicitImplicit || isWithClausePath) {
    // Prefer direct surface path
    candidateKernelPaths.push(surfacePath);
    if (elabKernelPath !== undefined && elabKernelPath !== surfacePath) {
      candidateKernelPaths.push(elabKernelPath);
    }
  } else {
    // Prefer elabMap for normal patterns (handles implicit index shifting)
    if (elabKernelPath !== undefined) {
      candidateKernelPaths.push(elabKernelPath);
    }
    if (!candidateKernelPaths.includes(surfacePath)) {
      candidateKernelPaths.push(surfacePath);
    }
  }

  // Surface paths may differ from kernel paths due to syntactic sugar.
  // Generate additional candidates by normalizing known surface-to-kernel mismatches:
  //
  // 1. Named patterns: {a:=Succ a} produces ".pattern.name" in surface
  //    but kernel uses just ".name" (no .pattern. segment)
  //
  // 2. Let bindings: `let x = v in body` produces ".bindings[0].value" in surface
  //    but kernel uses ".value" (single-binding let) or nested ".body.value" (multi-let)
  const extraCandidates: string[] = [];
  for (const candidate of candidateKernelPaths) {
    if (candidate.includes('.pattern.')) {
      extraCandidates.push(candidate.replace(/\.pattern\./g, '.'));
    }
    // Strip ".bindings[N]." → "." for let value/name paths
    const letMatch = candidate.match(/\.bindings\[\d+\]\.(value|name)$/);
    if (letMatch) {
      extraCandidates.push(candidate.replace(/\.bindings\[\d+\]\./, '.'));
    }
  }
  for (const extra of extraCandidates) {
    if (!candidateKernelPaths.includes(extra)) {
      candidateKernelPaths.push(extra);
    }
  }

  // Try each candidate kernel path, pick the first one with type info
  let kernelPath: string | undefined;
  let info: TypeInfoEntry | undefined;

  for (const candidate of candidateKernelPaths) {
    info = typeInfoMap.get(candidate);
    if (info) {
      kernelPath = candidate;
      break;
    }
  }

  // If no exact match, walk up from each candidate to find a parent entry
  if (!info) {
    for (const candidate of candidateKernelPaths) {
      let walkPath = candidate;
      while (walkPath !== '') {
        const lastDot = walkPath.lastIndexOf('.');
        const lastBracket = walkPath.lastIndexOf('[');
        const cutPoint = Math.max(lastDot, lastBracket);
        if (cutPoint <= 0) break;
        walkPath = walkPath.substring(0, cutPoint);
        info = typeInfoMap.get(walkPath);
        if (info) {
          kernelPath = walkPath;
          // When we walk up to a parent, also update surfacePath to match.
          // This prevents showing a narrow expression (e.g., "Succ") with
          // the parent's type (e.g., Nat) — instead show the full pattern.
          if (elabMap) {
            const parentSurface = elabMap.get(walkPath);
            if (parentSurface && sourceMap.has(parentSurface)) {
              surfacePath = parentSurface;
            }
          }
          // Fallback: if the walked-up kernel path matches a sourceMap entry directly
          if (sourceMap.has(walkPath)) {
            surfacePath = walkPath;
          }
          break;
        }
      }
      if (info) break;
    }
    if (!info) return undefined;
  }

  // Normalize types for display if definitions are available
  const norm = (t: TTKTerm): TTKTerm =>
    definitions ? normalizeForDisplay(t, definitions) : t;

  // Build pretty-printed context
  const contextNames = info.context.map(c => c.name).reverse();
  const prettyContext: Array<{ name: string; type: string }> = [];
  for (let i = 0; i < info.context.length; i++) {
    const entry = info.context[i];
    // For pretty-printing each entry's type, use the context up to that point
    const entryContextNames = info.context.slice(0, i).map(c => c.name).reverse();
    prettyContext.push({
      name: entry.name,
      type: prettyPrint(norm(entry.type), entryContextNames),
    });
  }

  return {
    type: info.type,
    prettyType: prettyPrint(norm(info.type), contextNames),
    context: prettyContext,
    expectedType: info.expectedType
      ? prettyPrint(norm(info.expectedType), contextNames)
      : undefined,
    sourceRange: sourceMap.get(surfacePath),
    surfacePath,
    kernelPath: kernelPath!,
  };
}

// ============================================================================
// Display Normalization (δ/ι/β/ζ with stuck-term awareness)
// ============================================================================

/**
 * Collect an application spine: `f a1 a2 a3` → { head: f, args: [a1, a2, a3] }
 */
function collectSpine(term: TTKTerm): { head: TTKTerm; args: TTKTerm[] } {
  const args: TTKTerm[] = [];
  let current = term;
  while (current.tag === 'App') {
    args.unshift(current.arg);
    current = current.fn;
  }
  return { head: current, args };
}

function rebuildApp(head: TTKTerm, args: TTKTerm[]): TTKTerm {
  let result = head;
  for (const arg of args) {
    result = { tag: 'App', fn: result, arg };
  }
  return result;
}

/**
 * Normalize a term for display, with definition unfolding (δ) and pattern
 * matching (ι). Unlike raw whnf, this recurses into subterms. Unlike naive
 * full normalization, it detects stuck applications (where a definition was
 * unfolded but the resulting Match couldn't reduce) and keeps the original
 * constant name for readability.
 */
function normalizeForDisplay(term: TTKTerm, definitions: DefinitionsMap, fuel: number = 500): TTKTerm {
  if (fuel <= 0) return term;

  const { head: origHead, args: origArgs } = collectSpine(term);

  // If head is a Const applied to args, try whnf on the full application
  if (origHead.tag === 'Const' && origArgs.length > 0) {
    const ctx: WhnfContext = { definitions, fuel };
    const reduced = whnf(term, ctx);
    const { head: redHead } = collectSpine(reduced);

    if (redHead.tag !== 'Match') {
      // Successful reduction (head is now a constructor, Var, etc.) — recurse
      return normSubterms(reduced, definitions, fuel - 1);
    }
    // Stuck match — keep the original Const name, just normalize args
    const normArgs = origArgs.map(a => normalizeForDisplay(a, definitions, fuel - 1));
    return rebuildApp(origHead, normArgs);
  }

  // For non-Const heads or bare Const: whnf then normalize subterms
  const ctx: WhnfContext = { definitions, fuel };
  const reduced = whnf(term, ctx);
  return normSubterms(reduced, definitions, fuel - 1);
}

function normSubterms(term: TTKTerm, definitions: DefinitionsMap, fuel: number): TTKTerm {
  if (fuel <= 0) return term;
  switch (term.tag) {
    case 'Var':
    case 'Sort':
    case 'Const':
    case 'Hole':
    case 'Meta':
    case 'ULevel':
    case 'ULit':
    case 'UOmega':
      return term;

    case 'App': {
      // For fn: only normalize subterms (don't re-whnf a stuck Const)
      const fn = normSubterms(term.fn, definitions, fuel - 1);
      // For arg: full normalize (may trigger new δ/ι reductions)
      const arg = normalizeForDisplay(term.arg, definitions, fuel - 1);
      if (fn.tag === 'Binder' && fn.binderKind.tag === 'BLam') {
        return normalizeForDisplay(subst(0, arg, fn.body), definitions, fuel - 1);
      }
      return { tag: 'App', fn, arg };
    }

    case 'Binder': {
      if (term.binderKind.tag === 'BLet') {
        return normalizeForDisplay(subst(0, term.binderKind.defVal, term.body), definitions, fuel - 1);
      }
      const domain = normalizeForDisplay(term.domain, definitions, fuel - 1);
      const body = normalizeForDisplay(term.body, definitions, fuel - 1);
      return { tag: 'Binder', name: term.name, binderKind: term.binderKind, domain, body };
    }

    case 'Annot':
      return normalizeForDisplay(term.term, definitions, fuel - 1);

    case 'Match': {
      // Stuck match — only normalize scrutinee, not clause bodies
      const scrutinee = normalizeForDisplay(term.scrutinee, definitions, fuel - 1);
      return { tag: 'Match', scrutinee, clauses: term.clauses };
    }
  }
}
