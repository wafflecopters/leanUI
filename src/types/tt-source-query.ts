/**
 * Source Position to Path Resolution
 *
 * This module bridges source positions (line/column) to IndexPaths.
 * It's a separate layer on top of the core type query API, used when
 * queries originate from user text selections.
 *
 * Architecture:
 * - SourceMap maps IndexPath → SourceRange (built by parser)
 * - This module provides the reverse: SourceRange → IndexPath
 */

import {
  SourceMap,
  SourceRange,
  SourcePos,
  IndexPath,
  deserializeIndexPath
} from './source-position';

// ============================================================================
// Types
// ============================================================================

/**
 * A candidate path that covers a source position.
 */
interface PathCandidate {
  pathKey: string;
  path: IndexPath;
  range: SourceRange;
  // How many characters the range spans
  rangeSize: number;
}

/**
 * Result of resolving a source position to a path.
 */
export type SourceToPathResult =
  | { success: true; path: IndexPath; range: SourceRange }
  | { success: false; reason: string };

// ============================================================================
// Position Utilities
// ============================================================================

/**
 * Check if a position is within a range.
 *
 * @param pos - The position to check
 * @param range - The range to check against
 * @returns true if pos is within range (inclusive start, exclusive end)
 */
export function positionInRange(pos: SourcePos, range: SourceRange): boolean {
  // Check if position is after start
  if (pos.line < range.start.line) return false;
  if (pos.line === range.start.line && pos.col < range.start.col) return false;

  // Check if position is before end
  if (pos.line > range.end.line) return false;
  if (pos.line === range.end.line && pos.col >= range.end.col) return false;

  return true;
}

/**
 * Check if one range is fully contained within another.
 *
 * @param inner - The potentially inner range
 * @param outer - The potentially outer range
 * @returns true if inner is fully contained in outer
 */
export function rangeContainedIn(inner: SourceRange, outer: SourceRange): boolean {
  return positionInRange(inner.start, outer) &&
         (positionInRange(inner.end, outer) ||
          // Handle case where inner.end equals outer.end (both exclusive)
          (inner.end.line === outer.end.line && inner.end.col <= outer.end.col));
}

/**
 * Calculate the "size" of a range for comparison purposes.
 * Smaller ranges are more specific (better matches).
 */
function rangeSize(range: SourceRange): number {
  // Use character offset if available and valid (end > start)
  // Some callers set pos: 0 for both which is meaningless
  if (range.start.pos !== undefined && range.end.pos !== undefined &&
      range.end.pos > range.start.pos) {
    return range.end.pos - range.start.pos;
  }

  // Fall back to line/col based estimate
  const lineSpan = range.end.line - range.start.line;
  if (lineSpan === 0) {
    return range.end.col - range.start.col;
  }
  return lineSpan * 100 + range.end.col;
}

// ============================================================================
// Source to Path Resolution
// ============================================================================

/**
 * Find the most specific path that contains a source position.
 *
 * When multiple paths cover a position, we select the smallest (most specific) one.
 * This matches user intuition: clicking on `x` in `f x y` should select just `x`,
 * not the entire application.
 *
 * @param pos - The source position (line, column)
 * @param sourceMap - The SourceMap from parsing
 * @returns The most specific path containing the position
 */
export function resolvePositionToPath(
  pos: SourcePos,
  sourceMap: SourceMap
): SourceToPathResult {
  const candidates: PathCandidate[] = [];

  // Find all ranges that contain this position
  for (const [pathKey, range] of sourceMap.entries()) {
    if (positionInRange(pos, range)) {
      candidates.push({
        pathKey,
        path: deserializeIndexPath(pathKey),
        range,
        rangeSize: rangeSize(range)
      });
    }
  }

  if (candidates.length === 0) {
    return { success: false, reason: 'No AST node covers this position' };
  }

  // Sort by range size (smallest first) to get most specific
  candidates.sort((a, b) => a.rangeSize - b.rangeSize);

  const best = candidates[0];
  return {
    success: true,
    path: best.path,
    range: best.range
  };
}

/**
 * Find all paths that overlap with a source range (for selection).
 *
 * When the user selects a range of text, we want to find paths that
 * are fully contained within that selection.
 *
 * @param selection - The selected range
 * @param sourceMap - The SourceMap from parsing
 * @returns Array of paths fully contained in the selection
 */
export function resolveSelectionToPaths(
  selection: SourceRange,
  sourceMap: SourceMap
): Array<{ path: IndexPath; range: SourceRange }> {
  const results: Array<{ path: IndexPath; range: SourceRange }> = [];

  for (const [pathKey, range] of sourceMap.entries()) {
    // Check if this range is fully contained in the selection
    if (rangeContainedIn(range, selection)) {
      results.push({
        path: deserializeIndexPath(pathKey),
        range
      });
    }
  }

  // Sort by range size (smallest first)
  results.sort((a, b) => rangeSize(a.range) - rangeSize(b.range));

  return results;
}

/**
 * Find the smallest path that fully contains a selection.
 *
 * This is useful when the user selects a piece of text and we want
 * to find the tightest AST node that contains the entire selection.
 *
 * @param selection - The selected range
 * @param sourceMap - The SourceMap from parsing
 * @returns The smallest path containing the entire selection
 */
export function resolveSelectionToContainingPath(
  selection: SourceRange,
  sourceMap: SourceMap
): SourceToPathResult {
  const candidates: PathCandidate[] = [];

  for (const [pathKey, range] of sourceMap.entries()) {
    // Check if this range fully contains the selection
    if (rangeContainedIn(selection, range)) {
      candidates.push({
        pathKey,
        path: deserializeIndexPath(pathKey),
        range,
        rangeSize: rangeSize(range)
      });
    }
  }

  if (candidates.length === 0) {
    return { success: false, reason: 'No AST node contains this selection' };
  }

  // Sort by range size (smallest first)
  candidates.sort((a, b) => a.rangeSize - b.rangeSize);

  const best = candidates[0];
  return {
    success: true,
    path: best.path,
    range: best.range
  };
}

// ============================================================================
// High-Level Query API
// ============================================================================

import { TTKTerm, TTKContext, prettyPrint } from './tt-kernel';
import { queryTypeAtPath, TypeQueryResult, ElaborationContext } from './tt-type-query';

/**
 * Extend context with a definition binding (for recursive references).
 * The name is added at the end of the context so it doesn't affect de Bruijn indices.
 */
function addDefinitionToContext(
  ctx: TTKContext,
  name: string | undefined,
  type: TTKTerm | undefined
): TTKContext {
  if (!name || !type) return ctx;
  // Add at end so de Bruijn indices stay correct for local bindings
  return [...ctx, { name, type }];
}

/**
 * Check if a character is whitespace or a delimiter (not part of an identifier).
 */
function isWhitespaceOrDelimiter(char: string | undefined): boolean {
  if (!char) return true;
  return /[\s(){}[\]:=\\,.]/.test(char);
}

/**
 * Adjust cursor position to snap to the nearest token.
 *
 * When the cursor is at the boundary between whitespace and a token,
 * snap to the token side so that left-edge and right-edge of a token
 * resolve to the same AST node.
 */
function adjustPositionToToken(pos: SourcePos, sourceCode?: string): SourcePos {
  if (!sourceCode) return pos;

  const lines = sourceCode.split('\n');
  const lineIndex = pos.line - 1;  // Convert to 0-indexed
  if (lineIndex < 0 || lineIndex >= lines.length) return pos;

  const line = lines[lineIndex];
  const colIndex = pos.col - 1;  // Convert to 0-indexed

  const charAtCursor = line[colIndex];
  const charBefore = colIndex > 0 ? line[colIndex - 1] : undefined;

  // If cursor is on whitespace/delimiter and there's a token to the left, move left
  if (isWhitespaceOrDelimiter(charAtCursor) && !isWhitespaceOrDelimiter(charBefore)) {
    return { ...pos, col: pos.col - 1 };
  }

  // If cursor is on whitespace/delimiter and there's a token to the right, stay (it will be found)
  // If cursor is inside a token, stay
  return pos;
}

/**
 * Query the type at a source position.
 *
 * This is the main entry point for UI-driven type queries.
 * It combines source resolution with type inference.
 *
 * @param pos - Source position (line, column)
 * @param sourceMap - SourceMap from parsing
 * @param rootTerm - The root term to query within
 * @param rootContext - The context at the root
 * @param expectedType - Optional expected type of rootTerm (used for pattern binding types)
 * @param definitionName - Optional name of the definition being queried (for recursive references)
 * @param sourceCode - Optional source code for cursor position adjustment
 * @param elabContext - Optional elaboration context with solved types from type checking
 * @returns Type query result with the term and its type
 */
export function queryTypeAtPosition(
  pos: SourcePos,
  sourceMap: SourceMap,
  rootTerm: TTKTerm,
  rootContext: TTKContext,
  expectedType?: TTKTerm,
  definitionName?: string,
  sourceCode?: string,
  elabContext?: ElaborationContext
): TypeQueryResult & { sourceRange?: SourceRange } {
  // Step 0: Adjust position to snap to nearest token
  const adjustedPos = adjustPositionToToken(pos, sourceCode);

  // Step 1: Resolve position to path
  const pathResult = resolvePositionToPath(adjustedPos, sourceMap);
  if (!pathResult.success) {
    return { success: false, error: pathResult.reason };
  }

  // Step 2: Extend context with the definition itself for recursive references
  const contextWithDef = addDefinitionToContext(rootContext, definitionName, expectedType);

  // Step 3: Query type at path (pass elabContext for solved types)
  const typeResult = queryTypeAtPath(rootTerm, contextWithDef, pathResult.path, expectedType, elabContext);
  if (!typeResult.success) {
    return typeResult;
  }

  // Step 4: Check if cursor is on/near a binder name
  // Create a zero-width selection at the cursor position for binder detection
  const cursorSelection: SourceRange = {
    start: adjustedPos,
    end: { ...adjustedPos, col: adjustedPos.col + 1 }  // 1-char width for binder detection
  };

  const pathExpectedType = computeExpectedTypeAtPath(expectedType, pathResult.path);
  const binderResult = checkBinderNameSelection(
    cursorSelection,
    pathResult.range,
    typeResult.term,
    pathExpectedType,
    typeResult.context,
    sourceMap
  );
  if (binderResult) {
    return {
      ...binderResult,
      sourceRange: cursorSelection
    };
  }

  // Combine results
  return {
    ...typeResult,
    sourceRange: pathResult.range
  };
}

/**
 * Query the type for a text selection.
 *
 * @param selection - The selected range
 * @param sourceMap - SourceMap from parsing
 * @param rootTerm - The root term
 * @param rootContext - The context at the root
 * @param expectedType - Optional expected type of rootTerm (used for pattern binding types)
 * @param definitionName - Optional name of the definition being queried (for recursive references)
 * @param elabContext - Optional elaboration context with solved types from type checking
 * @returns Type query result
 */
export function queryTypeForSelection(
  selection: SourceRange,
  sourceMap: SourceMap,
  rootTerm: TTKTerm,
  rootContext: TTKContext,
  expectedType?: TTKTerm,
  definitionName?: string,
  elabContext?: ElaborationContext
): TypeQueryResult & { sourceRange?: SourceRange } {
  // Find the smallest containing path
  const pathResult = resolveSelectionToContainingPath(selection, sourceMap);
  if (!pathResult.success) {
    return { success: false, error: pathResult.reason };
  }

  // Extend context with the definition itself for recursive references
  const contextWithDef = addDefinitionToContext(rootContext, definitionName, expectedType);

  // Query type at path (pass elabContext for solved types)
  const typeResult = queryTypeAtPath(rootTerm, contextWithDef, pathResult.path, expectedType, elabContext);
  if (!typeResult.success) {
    return typeResult;
  }

  // Check if the selection is exactly on a binder name
  // A lambda's source range starts at the binder name (e.g., "x y => body" starts at "x")
  // If the selection starts at the same position as the containing lambda AND
  // the selection is small (just the binder name), return the domain type instead
  //
  // We need to compute the expected type for this specific path - the type inference
  // tracked it through navigation, so we can reconstruct it by following the same path
  const pathExpectedType = computeExpectedTypeAtPath(expectedType, pathResult.path);
  const binderResult = checkBinderNameSelection(
    selection,
    pathResult.range,
    typeResult.term,
    pathExpectedType,
    typeResult.context,
    sourceMap
  );
  if (binderResult) {
    return {
      ...binderResult,
      sourceRange: selection  // Use the actual selection range, not the lambda's range
    };
  }

  return {
    ...typeResult,
    sourceRange: pathResult.range
  };
}

/**
 * Compute the expected type at a given path by following the same navigation
 * through Pi types that queryTypeAtPath does through lambdas.
 *
 * For example, if we have:
 * - expectedType: (A : Type) -> (B : Type) -> A -> B -> A
 * - path: ["body", "body", "body"]  (navigating to the 4th lambda)
 *
 * We navigate through the Pi type: body -> body -> body
 * Result: B -> A (the expected type for the 4th lambda)
 */
function computeExpectedTypeAtPath(
  expectedType: TTKTerm | undefined,
  path: IndexPath
): TTKTerm | undefined {
  if (!expectedType) return undefined;

  let current = expectedType;
  for (const segment of path) {
    if (segment.kind !== 'field') continue;

    if (segment.name === 'body' && current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
      current = current.body;
    }
    // For other path segments (like 'domain', 'fn', 'arg'), we don't have
    // a corresponding expected type structure, so we stop tracking
  }
  return current;
}

/**
 * Check if a type contains any holes.
 */
function typeHasHoles(type: TTKTerm): boolean {
  switch (type.tag) {
    case 'Hole': return true;
    case 'Binder': return typeHasHoles(type.domain) || typeHasHoles(type.body);
    case 'App': return typeHasHoles(type.fn) || typeHasHoles(type.arg);
    case 'Annot': return typeHasHoles(type.term) || typeHasHoles(type.type);
    case 'Const': return false;  // Don't check sort annotation
    case 'Match':
      if (typeHasHoles(type.scrutinee)) return true;
      return type.clauses.some(c => typeHasHoles(c.rhs));
    case 'Var':
    case 'Sort': return false;
  }
}

/**
 * Check if a selection is exactly on a binder name and return the variable's type.
 *
 * Lambda source ranges can start in two ways:
 * - Outer lambda with backslash: "\ A B x => body" starts at "\"
 * - Nested lambdas (no extra backslash): "B x => body" starts at "B"
 *
 * When selecting just "A" or "B", we want to show the binder's type, not the lambda's type.
 */
function checkBinderNameSelection(
  selection: SourceRange,
  containingRange: SourceRange,
  term: TTKTerm,
  expectedType: TTKTerm | undefined,
  context: TTKContext,
  sourceMap: SourceMap
): { success: true; term: TTKTerm; type: TTKTerm; context: TTKContext } | null {
  // Only applies to lambdas
  if (term.tag !== 'Binder' || term.binderKind.tag !== 'BLam') {
    return null;
  }

  const selectionSize = rangeSize(selection);
  const binderNameLen = term.name.length;

  // Selection must be small enough to be just this binder's name (allow 1 char tolerance for cursor)
  // This prevents "B x" (size 3) from matching binder "B" (size 1)
  if (selectionSize > binderNameLen + 1) {
    return null;
  }

  // Check if selection is in the "binder name region" of the lambda
  // For nested lambdas: selection should start at the same position as the containing range
  // For outer lambdas with backslash: selection is AFTER the lambda start but BEFORE the body starts
  const selectionIsAtStart = (selection.start.line === containingRange.start.line &&
                               selection.start.col === containingRange.start.col);

  let selectionIsInBinderRegion = selectionIsAtStart;

  if (!selectionIsAtStart) {
    // Find the body's source range to check if selection is in the binder region
    const bodyRange = findBodyRange(containingRange, sourceMap);
    if (bodyRange) {
      const onSameLine = selection.start.line === containingRange.start.line;
      const afterLambdaStart = selection.start.col > containingRange.start.col;
      const beforeBodyStart = selection.end.col <= bodyRange.start.col;
      const withinLambda = selection.end.col <= containingRange.end.col;

      selectionIsInBinderRegion = onSameLine && afterLambdaStart && beforeBodyStart && withinLambda;
    }
  }

  if (!selectionIsInBinderRegion) {
    return null;
  }

  // Get the binder's domain type
  // If the lambda's domain has holes and we have an expected Pi type, use the Pi's domain
  let domainType = term.domain;
  if (typeHasHoles(domainType) && expectedType?.tag === 'Binder' && expectedType.binderKind.tag === 'BPi') {
    domainType = expectedType.domain;
  }

  // Create a synthetic term representing the bound variable
  const syntheticVar: TTKTerm = { tag: 'Const', name: term.name, type: domainType };

  return {
    success: true,
    term: syntheticVar,
    type: domainType,
    context
  };
}

/**
 * Find the body's source range - the range that starts closest to (but after)
 * the containing range's start, on the same line.
 */
function findBodyRange(containingRange: SourceRange, sourceMap: SourceMap): SourceRange | null {
  let bodyRange: SourceRange | null = null;
  let closestStart = Infinity;

  for (const [, range] of sourceMap.entries()) {
    if (range.start.line !== containingRange.start.line) continue;
    if (range.start.col <= containingRange.start.col) continue;
    if (range.end.col > containingRange.end.col) continue;

    const distFromStart = range.start.col - containingRange.start.col;
    if (distFromStart < closestStart) {
      closestStart = distFromStart;
      bodyRange = range;
    }
  }

  return bodyRange;
}

/**
 * Format a type query result for display.
 *
 * @param result - The type query result
 * @returns A formatted string suitable for UI display
 */
export function formatTypeQueryResult(result: TypeQueryResult): string {
  if (!result.success) {
    return `Error: ${result.error}`;
  }

  const names = result.context.map(b => b.name);
  const termStr = prettyPrint(result.term, names);
  const typeStr = prettyPrint(result.type, names);

  return `${termStr}\n  : ${typeStr}`;
}
