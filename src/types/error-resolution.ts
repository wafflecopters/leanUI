/**
 * Error Resolution System
 *
 * Maps type check errors (which occur on kernel terms with kernel paths)
 * back to source code locations using the three-map architecture:
 *
 * TypeCheckError → kernel path → surface path → source range
 */

import { TypeCheckError } from '../compiler/kernel';
import { CheckError } from '../compiler/term';
import { NameResolutionError } from './name-resolution';
import { ElabMap, SourceMap, SourceRange, IndexPath, serializeIndexPath } from './source-position';
import { lookupSurfacePath } from '../compiler/elab';

// ============================================================================
// Error Location Resolution
// ============================================================================

/**
 * Resolve a TypeCheckError to a source location.
 *
 * Pipeline:
 * 1. Extract kernel path from error
 * 2. Map kernel path → surface path (via ElabMap)
 * 3. Map surface path → source range (via SourceMap)
 * 4. Fall back to parent paths if exact match not found
 *
 * @param error - The type check error to resolve
 * @param elabMap - Maps kernel paths to surface paths
 * @param sourceMap - Maps surface paths to source ranges
 * @returns Source range if found, null otherwise
 */
export function resolveErrorLocation(
  error: TypeCheckError,
  elabMap: ElabMap,
  sourceMap: SourceMap
): SourceRange | null {
  // If error has no path, can't resolve
  if (!error.termPath) {
    return null;
  }

  // Step 1: Get surface path from kernel path
  const surfaceKey = lookupSurfacePath(error.termPath, elabMap);
  if (!surfaceKey) {
    return null;
  }

  // Step 2: Get source range from surface path
  const sourceRange = sourceMap.get(surfaceKey);
  if (sourceRange) {
    return sourceRange;
  }

  // Step 3: Try parent paths in surface map
  // Walk up the surface path looking for a match
  const surfacePath = surfaceKey.split('.').filter(s => s.length > 0);
  for (let i = surfacePath.length - 1; i >= 0; i--) {
    const parentKey = surfacePath.slice(0, i).join('.');
    const parentRange = sourceMap.get(parentKey);
    if (parentRange) {
      return parentRange;
    }
  }

  // No match found
  return null;
}

/**
 * Resolve a CheckError to a source location.
 *
 * Similar to resolveErrorLocation but for CheckError from declaration checking.
 */
export function resolveCheckErrorLocation(
  error: CheckError,
  elabMap: ElabMap,
  sourceMap: SourceMap
): SourceRange | null {
  // If error has no path, can't resolve
  if (!error.path || error.path.length === 0) {
    return null;
  }

  // CheckError already has IndexPath, serialize it
  const kernelKey = serializeIndexPath(error.path);

  // Step 1: Get surface path from kernel path
  // First try exact match
  let surfaceKey = elabMap.get(kernelKey);

  // If no exact match, try parent paths and preserve the suffix
  if (!surfaceKey) {
    for (let i = error.path.length - 1; i >= 0; i--) {
      const parentPath = error.path.slice(0, i);
      const parentKey = serializeIndexPath(parentPath);
      const parentSurfaceKey = elabMap.get(parentKey);
      if (parentSurfaceKey) {
        // Found a parent match - append the remaining suffix
        const suffix = error.path.slice(i);
        const suffixKey = serializeIndexPath(suffix);
        surfaceKey = suffixKey ? `${parentSurfaceKey}.${suffixKey}` : parentSurfaceKey;
        break;
      }
    }
  }

  if (!surfaceKey) {
    return null;
  }

  // Step 2: Get source range from surface path
  const sourceRange = sourceMap.get(surfaceKey);
  if (sourceRange) {
    return sourceRange;
  }

  // Step 3: Try parent paths in source map
  const surfacePath = surfaceKey.split('.').filter(s => s.length > 0);
  for (let i = surfacePath.length - 1; i >= 0; i--) {
    const parentKey = surfacePath.slice(0, i).join('.');
    const parentRange = sourceMap.get(parentKey);
    if (parentRange) {
      return parentRange;
    }
  }

  return null;
}

/**
 * Resolve a NameResolutionError to a source location.
 *
 * Name resolution errors already have surface paths (not kernel paths),
 * so we skip the ElabMap step and go directly to the SourceMap.
 *
 * @param error - The name resolution error to resolve
 * @param sourceMap - Maps surface paths to source ranges
 * @returns Source range if found, null otherwise
 */
export function resolveNameResolutionErrorLocation(
  error: NameResolutionError,
  sourceMap: SourceMap
): SourceRange | null {
  // Serialize the path
  const pathKey = serializeIndexPath(error.path);

  // Try to find in source map
  const sourceRange = sourceMap.get(pathKey);
  if (sourceRange) {
    return sourceRange;
  }

  // Try parent paths
  for (let i = error.path.length - 1; i >= 0; i--) {
    const parentPath = error.path.slice(0, i);
    const parentKey = serializeIndexPath(parentPath);
    const parentRange = sourceMap.get(parentKey);
    if (parentRange) {
      return parentRange;
    }
  }

  return null;
}

// ============================================================================
// Error Formatting
// ============================================================================

/**
 * Format an error with source location context.
 *
 * Shows the error message along with the source line and a caret pointing
 * to the error location.
 *
 * @param errorMessage - The error message
 * @param sourceRange - The source range (if available)
 * @param sourceText - The full source text
 * @returns Formatted error string
 */
export function formatErrorWithLocation(
  errorMessage: string,
  sourceRange: SourceRange | null,
  sourceText: string
): string {
  if (!sourceRange) {
    // No location info, just return the message
    return errorMessage;
  }

  const lines = sourceText.split('\n');
  const errorLine = lines[sourceRange.start.line - 1]; // lines are 1-indexed

  if (!errorLine) {
    // Line doesn't exist, just return message with location
    return `${errorMessage}\n  at line ${sourceRange.start.line}, column ${sourceRange.start.col}`;
  }

  // Build formatted output with context
  const output: string[] = [];

  // Error message
  output.push(errorMessage);
  output.push('');

  // Location info
  output.push(`  at line ${sourceRange.start.line}, column ${sourceRange.start.col}`);

  // Source line
  output.push(`  ${errorLine}`);

  // Caret pointing to error
  const caretPadding = ' '.repeat(sourceRange.start.col + 1); // +1 for the "  " prefix
  const caretLength = Math.max(1, sourceRange.end.col - sourceRange.start.col);
  const caret = '^'.repeat(caretLength);
  output.push(`  ${caretPadding}${caret}`);

  return output.join('\n');
}

/**
 * Format a CheckError with source location context.
 */
export function formatCheckErrorWithLocation(
  error: CheckError,
  sourceRange: SourceRange | null,
  sourceText: string
): string {
  return formatErrorWithLocation(error.message, sourceRange, sourceText);
}

/**
 * Format multiple errors with source locations.
 */
export function formatMultipleErrors(
  errors: Array<{ message: string; range: SourceRange | null }>,
  sourceText: string
): string {
  if (errors.length === 0) {
    return 'No errors';
  }

  if (errors.length === 1) {
    return formatErrorWithLocation(errors[0].message, errors[0].range, sourceText);
  }

  // Multiple errors
  const output: string[] = [];
  output.push(`Found ${errors.length} errors:\n`);

  errors.forEach((error, index) => {
    output.push(`Error ${index + 1}:`);
    output.push(formatErrorWithLocation(error.message, error.range, sourceText));
    output.push('');
  });

  return output.join('\n');
}
