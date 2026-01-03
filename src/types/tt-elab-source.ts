/**
 * Elaboration with source position tracking
 *
 * This module extends the elaborator to track the correspondence between
 * surface (un-elaborated) and kernel (elaborated) AST nodes using index paths.
 *
 * The ElabMap produced by elaboration enables mapping type errors (which occur
 * on kernel terms) back to surface terms, which can then be mapped to source
 * positions via the SourceMap from the parser.
 */

import { TTerm } from './tt-core';
import { TTKTerm } from './tt-kernel';
import {
  ElabMap,
  IndexPath,
  appendPath,
  fieldSeg,
  arraySeg,
  serializeIndexPath
} from './source-position';
import { elabToKernel } from './tt-elab';

/**
 * Elaborate a TTerm to TTKTerm while tracking path correspondence.
 *
 * @param term - The surface term to elaborate
 * @param elabMap - Map to populate with kernel→surface path mappings
 * @param surfacePath - Current path in the surface AST
 * @param kernelPath - Current path in the kernel AST
 * @returns The elaborated kernel term
 */
export function elabToKernelWithMap(
  term: TTerm,
  elabMap: ElabMap,
  surfacePath: IndexPath = [],
  kernelPath: IndexPath = []
): TTKTerm {
  // Record the correspondence between kernel and surface paths
  const kernelKey = serializeIndexPath(kernelPath);
  const surfaceKey = serializeIndexPath(surfacePath);
  elabMap.set(kernelKey, surfaceKey);

  // For now, use the existing elaborator which does a structural copy
  // TODO: Recursively elaborate with path tracking for fine-grained correspondence
  // This will require threading paths through the elaborator similar to the parser
  const result = elabToKernel(term);

  // In the future, we would recursively track paths like this:
  // switch (term.tag) {
  //   case 'Binder':
  //     return {
  //       ...elaborated result...,
  //       domain: elabToKernelWithMap(
  //         term.domain,
  //         elabMap,
  //         appendPath(surfacePath, fieldSeg('domain')),
  //         appendPath(kernelPath, fieldSeg('domain'))
  //       ),
  //       body: elabToKernelWithMap(
  //         term.body,
  //         elabMap,
  //         appendPath(surfacePath, fieldSeg('body')),
  //         appendPath(kernelPath, fieldSeg('body'))
  //       )
  //     };
  //   // ... other cases
  // }

  return result;
}

/**
 * Look up a surface path given a kernel path.
 *
 * If the exact kernel path is not found, tries parent paths.
 * This handles cases where errors occur at a more specific location
 * than we've recorded.
 *
 * @param kernelPath - The kernel path to look up
 * @param elabMap - The elaboration map
 * @returns The corresponding surface path, or undefined if not found
 */
export function lookupSurfacePath(
  kernelPath: IndexPath,
  elabMap: ElabMap
): string | undefined {
  // Try exact match first
  const kernelKey = serializeIndexPath(kernelPath);
  const surfaceKey = elabMap.get(kernelKey);
  if (surfaceKey !== undefined) {
    return surfaceKey;
  }

  // Try parent paths (walking up the tree)
  for (let i = kernelPath.length - 1; i >= 0; i--) {
    const parentPath = kernelPath.slice(0, i);
    const parentKey = serializeIndexPath(parentPath);
    const parentSurfaceKey = elabMap.get(parentKey);
    if (parentSurfaceKey !== undefined) {
      return parentSurfaceKey;
    }
  }

  // No match found
  return undefined;
}
