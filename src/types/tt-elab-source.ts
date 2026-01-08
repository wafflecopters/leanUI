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

import { TTerm, TPattern } from './tt-core';
import { TTKTerm, TTKPattern } from './tt-kernel';
import {
  ElabMap,
  IndexPath,
  appendPath,
  fieldSeg,
  arraySeg,
  serializeIndexPath
} from './source-position';
// Note: We no longer use elabToKernel here - we do full recursive elaboration with path tracking

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

  // Recursively elaborate with path tracking
  switch (term.tag) {
    case 'Var':
      return { tag: 'Var', index: term.index };

    case 'Sort':
      return { tag: 'Sort', level: term.level };

    case 'Const':
      return {
        tag: 'Const',
        name: term.name,
        type: elabToKernelWithMap(
          term.type,
          elabMap,
          appendPath(surfacePath, fieldSeg('type')),
          appendPath(kernelPath, fieldSeg('type'))
        )
      };

    case 'Binder': {
      const domain = elabToKernelWithMap(
        term.domain,
        elabMap,
        appendPath(surfacePath, fieldSeg('domain')),
        appendPath(kernelPath, fieldSeg('domain'))
      );
      const body = elabToKernelWithMap(
        term.body,
        elabMap,
        appendPath(surfacePath, fieldSeg('body')),
        appendPath(kernelPath, fieldSeg('body'))
      );

      let binderKind: import('./tt-kernel').TTKBinderKind;
      switch (term.binderKind.tag) {
        case 'BPi':
          binderKind = { tag: 'BPi' };
          break;
        case 'BLam':
          binderKind = { tag: 'BLam' };
          break;
        case 'BLet':
          binderKind = {
            tag: 'BLet',
            defVal: elabToKernelWithMap(
              term.binderKind.defVal,
              elabMap,
              appendPath(surfacePath, fieldSeg('binderKind'), fieldSeg('defVal')),
              appendPath(kernelPath, fieldSeg('binderKind'), fieldSeg('defVal'))
            )
          };
          break;
      }

      return {
        tag: 'Binder',
        name: term.name,
        binderKind,
        domain,
        body
      };
    }

    case 'App':
      return {
        tag: 'App',
        fn: elabToKernelWithMap(
          term.fn,
          elabMap,
          appendPath(surfacePath, fieldSeg('fn')),
          appendPath(kernelPath, fieldSeg('fn'))
        ),
        arg: elabToKernelWithMap(
          term.arg,
          elabMap,
          appendPath(surfacePath, fieldSeg('arg')),
          appendPath(kernelPath, fieldSeg('arg'))
        )
      };

    case 'Hole':
      return {
        tag: 'Hole',
        id: term.id,
        type: elabToKernelWithMap(
          term.type,
          elabMap,
          appendPath(surfacePath, fieldSeg('type')),
          appendPath(kernelPath, fieldSeg('type'))
        ),
        context: term.context.map((binding, i) => ({
          name: binding.name,
          type: elabToKernelWithMap(
            binding.type,
            elabMap,
            appendPath(surfacePath, fieldSeg('context'), arraySeg(i), fieldSeg('type')),
            appendPath(kernelPath, fieldSeg('context'), arraySeg(i), fieldSeg('type'))
          )
        }))
      };

    case 'Annot':
      return {
        tag: 'Annot',
        term: elabToKernelWithMap(
          term.term,
          elabMap,
          appendPath(surfacePath, fieldSeg('term')),
          appendPath(kernelPath, fieldSeg('term'))
        ),
        type: elabToKernelWithMap(
          term.type,
          elabMap,
          appendPath(surfacePath, fieldSeg('type')),
          appendPath(kernelPath, fieldSeg('type'))
        )
      };

    case 'Match':
      return {
        tag: 'Match',
        scrutinee: elabToKernelWithMap(
          term.scrutinee,
          elabMap,
          appendPath(surfacePath, fieldSeg('scrutinee')),
          appendPath(kernelPath, fieldSeg('scrutinee'))
        ),
        clauses: term.clauses.map((clause, i) => {
          const clauseSurfacePath = appendPath(surfacePath, fieldSeg('clauses'), arraySeg(i));
          const clauseKernelPath = appendPath(kernelPath, fieldSeg('clauses'), arraySeg(i));

          // Record the clause mapping
          elabMap.set(serializeIndexPath(clauseKernelPath), serializeIndexPath(clauseSurfacePath));

          return {
            patterns: clause.patterns.map(elabPatternToKernel),
            rhs: elabToKernelWithMap(
              clause.rhs,
              elabMap,
              appendPath(clauseSurfacePath, fieldSeg('rhs')),
              appendPath(clauseKernelPath, fieldSeg('rhs'))
            )
          };
        })
      };
  }
}

/**
 * Elaborate a surface pattern (TPattern) to a kernel pattern (TTKPattern).
 * Wildcards are already PVar with unique names (_wN) from the parser.
 */
function elabPatternToKernel(pattern: TPattern): TTKPattern {
  switch (pattern.tag) {
    case 'PVar':
      // Includes wildcards (_wN) which are already PVar
      return { tag: 'PVar', name: pattern.name };
    case 'PCtor':
      return {
        tag: 'PCtor',
        name: pattern.name,
        args: pattern.args.map(elabPatternToKernel)
      };
  }
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
