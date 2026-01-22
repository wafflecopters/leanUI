/**
 * Pattern Elaboration
 *
 * This module provides `elaboratePatternsToPositionalArguments`, a single function
 * that transforms surface-level clause patterns into fully positional kernel patterns.
 *
 * Key responsibilities:
 * 1. Place named and positional patterns into parameter slots
 * 2. Fill unfilled implicit slots with wildcards
 * 3. Resolve leaf patterns: constructor vs variable
 * 4. Compute variable mapping for RHS adjustment
 */

import type { TPattern } from './surface';
import type { TTKPattern } from './kernel';

// ============================================================================
// Types
// ============================================================================

/**
 * Parameter implicitness - whether a parameter is explicit or implicit.
 */
export type Implicitness = 'explicit' | 'implicit';

/**
 * Information about a function parameter.
 */
export interface ParamInfo {
  name: string;
  implicitness: Implicitness;
}

/**
 * Result of pattern elaboration.
 */
export interface PatternElabResult {
  /**
   * Fully positional kernel patterns (one per parameter).
   */
  patterns: TTKPattern[];

  /**
   * Maps parser de Bruijn index → elaborated de Bruijn index.
   * For "phantom bindings" (parser var that's actually a ctor), value is { ctor: string }.
   * For regular vars, value is the new index.
   */
  varMapping: Map<number, number | { ctor: string }>;

  /**
   * Names of bound variables in elaborated order (for RHS context).
   * Includes wildcards as '_'.
   */
  boundNames: string[];
}

/**
 * Error result from pattern elaboration.
 */
export interface PatternElabError {
  error: string;
}

// ============================================================================
// Main Function
// ============================================================================

// Counter for generating unique wildcard names
let wildcardCounter = 0;

/**
 * Reset the wildcard counter (useful for testing).
 */
export function resetWildcardCounter(): void {
  wildcardCounter = 0;
}

/**
 * Generate a fresh wildcard name.
 */
function freshWildcardName(): string {
  return `_w${wildcardCounter++}`;
}

/**
 * Elaborate surface patterns into fully positional kernel patterns.
 *
 * This function:
 * 1. Creates slots for each parameter
 * 2. Places named patterns ({name := pattern}) into their slots
 * 3. Places positional patterns into explicit slots left-to-right
 * 4. Fills unfilled implicit slots with wildcards
 * 5. Validates no explicit slots are missing
 * 6. Converts surface patterns to kernel patterns (resolving ctor vs var)
 * 7. Computes variable mapping for RHS adjustment
 *
 * @param surfacePatterns - Positional patterns from the clause
 * @param namedPatterns - Named patterns from {name := pattern} syntax
 * @param params - Parameter info from the function type
 * @param constructorNames - Set of known constructor names
 * @returns Elaborated patterns and variable mapping, or an error
 */
export function elaboratePatternsToPositionalArguments(
  surfacePatterns: TPattern[],
  namedPatterns: Array<{ name: string; pattern: TPattern }> | undefined,
  params: ParamInfo[],
  constructorNames: Set<string>
): PatternElabResult | PatternElabError {
  // Step 1: Create slots
  const slots: (TPattern | null)[] = new Array(params.length).fill(null);

  // Step 2: Place named patterns
  for (const { name, pattern } of namedPatterns ?? []) {
    const idx = params.findIndex(p => p.name === name);
    if (idx === -1) {
      return { error: `Unknown parameter name: ${name}` };
    }
    if (slots[idx] !== null) {
      return { error: `Parameter '${name}' specified multiple times` };
    }
    slots[idx] = pattern;
  }

  // Step 3: Place positional patterns into explicit slots
  let patternIdx = 0;
  for (let i = 0; i < params.length && patternIdx < surfacePatterns.length; i++) {
    if (params[i].implicitness === 'explicit' && slots[i] === null) {
      slots[i] = surfacePatterns[patternIdx++];
    }
  }
  if (patternIdx < surfacePatterns.length) {
    const remaining = surfacePatterns.length - patternIdx;
    return { error: `Too many positional patterns: ${remaining} extra pattern(s)` };
  }

  // Step 4: Fill unfilled implicit slots with wildcards
  for (let i = 0; i < params.length; i++) {
    if (slots[i] === null && params[i].implicitness === 'implicit') {
      slots[i] = { tag: 'PWild' };
    }
  }

  // Step 5: Check for missing explicit patterns
  for (let i = 0; i < params.length; i++) {
    if (slots[i] === null && params[i].implicitness === 'explicit') {
      return { error: `Missing pattern for explicit parameter '${params[i].name}'` };
    }
  }

  // Step 6: Elaborate each pattern and collect bound variables
  const elaboratedPatterns: TTKPattern[] = [];
  const boundNames: string[] = [];

  for (let i = 0; i < slots.length; i++) {
    const slot = slots[i]!; // All slots should be filled by now
    const result = elaboratePatternWithVars(slot, constructorNames, boundNames);
    if ('error' in result) {
      return result;
    }
    elaboratedPatterns.push(result.pattern);
  }

  // Step 7: Compute variable mapping
  // First, simulate what the parser's collectPatternVars would produce
  const parserVars = collectParserVars(surfacePatterns, namedPatterns);

  // Then build the mapping
  const varMapping = buildVarMapping(parserVars, boundNames, constructorNames);

  return {
    patterns: elaboratedPatterns,
    varMapping,
    boundNames
  };
}

// ============================================================================
// Pattern Elaboration Helpers
// ============================================================================

/**
 * Elaborate a single pattern to kernel form, collecting bound variable names.
 *
 * @param pattern - Surface pattern to elaborate
 * @param constructorNames - Set of known constructor names
 * @param boundNames - Accumulator for bound variable names (mutated)
 * @returns Kernel pattern or error
 */
function elaboratePatternWithVars(
  pattern: TPattern,
  constructorNames: Set<string>,
  boundNames: string[]
): { pattern: TTKPattern } | PatternElabError {
  switch (pattern.tag) {
    case 'PVar':
      boundNames.push(pattern.name);
      return { pattern: { tag: 'PVar', name: pattern.name } };

    case 'PWild':
      boundNames.push('_');
      return { pattern: { tag: 'PWild', name: freshWildcardName() } };

    case 'PCtor': {
      const hasArgs = pattern.args.length > 0 || (pattern.namedArgs && pattern.namedArgs.length > 0);

      if (!hasArgs) {
        // Leaf PCtor - check if it's a known constructor
        if (constructorNames.has(pattern.name)) {
          // It's a constructor with no args - keep as PCtor
          return { pattern: { tag: 'PCtor', name: pattern.name, args: [] } };
        } else {
          // Not a constructor - treat as pattern variable
          boundNames.push(pattern.name);
          return { pattern: { tag: 'PVar', name: pattern.name } };
        }
      }

      // PCtor with args - must be a constructor
      if (!constructorNames.has(pattern.name)) {
        return { error: `'${pattern.name}' is not a known constructor but has arguments` };
      }

      // Recursively elaborate positional arguments
      const elabArgs: TTKPattern[] = [];
      for (const arg of pattern.args) {
        const result = elaboratePatternWithVars(arg, constructorNames, boundNames);
        if ('error' in result) {
          return result;
        }
        elabArgs.push(result.pattern);
      }

      // Handle named arguments within constructor patterns
      // These need to be placed into the constructor's parameter slots
      if (pattern.namedArgs && pattern.namedArgs.length > 0) {
        // For now, we handle named args by appending them after positional args
        // TODO: Proper slot-based placement for constructor named args
        for (const namedArg of pattern.namedArgs) {
          const result = elaboratePatternWithVars(namedArg.pattern, constructorNames, boundNames);
          if ('error' in result) {
            return result;
          }
          elabArgs.push(result.pattern);
        }
      }

      return { pattern: { tag: 'PCtor', name: pattern.name, args: elabArgs } };
    }
  }
}

// ============================================================================
// Parser Variable Collection (Simulation)
// ============================================================================

/**
 * Simulate the parser's collectPatternVars to get the variable names
 * in the order the parser would produce them.
 *
 * The parser treats ALL leaf PCtors (no args) as potential variables.
 * The elaborator then determines which are actual constructors vs variables.
 *
 * - PVar: always a variable
 * - PWild: binds '_'
 * - PCtor with no args: potential variable (added to pattern vars)
 * - PCtor with args: recursively collect from args
 */
function collectParserVarsFromPattern(pattern: TPattern): string[] {
  switch (pattern.tag) {
    case 'PVar':
      return [pattern.name];

    case 'PWild':
      return ['_'];

    case 'PCtor': {
      const hasArgs = pattern.args.length > 0 || (pattern.namedArgs && pattern.namedArgs.length > 0);

      if (!hasArgs) {
        // All leaf PCtors are treated as potential variables by the parser
        return [pattern.name];
      }

      // Has args - recursively collect
      const positionalVars = pattern.args.flatMap(collectParserVarsFromPattern);
      const namedVars = pattern.namedArgs
        ? pattern.namedArgs.flatMap(na => collectParserVarsFromPattern(na.pattern))
        : [];
      return [...positionalVars, ...namedVars];
    }
  }
}

/**
 * Collect parser variables from all patterns in a clause.
 *
 * @param surfacePatterns - Positional patterns
 * @param namedPatterns - Named patterns
 * @returns Variable names in parser order
 */
function collectParserVars(
  surfacePatterns: TPattern[],
  namedPatterns: Array<{ name: string; pattern: TPattern }> | undefined
): string[] {
  const positionalVars = surfacePatterns.flatMap(collectParserVarsFromPattern);
  const namedVars = (namedPatterns ?? []).flatMap(np => collectParserVarsFromPattern(np.pattern));
  return [...positionalVars, ...namedVars];
}

// ============================================================================
// Variable Mapping
// ============================================================================

/**
 * Build a mapping from parser variable indices to elaborated variable indices.
 *
 * The parser assigns de Bruijn indices based on its heuristic.
 * The elaborator may produce different indices because:
 * 1. Implicit wildcards are inserted
 * 2. Some "variables" turn out to be constructors
 * 3. Patterns are reordered
 *
 * This mapping allows us to adjust the RHS.
 *
 * Note: De Bruijn indices in the RHS are "reversed" - Var(0) refers to the
 * LAST bound variable. The mapping here works with "binding order" indices,
 * and the RHS adjustment will handle the reversal.
 *
 * @param parserVars - Variable names from parser's perspective
 * @param boundNames - Variable names from elaborator's perspective
 * @param constructorNames - Set of known constructor names
 * @returns Mapping from parser index to elaborated index or constructor info
 */
function buildVarMapping(
  parserVars: string[],
  boundNames: string[],
  constructorNames: Set<string>
): Map<number, number | { ctor: string }> {
  const mapping = new Map<number, number | { ctor: string }>();

  // Build a map of name → indices in boundNames (handling duplicates)
  const nameToIndices = new Map<string, number[]>();
  for (let i = 0; i < boundNames.length; i++) {
    const name = boundNames[i];
    if (!nameToIndices.has(name)) {
      nameToIndices.set(name, []);
    }
    nameToIndices.get(name)!.push(i);
  }

  // Track which indices we've used for each name (for handling duplicates)
  const usedIndices = new Map<string, number>();

  for (let parserIdx = 0; parserIdx < parserVars.length; parserIdx++) {
    const name = parserVars[parserIdx];

    // Check if this name is a constructor (phantom binding)
    if (constructorNames.has(name)) {
      mapping.set(parserIdx, { ctor: name });
      continue;
    }

    // Find the corresponding index in boundNames
    const indices = nameToIndices.get(name);
    if (indices && indices.length > 0) {
      const usedCount = usedIndices.get(name) ?? 0;
      if (usedCount < indices.length) {
        mapping.set(parserIdx, indices[usedCount]);
        usedIndices.set(name, usedCount + 1);
      }
    }
    // If name not found, it means the elaborator didn't bind it
    // (shouldn't happen in well-formed patterns, but we handle it gracefully)
  }

  return mapping;
}

// ============================================================================
// RHS Adjustment
// ============================================================================

/**
 * Adjust RHS term based on variable mapping.
 *
 * This transforms de Bruijn indices in the RHS to account for:
 * 1. Inserted implicit wildcards
 * 2. Pattern reordering
 * 3. Phantom bindings (parser vars that are actually constructors)
 *
 * @param rhs - The RHS term to adjust (surface syntax)
 * @param varMapping - Mapping from parser to elaborated indices
 * @param totalParserVars - Total number of variables the parser counted
 * @param totalElabVars - Total number of variables after elaboration
 * @returns Adjusted RHS term
 */
export function adjustRhsWithMapping(
  rhs: import('./surface').TTerm,
  varMapping: Map<number, number | { ctor: string }>,
  totalParserVars: number,
  totalElabVars: number
): import('./surface').TTerm {
  type TTerm = import('./surface').TTerm;

  function adjust(term: TTerm, depth: number): TTerm {
    switch (term.tag) {
      case 'Var': {
        // Check if this Var references a pattern variable
        const rhsIndex = term.index - depth;

        // RHS de Bruijn index (0 = last bound var)
        // Parser binding index (0 = first bound var)
        // Conversion: parserIdx = totalParserVars - 1 - rhsIndex
        if (rhsIndex < 0 || rhsIndex >= totalParserVars) {
          // Not a pattern variable (references something outside the patterns)
          return term;
        }

        const parserIdx = totalParserVars - 1 - rhsIndex;
        const mapped = varMapping.get(parserIdx);

        if (mapped === undefined) {
          // No mapping - leave unchanged (shouldn't happen in valid code)
          return term;
        }

        if (typeof mapped === 'object' && 'ctor' in mapped) {
          // Phantom binding - replace with Const
          return { tag: 'Const', name: mapped.ctor };
        }

        // Regular variable - compute new de Bruijn index
        // mapped is the binding index in elaborated order
        // New RHS index: totalElabVars - 1 - mapped
        const newRhsIndex = totalElabVars - 1 - mapped;
        return { tag: 'Var', index: newRhsIndex + depth };
      }

      case 'Const':
      case 'Sort':
      case 'ULevel':
      case 'Hole':
      case 'AbsurdMarker':
        return term;

      case 'Binder':
        return {
          ...term,
          domain: term.domain ? adjust(term.domain, depth) : undefined,
          body: adjust(term.body, depth + 1)
        };

      case 'MultiBinder':
        return {
          ...term,
          domain: adjust(term.domain, depth),
          body: adjust(term.body, depth + term.names.length)
        };

      case 'App':
        return {
          ...term,
          fn: adjust(term.fn, depth),
          arg: adjust(term.arg, depth)
        };

      case 'Annot':
        return {
          ...term,
          term: adjust(term.term, depth),
          type: adjust(term.type, depth)
        };

      case 'Match':
        return {
          ...term,
          scrutinee: adjust(term.scrutinee, depth),
          clauses: term.clauses.map(c => ({
            ...c,
            // For nested match, need to count pattern vars
            rhs: adjust(c.rhs, depth + countPatternVars(c.patterns))
          }))
        };
    }
  }

  return adjust(rhs, 0);
}

/**
 * Count pattern variables (for nested match depth calculation).
 */
function countPatternVars(patterns: TPattern[]): number {
  function countInPattern(p: TPattern): number {
    switch (p.tag) {
      case 'PVar':
        return 1;
      case 'PWild':
        return 1;
      case 'PCtor':
        return p.args.reduce((sum, arg) => sum + countInPattern(arg), 0) +
               (p.namedArgs?.reduce((sum, na) => sum + countInPattern(na.pattern), 0) ?? 0);
    }
  }
  return patterns.reduce((sum, p) => sum + countInPattern(p), 0);
}
