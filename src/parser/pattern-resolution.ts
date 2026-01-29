/**
 * Pattern Resolution
 *
 * Resolves ambiguous identifier patterns to either constructors or variables.
 *
 * During parsing, all identifiers in pattern position are parsed as PCtor.
 * This module determines which should actually be PVar (variable bindings)
 * based on the symbol context (known constructors).
 */

import { TPattern, TTerm } from '../compiler/surface';
import { ParsedDeclaration } from './parser';
import { SymbolContext } from '../types/name-resolution';

/**
 * Resolve patterns in a declaration based on known constructors.
 *
 * Rules:
 * - If an identifier pattern is a known constructor, keep it as PCtor
 * - Otherwise, convert it to PVar (it's a variable binding)
 * - Underscore _ is always PVar (wildcard)
 *
 * @param decl - Declaration with potentially unresolved patterns
 * @param symbolContext - Set of known constructor names
 * @returns Declaration with resolved patterns
 */
export function resolvePatterns(
  decl: ParsedDeclaration,
  symbolContext: SymbolContext
): ParsedDeclaration {
  // Only term declarations can have pattern matching
  if (!decl.value) {
    return decl;
  }

  // Resolve patterns in the value (which might be a Match expression)
  const resolvedValue = resolvePatternsInTerm(decl.value, symbolContext);

  return {
    ...decl,
    value: resolvedValue
  };
}

/**
 * Resolve patterns in a term.
 */
function resolvePatternsInTerm(
  term: TTerm,
  symbolContext: SymbolContext
): TTerm {
  switch (term.tag) {
    case 'Match':
      // Resolve patterns in all clauses, including any nested WithClause in the RHS
      return {
        ...term,
        clauses: term.clauses.map(clause => ({
          ...clause,
          patterns: clause.patterns.map(pattern =>
            resolvePattern(pattern, symbolContext)
          ),
          // Also resolve patterns in clause-level namedPatterns
          namedPatterns: clause.namedPatterns?.map(np => ({
            ...np,
            pattern: resolvePattern(np.pattern, symbolContext)
          })),
          // Recurse into RHS to resolve patterns in nested WithClauses
          rhs: resolvePatternsInTerm(clause.rhs, symbolContext),
        }))
      };

    case 'WithClause':
      // Resolve patterns in function patterns, named patterns, and with-clauses
      return {
        ...term,
        functionPatterns: term.functionPatterns.map(pattern =>
          resolvePattern(pattern, symbolContext)
        ),
        functionNamedPatterns: term.functionNamedPatterns?.map(np => ({
          ...np,
          pattern: resolvePattern(np.pattern, symbolContext)
        })),
        clauses: term.clauses.map(clause => ({
          ...clause,
          patterns: clause.patterns.map(pattern =>
            resolvePattern(pattern, symbolContext)
          ),
          namedPatterns: clause.namedPatterns?.map(np => ({
            ...np,
            pattern: resolvePattern(np.pattern, symbolContext)
          })),
          // Recurse into RHS to resolve patterns in nested WithClauses
          rhs: resolvePatternsInTerm(clause.rhs, symbolContext),
        }))
      };

    // For other term types, we don't need to resolve patterns
    // (patterns only appear in Match and WithClause expressions)
    default:
      return term;
  }
}

/**
 * Resolve a single pattern.
 */
function resolvePattern(
  pattern: TPattern,
  symbolContext: SymbolContext
): TPattern {
  switch (pattern.tag) {
    case 'PVar':
      // Already resolved
      return pattern;

    case 'PWild':
      // Wildcards are already resolved
      return pattern;

    case 'PCtor': {
      // Check if this is actually a known constructor
      const isConstructor = symbolContext.has(pattern.name);
      const hasArgs = pattern.args.length > 0 || (pattern.namedArgs && pattern.namedArgs.length > 0);

      if (isConstructor) {
        // It's a known constructor - keep it as PCtor
        // Recursively resolve arguments (both positional and named)
        return {
          ...pattern,
          args: pattern.args.map(arg => resolvePattern(arg, symbolContext)),
          namedArgs: pattern.namedArgs?.map(na => ({
            ...na,
            pattern: resolvePattern(na.pattern, symbolContext)
          }))
        };
      } else {
        // Not a known constructor - this is a variable binding
        // Convert to PVar (only if it has no args and no namedArgs)
        if (!hasArgs) {
          return { tag: 'PVar', name: pattern.name };
        } else {
          // Constructor with args but not in context - this is an error
          // that will be caught during type checking. Keep as PCtor for now.
          return {
            ...pattern,
            args: pattern.args.map(arg => resolvePattern(arg, symbolContext)),
            namedArgs: pattern.namedArgs?.map(na => ({
              ...na,
              pattern: resolvePattern(na.pattern, symbolContext)
            }))
          };
        }
      }
    }
  }
}

/**
 * Resolve patterns in multiple declarations.
 *
 * This processes declarations in order, updating the symbol context
 * as new constructors are encountered.
 */
export function resolvePatternsInDeclarations(
  decls: ParsedDeclaration[],
  initialContext: SymbolContext
): ParsedDeclaration[] {
  let context = initialContext;
  const resolved: ParsedDeclaration[] = [];

  for (const decl of decls) {
    // Resolve patterns with current context
    const resolvedDecl = resolvePatterns(decl, context);
    resolved.push(resolvedDecl);

    // Update context with any new constructors from this declaration
    if (decl.constructors) {
      for (const ctor of decl.constructors) {
        context = new Set([...context, ctor.name]);
      }
    }
  }

  return resolved;
}
