/**
 * Smart Variable Name Proposal
 *
 * Single function for proposing meaningful variable names based on domain type.
 * Used for intro suggestions AND case split parameter names.
 */

import { TTerm } from '../compiler/surface';
import { ReverseRegistry } from '../math-editor/tt-to-math';
import { PatternElement } from '../math-editor/syntax-registry';
import { extractTypeHead } from './goal-computation';

// ============================================================================
// Operator symbol → name fragment mapping
// ============================================================================

const OPERATOR_NAME_MAP = new Map<string, string>([
  ['\\vee', 'Or'],    ['\\lor', 'Or'],
  ['\\wedge', 'And'],  ['\\land', 'And'],
  ['=', 'Eq'],
  ['\\to', 'To'],
  ['\\leq', 'Le'],    ['\\geq', 'Ge'],
  ['<', 'Lt'],         ['>', 'Gt'],
  ['+', 'Plus'],       ['-', 'Minus'],
  ['\\cdot', 'Mul'],   ['\\times', 'Times'],
  ['\\in', 'In'],
  ['\\neq', 'Ne'],
]);

// ============================================================================
// Helpers
// ============================================================================

/** Collect the app spine of a surface term: App(App(f, a), b) → { head: f, args: [a, b] } */
function collectSurfaceAppSpine(term: TTerm): { head: TTerm; args: TTerm[] } {
  const args: TTerm[] = [];
  let current = term;
  while (current.tag === 'App') {
    args.unshift(current.arg);
    current = current.fn;
  }
  return { head: current, args };
}

/** Extract the primary operator symbol from a SyntaxEntry's pattern (first literal element). */
function extractPrimaryOperator(pattern: PatternElement[]): string | null {
  for (const pe of pattern) {
    if (pe.tag === 'literal') return pe.symbol;
  }
  return null;
}

/**
 * Get a 1-char abbreviation for a type argument.
 * - Const("Nat") → 'n'
 * - Var(i) with ctx → lowercase first char of ctx[ctx.length - 1 - i]
 * - Fallback → positional letter ('a', 'b', 'c', ...)
 */
function argAbbreviation(arg: TTerm, position: number, ctx?: readonly string[]): string {
  if (arg.tag === 'Const') {
    return arg.name.charAt(0).toLowerCase();
  }
  if (arg.tag === 'Var' && ctx) {
    const name = ctx[arg.index];
    if (name && name !== '_') {
      return name.charAt(0).toLowerCase();
    }
  }
  // Positional fallback
  return String.fromCharCode(97 + (position % 26)); // a, b, c, ...
}

/**
 * Freshen a base name against a set of used names.
 * Function names cycle f → g → h before numeric suffixes.
 */
export function freshenName(baseName: string, usedNames: ReadonlySet<string>): string {
  if (!usedNames.has(baseName)) return baseName;

  // Function names cycle through common alternatives
  if (baseName === 'f') {
    for (const alt of ['g', 'h']) {
      if (!usedNames.has(alt)) return alt;
    }
  }

  // Numeric suffix fallback
  let i = 1;
  while (usedNames.has(`${baseName}${i}`)) i++;
  return `${baseName}${i}`;
}

// ============================================================================
// Core proposal logic
// ============================================================================

/**
 * Propose a base name (before freshening) from a domain type.
 */
function proposeBaseName(
  domain: TTerm,
  rev?: ReverseRegistry,
  ctx?: readonly string[],
): string {
  // 1. Function types → 'f'
  if (domain.tag === 'Binder' && domain.binderKind.tag === 'BPiTT') {
    return 'f';
  }

  // 2. Applied constructor — check for syntax notation
  const headName = extractTypeHead(domain);
  if (headName && rev) {
    const entry = rev.nameToEntry.get(headName);
    if (entry) {
      const operator = extractPrimaryOperator(entry.pattern);
      if (operator) {
        const fragment = OPERATOR_NAME_MAP.get(operator);
        if (fragment) {
          // Build compound name from args: aOrB, xEqY, etc.
          const { args } = collectSurfaceAppSpine(domain);
          if (args.length >= 2) {
            const first = argAbbreviation(args[args.length - 2], 0, ctx);
            const second = argAbbreviation(args[args.length - 1], 1, ctx);
            return `${first}${fragment}${second}`;
          }
        }
      }
    }
  }

  // 3. Simple type constructor → lowercase first letter
  if (headName) {
    return headName.charAt(0).toLowerCase();
  }

  // 4. Var reference — resolve via context to get type name
  if (domain.tag === 'Var' && ctx && domain.index < ctx.length) {
    const resolved = ctx[domain.index];
    if (resolved && resolved !== '_') {
      return resolved.charAt(0).toLowerCase();
    }
  }

  // 5. Fallback
  return 'x';
}

// ============================================================================
// Public API
// ============================================================================

/**
 * Propose a meaningful variable name based on the domain type.
 *
 * This is the ONE function for all variable name recommendations:
 * intro suggestions, case split params, etc.
 *
 * @param domain - The type of the variable being named (surface TTerm)
 * @param usedNames - Names already in scope (returned name guaranteed free)
 * @param rev - Optional syntax registry for operator-based naming
 * @param ctx - Optional name context for resolving Var args (de Bruijn order)
 * @returns A fresh, meaningful variable name
 */
export function proposeVarName(
  domain: TTerm,
  usedNames: ReadonlySet<string>,
  rev?: ReverseRegistry,
  ctx?: readonly string[],
): string {
  const base = proposeBaseName(domain, rev, ctx);
  return freshenName(base, usedNames);
}
