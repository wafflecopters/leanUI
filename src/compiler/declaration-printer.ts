/**
 * Pretty-print ParsedDeclarations back to source text.
 *
 * This is the inverse of parsing: given a ParsedDeclaration (surface-level TT tree),
 * reconstruct the source text that would parse back to the same declaration.
 *
 * Used by the WYSIWYG editor for bidirectional sync: TT tree ↔ source text.
 */

import { ParsedDeclaration } from '../parser/parser';
import { resolvePatternsInDeclarations } from '../parser/pattern-resolution';
import { TTerm, TPattern, TClause } from './surface';
import { prettyPrintTT, prettyPrintPatternTT } from './surface';
import { parseTTSource } from './compile';

/**
 * Strip outer parentheses from a string, e.g. "(Nat -> Nat)" → "Nat -> Nat"
 */
function stripOuterParens(s: string): string {
  if (s.startsWith('(') && s.endsWith(')')) {
    // Check that the parens are balanced (not e.g. "(a) -> (b)")
    let depth = 0;
    for (let i = 0; i < s.length; i++) {
      if (s[i] === '(') depth++;
      if (s[i] === ')') depth--;
      if (depth === 0 && i < s.length - 1) return s; // Closed before end
    }
    return s.slice(1, -1);
  }
  return s;
}

/**
 * Collect all variable names bound by a list of patterns, in left-to-right depth-first order.
 * This is the binding order used by the parser/elaborator.
 */
export function collectPatternVars(patterns: TPattern[]): string[] {
  const vars: string[] = [];
  function walk(pat: TPattern): void {
    switch (pat.tag) {
      case 'PVar':
        vars.push(pat.name);
        break;
      case 'PWild':
        vars.push('_');
        break;
      case 'PCtor':
        // Named args first (if any), then positional args
        if (pat.namedArgs) {
          for (const na of pat.namedArgs) {
            walk(na.pattern);
          }
        }
        for (const arg of pat.args) {
          walk(arg);
        }
        break;
    }
  }
  for (const p of patterns) {
    walk(p);
  }
  return vars;
}

/**
 * Print a single clause of a pattern-matching definition.
 * Returns "name pat1 pat2 = rhs"
 */
function printClause(name: string, clause: TClause, outerContext: string[]): string {
  const patternStrs = clause.patterns.map(p => prettyPrintPatternTT(p));
  const patternVars = collectPatternVars(clause.patterns);

  // Build de Bruijn context for the RHS: most recently bound variable = index 0
  // prettyPrintTT uses context[index], with prepend convention [newest, ..., oldest]
  const rhsContext = [...patternVars].reverse().concat(outerContext);

  const rhsStr = stripOuterParens(prettyPrintTT(clause.rhs, rhsContext));

  const patsStr = patternStrs.length > 0 ? ' ' + patternStrs.join(' ') : '';
  return `${name}${patsStr} = ${rhsStr}`;
}

/**
 * Pretty-print a single ParsedDeclaration back to source text.
 */
export function prettyPrintDeclaration(decl: ParsedDeclaration): string {
  switch (decl.kind) {
    case 'inductive':
      return printInductive(decl);
    case 'record':
      return printRecord(decl);
    case 'def':
      return printDef(decl);
    case 'expr':
      return printExpr(decl);
  }
}

function printInductive(decl: ParsedDeclaration): string {
  const name = decl.name || 'Unnamed';
  const typeStr = decl.type ? ' : ' + stripOuterParens(prettyPrintTT(decl.type)) : '';
  const lines = [`inductive ${name}${typeStr} where`];

  if (decl.constructors) {
    for (const ctor of decl.constructors) {
      // Constructor types may reference the inductive type name and its parameters
      const ctorTypeStr = stripOuterParens(prettyPrintTT(ctor.type));
      lines.push(`  ${ctor.name} : ${ctorTypeStr}`);
    }
  }

  return lines.join('\n');
}

function printRecord(decl: ParsedDeclaration): string {
  const name = decl.name || 'Unnamed';

  // Print parameters, building context incrementally since params can reference each other
  let paramsStr = '';
  let paramContext: string[] = [];  // de Bruijn context for param types
  if (decl.params && decl.params.length > 0) {
    const paramParts: string[] = [];
    for (const p of decl.params) {
      const typeStr = stripOuterParens(prettyPrintTT(p.type, paramContext));
      if (p.implicit) {
        paramParts.push(`{${p.name} : ${typeStr}}`);
      } else {
        paramParts.push(`(${p.name} : ${typeStr})`);
      }
      // Add this param to context for subsequent params (prepend = most recent first)
      paramContext = [p.name, ...paramContext];
    }
    paramsStr = ' ' + paramParts.join(' ');
  }

  // Print extends (params are in scope)
  let extendsStr = '';
  if (decl.extends && decl.extends.length > 0) {
    if (decl.extendsExprs && decl.extendsExprs.length > 0) {
      const extParts = decl.extendsExprs.map(e => stripOuterParens(prettyPrintTT(e, paramContext)));
      extendsStr = ' extends ' + extParts.join(', ');
    } else {
      extendsStr = ' extends ' + decl.extends.join(', ');
    }
  }

  const lines = [`record ${name}${paramsStr}${extendsStr} where`];

  // Custom constructor name
  if (decl.constructorName) {
    lines.push(`  constructor ${decl.constructorName}`);
  }

  if (decl.fields) {
    // Fields are in scope of all params; each field can also reference previous fields
    let fieldContext = paramContext;

    for (let i = 0; i < decl.fields.length; i++) {
      const field = decl.fields[i];
      const typeStr = stripOuterParens(prettyPrintTT(field.type, fieldContext));
      if (field.implicit) {
        lines.push(`  {${field.name} : ${typeStr}}`);
      } else {
        lines.push(`  ${field.name} : ${typeStr}`);
      }
      // Add this field to context for subsequent fields
      fieldContext = [field.name, ...fieldContext];
    }
  }

  return lines.join('\n');
}

function printDef(decl: ParsedDeclaration): string {
  const name = decl.name || '_';

  // Postulate: type-only, no value
  if (decl.isPostulate) {
    const typeStr = decl.type ? stripOuterParens(prettyPrintTT(decl.type)) : '_';
    return `postulate ${name} : ${typeStr}`;
  }

  const lines: string[] = [];

  // Type signature
  if (decl.type) {
    const typeStr = stripOuterParens(prettyPrintTT(decl.type));
    lines.push(`${name} : ${typeStr}`);
  }

  // Value
  if (decl.value) {
    if (decl.value.tag === 'Match' && decl.value.clauses.length > 0) {
      // Multi-clause pattern matching definition
      for (const clause of decl.value.clauses) {
        lines.push(printClause(name, clause, []));
      }
    } else if (decl.value.tag === 'TacticBlock') {
      // Tactic proof - re-emit as := by with tactic names
      // For now, just indicate it's a tactic block
      if (lines.length > 0) {
        // Amend the type line to add := by
        lines[lines.length - 1] += ' := by';
        lines.push('  sorry');
      }
    } else {
      // Simple definition
      const valueStr = stripOuterParens(prettyPrintTT(decl.value));
      if (lines.length > 0) {
        // Has type signature, emit "name = value" on next line
        lines.push(`${name} = ${valueStr}`);
      } else {
        // No type signature
        lines.push(`${name} = ${valueStr}`);
      }
    }
  }

  if (lines.length === 0) {
    // Bare name with no type or value (shouldn't happen, but handle gracefully)
    return name;
  }

  return lines.join('\n');
}

function printExpr(decl: ParsedDeclaration): string {
  if (decl.value) {
    return stripOuterParens(prettyPrintTT(decl.value));
  }
  if (decl.type) {
    return stripOuterParens(prettyPrintTT(decl.type));
  }
  return '_';
}

/**
 * Pretty-print an array of declarations, joining with blank lines.
 */
export function prettyPrintAllDeclarations(decls: ParsedDeclaration[]): string {
  return decls.map(d => prettyPrintDeclaration(d)).join('\n\n') + '\n';
}

/**
 * Parse source text and return pattern-resolved declarations.
 * This is the entry point for the WYSIWYG editor: source → resolved ParsedDeclaration[].
 *
 * Pattern resolution converts ambiguous PCtor nodes to PVar where the name
 * is not a known constructor. This is necessary for correct pretty-printing.
 */
export function parseAndResolveDeclarations(source: string): ParsedDeclaration[] {
  const parseResult = parseTTSource(source);

  // Extract all declarations from parsed blocks
  const decls: ParsedDeclaration[] = [];
  for (const block of parseResult.blocks) {
    if (block.kind === 'declarations') {
      decls.push(...block.declarations);
    }
  }

  // Build symbol context from constructor names
  const constructorNames = new Set<string>();
  for (const decl of decls) {
    if (decl.constructors) {
      for (const ctor of decl.constructors) {
        constructorNames.add(ctor.name);
      }
    }
  }

  // Resolve patterns (PCtor → PVar for non-constructor names)
  return resolvePatternsInDeclarations(decls, constructorNames);
}
