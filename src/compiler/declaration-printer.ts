/**
 * Pretty-print declarations back to source text.
 *
 * Two modes:
 * 1. prettyPrintDeclaration(ParsedDeclaration) — from surface syntax (for editing roundtrip)
 * 2. prettyPrintCompiledDeclaration(CompiledDeclaration) — from kernel output (for display)
 *
 * The compiled path uses zonked kernel terms, so all metas are resolved and
 * lambda binder types are fully elaborated (no ?ih_type holes).
 */

import { ParsedDeclaration } from '../parser/parser';
import { resolvePatternsInDeclarations } from '../parser/pattern-resolution';
import { TTerm, TPattern, TClause } from './surface';
import { prettyPrintTT, prettyPrintPatternTT } from './surface';
import { parseTTSource, CompiledDeclaration } from './compile';
import { prettyPrintFormatted, prettyPrintPattern, prettyPrintPatternList } from './kernel';
import { TTKTerm, TTKPattern, TTKClause } from './kernel';

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

/** Collect variable names from kernel patterns */
function collectKernelPatternVars(patterns: TTKPattern[]): string[] {
  const vars: string[] = [];
  function walk(pat: TTKPattern): void {
    switch (pat.tag) {
      case 'PVar': vars.push(pat.name); break;
      case 'PWild': vars.push(pat.name || '_'); break;
      case 'PCtor':
        for (const arg of pat.args) walk(arg);
        break;
    }
  }
  for (const p of patterns) walk(p);
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

/** Print a kernel clause as "name pat1 pat2 = rhs" */
function printKernelClause(name: string, clause: TTKClause): string {
  const patternStrs = clause.patterns.map(p => prettyPrintPattern(p));

  // Build context for RHS from pattern vars (or stored contextNames)
  const context = clause.contextNames
    ? [...clause.contextNames]
    : [...collectKernelPatternVars(clause.patterns).reverse()];

  const rhsStr = stripOuterParens(prettyPrintFormatted(clause.rhs, context, clause.metaVars));

  const patsStr = patternStrs.length > 0 ? ' ' + patternStrs.join(' ') : '';
  return `${name}${patsStr} = ${rhsStr}`;
}

// ============================================================================
// Surface (ParsedDeclaration) Pretty-Printing
// ============================================================================

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

// ============================================================================
// Compiled (CompiledDeclaration) Pretty-Printing
// ============================================================================

/**
 * Pretty-print a CompiledDeclaration using zonked kernel terms.
 *
 * All metas are resolved, so lambda binder types show their inferred types
 * (e.g., `\(ih : PeanoNat.carrier N)`) instead of parser Holes (`?ih_type`).
 *
 * Falls back to surface terms for records (which preserve record syntax).
 */
export function prettyPrintCompiledDeclaration(decl: CompiledDeclaration): string {
  if (decl.kind === 'inductive') {
    // Records: use surface fields to preserve record syntax
    if (decl.isRecord && decl.surfaceFields) {
      return printCompiledRecord(decl);
    }
    return printCompiledInductive(decl);
  }
  return printCompiledDef(decl);
}

function printCompiledInductive(decl: CompiledDeclaration): string {
  const name = decl.name || 'Unnamed';
  const typeStr = decl.prettyType ? ' : ' + stripOuterParens(decl.prettyType) : '';
  const lines = [`inductive ${name}${typeStr} where`];

  if (decl.prettyConstructors) {
    for (const ctor of decl.prettyConstructors) {
      lines.push(`  ${ctor.name} : ${stripOuterParens(ctor.prettyType)}`);
    }
  }

  return lines.join('\n');
}

function printCompiledRecord(decl: CompiledDeclaration): string {
  const name = decl.name || 'Unnamed';

  // Use surface params for record syntax
  let paramsStr = '';
  let paramContext: string[] = [];
  if (decl.surfaceParams && decl.surfaceParams.length > 0) {
    const paramParts: string[] = [];
    for (const p of decl.surfaceParams) {
      const typeStr = stripOuterParens(prettyPrintTT(p.type, paramContext));
      paramParts.push(`(${p.name} : ${typeStr})`);
      paramContext = [p.name, ...paramContext];
    }
    paramsStr = ' ' + paramParts.join(' ');
  }

  // Use surface extends expressions
  let extendsStr = '';
  if (decl.surfaceExtendsExprs && decl.surfaceExtendsExprs.length > 0) {
    const extParts = decl.surfaceExtendsExprs.map(e => stripOuterParens(prettyPrintTT(e, paramContext)));
    extendsStr = ' extends ' + extParts.join(', ');
  }

  const lines = [`record ${name}${paramsStr}${extendsStr} where`];

  // Use surface fields
  if (decl.surfaceFields) {
    let fieldContext = paramContext;
    for (const field of decl.surfaceFields) {
      const typeStr = stripOuterParens(prettyPrintTT(field.type, fieldContext));
      lines.push(`  ${field.name} : ${typeStr}`);
      fieldContext = [field.name, ...fieldContext];
    }
  }

  return lines.join('\n');
}

function printCompiledDef(decl: CompiledDeclaration): string {
  const name = decl.name || '_';
  const lines: string[] = [];

  // Type signature (from kernel, fully resolved)
  if (decl.prettyType) {
    lines.push(`${name} : ${stripOuterParens(decl.prettyType)}`);
  }

  // Value (from kernel)
  const kv = decl.kernelValue;
  if (kv) {
    if (kv.tag === 'Match' && kv.scrutinee.tag === 'Hole' && kv.scrutinee.id === '_scrutinee') {
      // Pattern-matching definition: render each clause as "name pats = rhs"
      for (const clause of kv.clauses) {
        lines.push(printKernelClause(name, clause));
      }
    } else {
      // Simple definition: use prettyValue or render kernelValue
      const valueStr = decl.prettyValue
        ? stripOuterParens(decl.prettyValue)
        : stripOuterParens(prettyPrintFormatted(kv, []));
      lines.push(`${name} = ${valueStr}`);
    }
  }

  if (lines.length === 0) {
    return name;
  }

  return lines.join('\n');
}

// ============================================================================
// Utility functions
// ============================================================================

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
