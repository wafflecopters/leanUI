import type { CompileResult } from './compile-types';
import type { ElabMap, SourceMap } from '../types/source-position';
import type { TPattern, TTerm, TacticCommand } from './surface';
import type { TTKPattern, TTKTerm } from './kernel';
import { serializePathForLookup } from './compile-source-utils';

/**
 * Whether to show wildcard inlay hints (e.g., `_[n0]`) in the editor.
 */
export const SHOW_WILDCARD_INLAY_HINTS = false;

/**
 * Information for a wildcard inlay hint.
 */
export interface WildcardInlayHint {
  line: number;
  column: number;
  name: string;
}

/**
 * Semantic token types for syntax highlighting.
 */
export type SemanticTokenType =
  | 'termName'
  | 'constName'
  | 'boundVar'
  | 'patternVar'
  | 'absurd'
  | 'namedBrace'
  | 'directive'
  | 'directiveValue'
  | 'tacticName';

/**
 * A semantic token for highlighting.
 */
export interface SemanticToken {
  line: number;
  column: number;
  length: number;
  type: SemanticTokenType;
}

/**
 * Information about a hole location for warning markers.
 */
export interface HoleLocation {
  line: number;
  column: number;
  endColumn: number;
  id: string;
}

/**
 * Extract semantic tokens from a compile result for syntax highlighting.
 */
export function extractSemanticTokens(result: CompileResult, source?: string): SemanticToken[] {
  const tokens: SemanticToken[] = [];

  if (source) {
    tokens.push(...extractDirectiveTokens(source));
  }

  for (const block of result.blocks) {
    for (const decl of block.declarations) {
      if (!decl.sourceMap) continue;

      if (decl.name) {
        const tokenType = decl.kind === 'inductive' ? 'constName' : 'termName';
        addSemanticTokenDirect(['name'], decl.sourceMap, tokenType, tokens);
      }

      if (decl.surfaceType) {
        collectSemanticTokensFromSurfaceTerm(
          decl.surfaceType,
          decl.sourceMap,
          ['type'],
          tokens
        );
      }

      if (decl.surfaceValue) {
        collectSemanticTokensFromSurfaceTerm(
          decl.surfaceValue,
          decl.sourceMap,
          ['value'],
          tokens
        );

        if (decl.surfaceValue.tag === 'Match') {
          for (let i = 0; i < decl.surfaceValue.clauses.length; i++) {
            addSemanticTokenDirect(
              ['value', 'clauses', i, 'defName'],
              decl.sourceMap,
              'termName',
              tokens
            );
          }
        } else {
          addSemanticTokenDirect(
            ['value', 'clauses', 0, 'defName'],
            decl.sourceMap,
            'termName',
            tokens
          );
        }
      }

      if (decl.surfaceConstructors) {
        for (let i = 0; i < decl.surfaceConstructors.length; i++) {
          addSemanticTokenDirect(['constructors', i, 'name'], decl.sourceMap, 'constName', tokens);
          collectSemanticTokensFromSurfaceTerm(
            decl.surfaceConstructors[i].type,
            decl.sourceMap,
            ['constructors', i, 'type'],
            tokens
          );
        }
      }

      if (decl.isRecord) {
        addSemanticTokenDirect(['constructorName'], decl.sourceMap, 'constName', tokens);

        if (decl.surfaceParams) {
          for (let i = 0; i < decl.surfaceParams.length; i++) {
            addSemanticTokenDirect(['params', i, 'name'], decl.sourceMap, 'boundVar', tokens);
            collectSemanticTokensFromSurfaceTerm(
              decl.surfaceParams[i].type,
              decl.sourceMap,
              ['params', i, 'type'],
              tokens
            );
          }
        }

        if (decl.surfaceFields) {
          for (let i = 0; i < decl.surfaceFields.length; i++) {
            addSemanticTokenDirect(['fields', i, 'name'], decl.sourceMap, 'termName', tokens);
            collectSemanticTokensFromSurfaceTerm(
              decl.surfaceFields[i].type,
              decl.sourceMap,
              ['fields', i, 'type'],
              tokens
            );
          }
        }

        if (decl.surfaceExtendsExprs) {
          for (let i = 0; i < decl.surfaceExtendsExprs.length; i++) {
            collectSemanticTokensFromSurfaceTerm(
              decl.surfaceExtendsExprs[i],
              decl.sourceMap,
              ['extends', i],
              tokens
            );
          }
        }
      }
    }
  }

  const seen = new Set<string>();
  const deduped: SemanticToken[] = [];
  for (const token of tokens) {
    const key = `${token.line}:${token.column}:${token.length}`;
    if (!seen.has(key)) {
      seen.add(key);
      deduped.push(token);
    }
  }
  return deduped;
}

/**
 * Extract directive tokens from source text for syntax highlighting.
 */
export function extractDirectiveTokens(source: string): SemanticToken[] {
  const tokens: SemanticToken[] = [];
  const lines = source.split('\n');

  for (let lineIndex = 0; lineIndex < lines.length; lineIndex++) {
    const line = lines[lineIndex];
    const directiveMatch = line.match(/^(\s*)(?:--\s*)?(@\w+)(?:=(\w+)|\s+(\w+)|\s+"([^"]*)")?/);
    if (!directiveMatch) continue;

    const [, , directive, equalsValue, spaceValue, quotedValue] = directiveMatch;
    const value = equalsValue || spaceValue || quotedValue;
    const atIndex = line.indexOf('@');
    const column = atIndex >= 0 ? atIndex + 1 : 0;

    tokens.push({
      line: lineIndex + 1,
      column,
      length: directive.length,
      type: 'directive',
    });

    if (value) {
      const valueIndex = line.indexOf(value, atIndex + directive.length);
      if (valueIndex >= 0) {
        tokens.push({
          line: lineIndex + 1,
          column: valueIndex + 1,
          length: value.length,
          type: 'directiveValue',
        });
      }
    }

    if (directive === '@syntax') {
      const becomesMatch = line.match(/@becomes\b/);
      if (becomesMatch?.index !== undefined) {
        tokens.push({
          line: lineIndex + 1,
          column: becomesMatch.index + 1,
          length: '@becomes'.length,
          type: 'directive',
        });
      }
    }
  }

  return tokens;
}

function collectSemanticTokensFromSurfaceTerm(
  term: TTerm,
  sourceMap: SourceMap,
  path: (string | number)[],
  tokens: SemanticToken[]
): void {
  switch (term.tag) {
    case 'Var':
      addSemanticTokenDirect(path, sourceMap, 'boundVar', tokens);
      break;

    case 'Const':
      if (term.name.length > 0) {
        const firstChar = term.name[0];
        const isUppercase = firstChar >= 'A' && firstChar <= 'Z';
        addSemanticTokenDirect(path, sourceMap, isUppercase ? 'constName' : 'termName', tokens);
      }
      break;

    case 'Sort':
      collectSemanticTokensFromSurfaceTerm(term.level, sourceMap, [...path, 'level'], tokens);
      break;

    case 'Hole':
      collectSemanticTokensFromSurfaceTerm(term.type, sourceMap, [...path, 'type'], tokens);
      break;

    case 'Binder':
      addSemanticTokenDirect([...path, 'name'], sourceMap, 'patternVar', tokens);
      if (term.named) {
        addSemanticTokenDirect([...path, 'openBrace'], sourceMap, 'namedBrace', tokens);
        addSemanticTokenDirect([...path, 'closeBrace'], sourceMap, 'namedBrace', tokens);
      }
      if (term.domain !== undefined) {
        collectSemanticTokensFromSurfaceTerm(term.domain, sourceMap, [...path, 'domain'], tokens);
      }
      collectSemanticTokensFromSurfaceTerm(term.body, sourceMap, [...path, 'body'], tokens);
      if (term.binderKind.tag === 'BLetTT') {
        collectSemanticTokensFromSurfaceTerm(
          term.binderKind.defVal,
          sourceMap,
          [...path, 'bindings', 0, 'value'],
          tokens
        );
      }
      break;

    case 'App':
      collectSemanticTokensFromSurfaceTerm(term.fn, sourceMap, [...path, 'fn'], tokens);
      collectSemanticTokensFromSurfaceTerm(term.arg, sourceMap, [...path, 'arg'], tokens);
      if (term.argName) {
        addSemanticTokenDirect([...path, 'arg', 'name'], sourceMap, 'boundVar', tokens);
        addSemanticTokenDirect([...path, 'arg', 'openBrace'], sourceMap, 'namedBrace', tokens);
        addSemanticTokenDirect([...path, 'arg', 'closeBrace'], sourceMap, 'namedBrace', tokens);
      }
      break;

    case 'Annot':
      collectSemanticTokensFromSurfaceTerm(term.term, sourceMap, [...path, 'term'], tokens);
      collectSemanticTokensFromSurfaceTerm(term.type, sourceMap, [...path, 'type'], tokens);
      break;

    case 'Match':
      collectSemanticTokensFromSurfaceTerm(term.scrutinee, sourceMap, [...path, 'scrutinee'], tokens);
      for (let i = 0; i < term.clauses.length; i++) {
        const clause = term.clauses[i];
        const totalPatternCount = clause.patterns.length + (clause.namedPatterns?.length || 0);
        for (let j = 0; j < totalPatternCount; j++) {
          addSemanticTokenDirect([...path, 'clauses', i, 'patterns', j, 'openBrace'], sourceMap, 'namedBrace', tokens);
          addSemanticTokenDirect([...path, 'clauses', i, 'patterns', j, 'closeBrace'], sourceMap, 'namedBrace', tokens);
        }
        const namedPatternCount = clause.namedPatterns?.length || 0;
        for (let j = 0; j < clause.patterns.length; j++) {
          const sourceMapIndex = j + namedPatternCount;
          collectSemanticTokensFromSurfacePattern(
            clause.patterns[j],
            sourceMap,
            [...path, 'clauses', i, 'patterns', sourceMapIndex],
            tokens
          );
        }
        if (clause.namedPatterns) {
          for (let j = 0; j < clause.namedPatterns.length; j++) {
            addSemanticTokenDirect([...path, 'clauses', i, 'patterns', j, 'name'], sourceMap, 'boundVar', tokens);
            collectSemanticTokensFromSurfacePattern(
              clause.namedPatterns[j].pattern,
              sourceMap,
              [...path, 'clauses', i, 'patterns', j, 'pattern'],
              tokens
            );
          }
        }
        if (clause.rhs.tag === 'WithClause') {
          const withClause = clause.rhs as any;
          const clausePath = [...path, 'clauses', i];
          for (let scrutineeIndex = 0; scrutineeIndex < withClause.scrutinees.length; scrutineeIndex++) {
            collectSemanticTokensFromSurfaceTerm(
              withClause.scrutinees[scrutineeIndex],
              sourceMap,
              [...clausePath, 'scrutinee'],
              tokens
            );
          }
          for (let withClauseIndex = 0; withClauseIndex < withClause.clauses.length; withClauseIndex++) {
            const nestedClause = withClause.clauses[withClauseIndex];
            const withClausePath = [...clausePath, 'withClauses', withClauseIndex];
            const nestedNamedPatternCount = nestedClause.namedPatterns?.length || 0;
            const totalNestedPatternCount = nestedClause.patterns.length + nestedNamedPatternCount;
            for (let patternIndex = 0; patternIndex < totalNestedPatternCount; patternIndex++) {
              addSemanticTokenDirect([...withClausePath, 'patterns', patternIndex, 'openBrace'], sourceMap, 'namedBrace', tokens);
              addSemanticTokenDirect([...withClausePath, 'patterns', patternIndex, 'closeBrace'], sourceMap, 'namedBrace', tokens);
            }
            for (let patternIndex = 0; patternIndex < nestedClause.patterns.length; patternIndex++) {
              const sourceMapIndex = patternIndex + nestedNamedPatternCount;
              collectSemanticTokensFromSurfacePattern(
                nestedClause.patterns[patternIndex],
                sourceMap,
                [...withClausePath, 'patterns', sourceMapIndex],
                tokens
              );
            }
            if (nestedClause.namedPatterns) {
              for (let patternIndex = 0; patternIndex < nestedClause.namedPatterns.length; patternIndex++) {
                addSemanticTokenDirect([...withClausePath, 'patterns', patternIndex, 'name'], sourceMap, 'boundVar', tokens);
                collectSemanticTokensFromSurfacePattern(
                  nestedClause.namedPatterns[patternIndex].pattern,
                  sourceMap,
                  [...withClausePath, 'patterns', patternIndex, 'pattern'],
                  tokens
                );
              }
            }
            collectSemanticTokensFromSurfaceTerm(
              nestedClause.rhs,
              sourceMap,
              [...withClausePath, 'rhs'],
              tokens
            );
          }
        } else {
          collectSemanticTokensFromSurfaceTerm(
            clause.rhs,
            sourceMap,
            [...path, 'clauses', i, 'rhs'],
            tokens
          );
        }
      }
      break;

    case 'AbsurdMarker':
      addSemanticTokenDirect(path, sourceMap, 'absurd', tokens);
      break;

    case 'ULevel':
      break;

    case 'MultiBinder':
      for (let i = 0; i < term.names.length; i++) {
        addSemanticTokenDirect([...path, 'names', i], sourceMap, 'patternVar', tokens);
      }
      if (term.named) {
        addSemanticTokenDirect([...path, 'openBrace'], sourceMap, 'namedBrace', tokens);
        addSemanticTokenDirect([...path, 'closeBrace'], sourceMap, 'namedBrace', tokens);
      }
      collectSemanticTokensFromSurfaceTerm(term.domain, sourceMap, [...path, 'domain'], tokens);
      collectSemanticTokensFromSurfaceTerm(term.body, sourceMap, [...path, 'body'], tokens);
      break;

    case 'WithClause': {
      const withClause = term as any;
      for (let scrutineeIndex = 0; scrutineeIndex < withClause.scrutinees.length; scrutineeIndex++) {
        collectSemanticTokensFromSurfaceTerm(
          withClause.scrutinees[scrutineeIndex],
          sourceMap,
          [...path, 'scrutinee'],
          tokens
        );
      }
      for (let i = 0; i < withClause.clauses.length; i++) {
        const clause = withClause.clauses[i];
        const withClausePath = [...path, 'withClauses', i];
        for (let patternIndex = 0; patternIndex < clause.patterns.length; patternIndex++) {
          collectSemanticTokensFromSurfacePattern(
            clause.patterns[patternIndex],
            sourceMap,
            [...withClausePath, 'patterns', patternIndex],
            tokens
          );
        }
        collectSemanticTokensFromSurfaceTerm(
          clause.rhs,
          sourceMap,
          [...withClausePath, 'rhs'],
          tokens
        );
      }
      break;
    }

    case 'TacticBlock':
      for (let i = 0; i < term.tactics.length; i++) {
        collectSemanticTokensFromTactic(
          term.tactics[i],
          sourceMap,
          [...path, 'tactics', i],
          tokens
        );
      }
      break;
  }
}

function collectSemanticTokensFromTactic(
  tactic: TacticCommand,
  sourceMap: SourceMap,
  path: (string | number)[],
  tokens: SemanticToken[]
): void {
  addSemanticTokenDirect([...path, 'name'], sourceMap, 'tacticName', tokens);

  switch (tactic.name) {
    case 'intro':
    case 'intros':
      for (let i = 0; i < tactic.args.length; i++) {
        addSemanticTokenDirect([...path, 'args', i], sourceMap, 'boundVar', tokens);
      }
      break;

    case 'exact':
    case 'apply':
    case 'refine':
    case 'rewrite':
    case 'subst':
    case 'rw':
    case 'erw':
    case 'unfold':
      for (let i = 0; i < tactic.args.length; i++) {
        collectSemanticTokensFromSurfaceTerm(tactic.args[i], sourceMap, [...path, 'args', i], tokens);
      }
      break;

    case 'cases':
    case 'induction':
      if (tactic.args.length > 0) {
        if (tactic.name === 'induction') {
          addSemanticTokenDirect([...path, 'args', 0], sourceMap, 'boundVar', tokens);
        } else {
          collectSemanticTokensFromSurfaceTerm(tactic.args[0], sourceMap, [...path, 'args', 0], tokens);
        }
      }
      if (tactic.caseBranches) {
        for (let branchIndex = 0; branchIndex < tactic.caseBranches.length; branchIndex++) {
          const branch = tactic.caseBranches[branchIndex];
          const branchPath = [...path, 'caseBranches', branchIndex];
          addSemanticTokenDirect([...branchPath, 'constructor'], sourceMap, 'constName', tokens);
          for (let paramIndex = 0; paramIndex < branch.params.length; paramIndex++) {
            addSemanticTokenDirect([...branchPath, 'params', paramIndex], sourceMap, 'boundVar', tokens);
          }
          for (let tacticIndex = 0; tacticIndex < branch.tactics.length; tacticIndex++) {
            collectSemanticTokensFromTactic(
              branch.tactics[tacticIndex],
              sourceMap,
              [...branchPath, 'tactics', tacticIndex],
              tokens
            );
          }
        }
      }
      break;

    case 'have':
      if (tactic.args.length > 0) {
        addSemanticTokenDirect([...path, 'args', 0], sourceMap, 'boundVar', tokens);
      }
      if (tactic.args.length > 1) {
        collectSemanticTokensFromSurfaceTerm(tactic.args[1], sourceMap, [...path, 'args', 1], tokens);
      }
      if (tactic.args.length > 2) {
        collectSemanticTokensFromSurfaceTerm(tactic.args[2], sourceMap, [...path, 'args', 2], tokens);
      }
      break;

    case 'obtain':
      for (let i = 0; i < tactic.args.length - 1; i++) {
        addSemanticTokenDirect([...path, 'args', i], sourceMap, 'boundVar', tokens);
      }
      if (tactic.args.length > 0) {
        const proofIndex = tactic.args.length - 1;
        collectSemanticTokensFromSurfaceTerm(tactic.args[proofIndex], sourceMap, [...path, 'args', proofIndex], tokens);
      }
      break;

    case 'suffices':
      if (tactic.args.length > 0) {
        addSemanticTokenDirect([...path, 'args', 0], sourceMap, 'boundVar', tokens);
      }
      if (tactic.args.length > 1) {
        collectSemanticTokensFromSurfaceTerm(tactic.args[1], sourceMap, [...path, 'args', 1], tokens);
      }
      if (tactic.focusedTactics) {
        for (let i = 0; i < tactic.focusedTactics.length; i++) {
          collectSemanticTokensFromTactic(
            tactic.focusedTactics[i],
            sourceMap,
            [...path, 'focusedTactics', i],
            tokens
          );
        }
      }
      break;

    default:
      break;
  }

  if (tactic.focusedTactics) {
    for (let i = 0; i < tactic.focusedTactics.length; i++) {
      collectSemanticTokensFromTactic(
        tactic.focusedTactics[i],
        sourceMap,
        [...path, 'focusedTactics', i],
        tokens
      );
    }
  }
}

function collectSemanticTokensFromSurfacePattern(
  pattern: TPattern,
  sourceMap: SourceMap,
  path: (string | number)[],
  tokens: SemanticToken[]
): void {
  switch (pattern.tag) {
    case 'PVar':
    case 'PWild':
      addSemanticTokenDirect(path, sourceMap, 'patternVar', tokens);
      if (pattern.named) {
        addSemanticTokenDirect([...path, 'openBrace'], sourceMap, 'namedBrace', tokens);
        addSemanticTokenDirect([...path, 'closeBrace'], sourceMap, 'namedBrace', tokens);
      }
      break;

    case 'PCtor': {
      const namedArgCount = pattern.namedArgs?.length || 0;
      if (pattern.args.length > 0 || namedArgCount > 0) {
        addSemanticTokenDirect([...path, 'name'], sourceMap, 'constName', tokens);

        const totalArgCount = pattern.args.length + namedArgCount;
        for (let i = 0; i < totalArgCount; i++) {
          addSemanticTokenDirect([...path, 'args', i, 'openBrace'], sourceMap, 'namedBrace', tokens);
          addSemanticTokenDirect([...path, 'args', i, 'closeBrace'], sourceMap, 'namedBrace', tokens);
        }

        for (let i = 0; i < pattern.args.length; i++) {
          const sourceMapIndex = i + namedArgCount;
          collectSemanticTokensFromSurfacePattern(
            pattern.args[i],
            sourceMap,
            [...path, 'args', sourceMapIndex],
            tokens
          );
        }

        if (pattern.namedArgs) {
          for (let i = 0; i < pattern.namedArgs.length; i++) {
            addSemanticTokenDirect([...path, 'args', i, 'name'], sourceMap, 'boundVar', tokens);
            collectSemanticTokensFromSurfacePattern(
              pattern.namedArgs[i].pattern,
              sourceMap,
              [...path, 'args', i, 'pattern'],
              tokens
            );
          }
        }
      } else {
        addSemanticTokenDirect(path, sourceMap, 'constName', tokens);
      }
      break;
    }
  }
}

function addSemanticTokenDirect(
  path: (string | number)[],
  sourceMap: SourceMap,
  type: SemanticTokenType,
  tokens: SemanticToken[]
): void {
  const pathStr = serializePathForLookup(path);
  const range = sourceMap.get(pathStr);
  if (!range) return;

  const length = range.start.line === range.end.line
    ? range.end.col - range.start.col
    : 1;
  if (length <= 0) return;

  tokens.push({
    line: range.start.line,
    column: range.start.col,
    length,
    type,
  });
}

/**
 * Extract hole locations from a compile result for warning markers.
 */
export function extractHoleLocations(result: CompileResult): HoleLocation[] {
  const holes: HoleLocation[] = [];

  for (const block of result.blocks) {
    for (const decl of block.declarations) {
      if (!decl.sourceMap) continue;
      if ((decl as any).isWithAuxiliary) continue;

      if (decl.surfaceType) {
        collectHolesFromSurfaceTerm(decl.surfaceType, decl.sourceMap, ['type'], holes);
      }

      if (decl.surfaceValue) {
        collectHolesFromSurfaceTerm(decl.surfaceValue, decl.sourceMap, ['value'], holes);
      }

      if (decl.surfaceConstructors) {
        for (let i = 0; i < decl.surfaceConstructors.length; i++) {
          collectHolesFromSurfaceTerm(
            decl.surfaceConstructors[i].type,
            decl.sourceMap,
            ['constructors', i, 'type'],
            holes
          );
        }
      }
    }
  }

  return holes;
}

function collectHolesFromSurfaceTerm(
  term: TTerm,
  sourceMap: SourceMap,
  path: (string | number)[],
  holes: HoleLocation[]
): void {
  switch (term.tag) {
    case 'Hole':
      if (term.id !== '_') {
        addHoleLocation(path, sourceMap, term.id, holes);
      }
      collectHolesFromSurfaceTerm(term.type, sourceMap, [...path, 'type'], holes);
      break;

    case 'Var':
    case 'Const':
    case 'Sort':
      break;

    case 'Binder':
      if (term.domain !== undefined) {
        collectHolesFromSurfaceTerm(term.domain, sourceMap, [...path, 'domain'], holes);
      }
      collectHolesFromSurfaceTerm(term.body, sourceMap, [...path, 'body'], holes);
      if (term.binderKind.tag === 'BLetTT') {
        collectHolesFromSurfaceTerm(
          term.binderKind.defVal,
          sourceMap,
          [...path, 'bindings', 0, 'value'],
          holes
        );
      }
      break;

    case 'App':
      collectHolesFromSurfaceTerm(term.fn, sourceMap, [...path, 'fn'], holes);
      collectHolesFromSurfaceTerm(term.arg, sourceMap, [...path, 'arg'], holes);
      break;

    case 'Annot':
      collectHolesFromSurfaceTerm(term.term, sourceMap, [...path, 'term'], holes);
      collectHolesFromSurfaceTerm(term.type, sourceMap, [...path, 'type'], holes);
      break;

    case 'WithClause':
    case 'Match': {
      if (term.tag === 'Match') {
        collectHolesFromSurfaceTerm(term.scrutinee, sourceMap, [...path, 'scrutinee'], holes);
      }
      const isWith = term.tag === 'WithClause';
      const clauses = (term as any).clauses as { rhs: TTerm; patterns: any[] }[];
      if (isWith) {
        const withClause = term as any;
        for (let i = 0; i < withClause.scrutinees.length; i++) {
          collectHolesFromSurfaceTerm(withClause.scrutinees[i], sourceMap, [...path, 'scrutinee'], holes);
        }
      }
      for (let i = 0; i < clauses.length; i++) {
        const clause = clauses[i];
        if (isWith) {
          collectHolesFromSurfaceTerm(clause.rhs, sourceMap, [...path, 'withClauses', i, 'rhs'], holes);
        } else if (clause.rhs.tag === 'WithClause') {
          collectHolesFromSurfaceTerm(clause.rhs, sourceMap, [...path, 'clauses', i], holes);
        } else {
          collectHolesFromSurfaceTerm(clause.rhs, sourceMap, [...path, 'clauses', i, 'rhs'], holes);
        }
      }
      break;
    }
  }
}

function addHoleLocation(
  path: (string | number)[],
  sourceMap: SourceMap,
  id: string,
  holes: HoleLocation[]
): void {
  const pathStr = serializePathForLookup(path);
  const range = sourceMap.get(pathStr);
  if (!range) return;

  holes.push({
    line: range.start.line,
    column: range.start.col,
    endColumn: range.end.col,
    id,
  });
}

/**
 * Extract wildcard inlay hints from a compile result.
 */
export function extractWildcardInlayHints(result: CompileResult): WildcardInlayHint[] {
  if (!SHOW_WILDCARD_INLAY_HINTS) {
    return [];
  }

  const hints: WildcardInlayHint[] = [];

  for (const block of result.blocks) {
    for (const decl of block.declarations) {
      if (!decl.kernelValue) continue;
      collectWildcardsFromTerm(
        decl.kernelValue,
        decl.elabMap,
        decl.sourceMap,
        ['value'],
        hints
      );
    }
  }

  return hints;
}

function collectWildcardsFromTerm(
  term: TTKTerm,
  elabMap: ElabMap | undefined,
  sourceMap: SourceMap | undefined,
  path: (string | number)[],
  hints: WildcardInlayHint[]
): void {
  if (!elabMap || !sourceMap) return;

  switch (term.tag) {
    case 'Match':
      for (let clauseIndex = 0; clauseIndex < term.clauses.length; clauseIndex++) {
        const clause = term.clauses[clauseIndex];
        for (let patternIndex = 0; patternIndex < clause.patterns.length; patternIndex++) {
          collectWildcardsFromPattern(
            clause.patterns[patternIndex],
            elabMap,
            sourceMap,
            [...path, 'clauses', clauseIndex, 'patterns', patternIndex],
            hints
          );
        }
        collectWildcardsFromTerm(
          clause.rhs,
          elabMap,
          sourceMap,
          [...path, 'clauses', clauseIndex, 'rhs'],
          hints
        );
      }
      collectWildcardsFromTerm(term.scrutinee, elabMap, sourceMap, [...path, 'scrutinee'], hints);
      break;

    case 'Binder':
      collectWildcardsFromTerm(term.domain, elabMap, sourceMap, [...path, 'domain'], hints);
      collectWildcardsFromTerm(term.body, elabMap, sourceMap, [...path, 'body'], hints);
      if (term.binderKind.tag === 'BLet') {
        collectWildcardsFromTerm(term.binderKind.defVal, elabMap, sourceMap, [...path, 'binderKind', 'defVal'], hints);
      }
      break;

    case 'App':
      collectWildcardsFromTerm(term.fn, elabMap, sourceMap, [...path, 'fn'], hints);
      collectWildcardsFromTerm(term.arg, elabMap, sourceMap, [...path, 'arg'], hints);
      break;

    case 'Annot':
      collectWildcardsFromTerm(term.term, elabMap, sourceMap, [...path, 'term'], hints);
      collectWildcardsFromTerm(term.type, elabMap, sourceMap, [...path, 'type'], hints);
      break;

    case 'Hole':
    case 'Meta':
    case 'Var':
    case 'Sort':
    case 'Const':
      break;
  }
}

function collectWildcardsFromPattern(
  pattern: TTKPattern,
  elabMap: ElabMap,
  sourceMap: SourceMap,
  path: (string | number)[],
  hints: WildcardInlayHint[]
): void {
  const pathStr = serializePathForLookup(path);

  if (pattern.tag === 'PWild') {
    const surfacePathStr = elabMap.get(pathStr);
    if (!surfacePathStr) return;
    const range = sourceMap.get(surfacePathStr);
    if (!range) return;
    hints.push({
      line: range.start.line,
      column: range.end.col,
      name: pattern.name,
    });
  } else if (pattern.tag === 'PCtor') {
    for (let i = 0; i < pattern.args.length; i++) {
      collectWildcardsFromPattern(
        pattern.args[i],
        elabMap,
        sourceMap,
        [...path, 'args', i],
        hints
      );
    }
  }
}
