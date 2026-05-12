import type { CompiledDeclaration } from './compile-types';
import type { SourceMap } from '../types/source-position';

/**
 * Remap an auxiliary with-function's elabMap to the original with-clause
 * surface paths recorded in the parent declaration's source map.
 */
export function remapWithClauseElabMap(
  compiled: CompiledDeclaration,
  sourceMap: SourceMap,
  withScrutineeCount: number,
  newScrutineeCount: number,
): void {
  if (!compiled.elabMap) return;

  let numFunctionPatterns = 0;
  if (compiled.kernelValue?.tag === 'Match' && compiled.kernelValue.clauses.length > 0) {
    const totalPatterns = compiled.kernelValue.clauses[0].patterns.length;
    numFunctionPatterns = totalPatterns - withScrutineeCount;
  } else if (compiled.surfaceValue?.tag === 'Match' && compiled.surfaceValue.clauses.length > 0) {
    const totalPatterns = compiled.surfaceValue.clauses[0].patterns.length;
    numFunctionPatterns = totalPatterns - withScrutineeCount;
  }

  let hasNestedMatch = false;
  const surfaceMatch = compiled.surfaceValue?.tag === 'Match' ? compiled.surfaceValue : null;
  if (surfaceMatch && surfaceMatch.clauses.length === 1) {
    const rhs = surfaceMatch.clauses[0].rhs;
    if (rhs.tag === 'Match') {
      hasNestedMatch = true;
    }
  }

  const withClausePattern = /^value\.clauses\[(\d+)\]\.withClauses\[(\d+)\](.*)/;

  const remapPatternSuffix = (rawSuffix: string, functionPatternCount: number): string => {
    const patternMatch = rawSuffix.match(/^\.patterns\[(\d+)\](.*)/);
    if (!patternMatch) return rawSuffix;

    const withPatIdx = parseInt(patternMatch[1]);
    const patSuffix = patternMatch[2];
    return `.patterns[${functionPatternCount + withPatIdx}]${patSuffix}`;
  };

  for (const [path] of sourceMap) {
    if (!path.includes('.withClauses[')) continue;

    const allWithMatches = path.match(/\.withClauses\[(\d+)\]/g);
    if (!allWithMatches) continue;

    if (allWithMatches.length === 1) {
      const match = path.match(withClausePattern);
      if (!match) continue;

      const withIdx = parseInt(match[2]);
      const rawSuffix = match[3];
      const suffix = remapPatternSuffix(rawSuffix, numFunctionPatterns);
      const kernelPath = `value.clauses[${withIdx}]${suffix}`;
      compiled.elabMap.set(kernelPath, path);
    } else {
      if (newScrutineeCount >= withScrutineeCount) continue;

      const lastWithIndex = path.lastIndexOf('.withClauses[');
      const remainder = path.substring(lastWithIndex);
      const remainderMatch = remainder.match(/^\.withClauses\[(\d+)\](.*)/);
      if (!remainderMatch) continue;

      const withIdx = parseInt(remainderMatch[1]);
      const rawSuffix = remainderMatch[2];
      const suffix = remapPatternSuffix(rawSuffix, numFunctionPatterns + (withScrutineeCount - newScrutineeCount));
      const kernelPath = `value.clauses[${withIdx}]${suffix}`;
      compiled.elabMap.set(kernelPath, path);
    }
  }

  for (const [path] of sourceMap) {
    const scrutineeMatch = path.match(/^value\.clauses\[(\d+)\]\.withClauses\[(\d+)\]\.rhs\.scrutinee(.*)$/);
    if (!scrutineeMatch) continue;

    const withIdx = parseInt(scrutineeMatch[2]);
    const suffix = scrutineeMatch[3];
    const kernelPath = `value.clauses[${withIdx}].rhs.arg${suffix}`;
    compiled.elabMap.set(kernelPath, path);
  }

  if (hasNestedMatch) {
    const parentWithPattern = /^value\.clauses\[(\d+)\]\.withClauses\[0\]/;
    for (const [path] of sourceMap) {
      const match = path.match(parentWithPattern);
      if (!match) continue;

      const clauseIdx = match[1];
      const parentEntry = `value.clauses[${clauseIdx}]`;
      if (sourceMap.has(parentEntry)) {
        compiled.elabMap.set('value.clauses[0].rhs', parentEntry);
        break;
      }
    }
  }
}

/**
 * Remap the main declaration's scrutinee paths so type-at-cursor can find
 * with-clause scrutinee info through the rewritten auxiliary call.
 */
export function remapWithScrutineeInMainElabMap(
  compiled: CompiledDeclaration,
  sourceMap: SourceMap,
): void {
  if (!compiled.elabMap) return;

  const scrutineePattern = /^value\.clauses\[(\d+)\]\.scrutinee/;
  const nestedScrutineePattern = /\.scrutinee($|\.)/;

  for (const [path] of sourceMap) {
    const directMatch = path.match(scrutineePattern);
    if (directMatch) {
      const clauseIdx = parseInt(directMatch[1]);
      const suffix = path.substring(`value.clauses[${clauseIdx}].scrutinee`.length);
      const kernelRhsBase = `value.clauses[${clauseIdx}].rhs`;
      if (suffix === '' || suffix === '.fn' || suffix === '.arg') {
        const kernelPath = suffix === '' ? `${kernelRhsBase}.arg` : `${kernelRhsBase}.arg${suffix}`;
        compiled.elabMap.set(kernelPath, path);
      }
    } else if (path.includes('.withClauses[') && nestedScrutineePattern.test(path)) {
      continue;
    }
  }
}

/**
 * Merge an auxiliary declaration's type info into the main declaration under
 * surface paths so IDE queries can resolve with-clause subterms directly.
 */
export function mergeAuxTypeInfoIntoMain(
  mainCompiled: CompiledDeclaration,
  auxCompiled: CompiledDeclaration,
): void {
  if (!auxCompiled.typeInfoMap || !auxCompiled.elabMap) return;
  if (!mainCompiled.typeInfoMap) {
    mainCompiled.typeInfoMap = new Map();
  }
  if (!mainCompiled.elabMap) {
    mainCompiled.elabMap = new Map();
  }

  const auxReverse = new Map<string, string>();
  for (const [kernelPath, surfacePath] of auxCompiled.elabMap) {
    auxReverse.set(kernelPath, surfacePath);
  }

  for (const [kernelPath, entry] of auxCompiled.typeInfoMap) {
    const surfacePath = auxReverse.get(kernelPath);
    if (surfacePath) {
      mainCompiled.typeInfoMap.set(surfacePath, {
        ...entry,
        kernelPath: surfacePath,
      });
      continue;
    }

    let path = kernelPath;
    while (path !== '') {
      const mapped = auxReverse.get(path);
      if (mapped) {
        const suffix = kernelPath.substring(path.length);
        const surfaceKey = mapped + suffix;
        mainCompiled.typeInfoMap.set(surfaceKey, {
          ...entry,
          kernelPath: surfaceKey,
        });
        break;
      }
      const lastDot = path.lastIndexOf('.');
      const lastBracket = path.lastIndexOf('[');
      const cutPoint = Math.max(lastDot, lastBracket);
      if (cutPoint <= 0) break;
      path = path.substring(0, cutPoint);
    }
  }
}
