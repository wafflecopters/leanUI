/**
 * Fresh TT Compiler - A clean implementation of the compilation pipeline
 *
 * This module provides a simple interface for compiling TT source code
 * to elaborated kernel terms (TTK).
 */

import { ParsedDeclaration, ParseError } from '../parser/parser';
import { elabPatternToKernel, elabPatternToKernelWithMap, resetWildcardCounter, extractConstructorParamNames, setConstructorParamNames, setCurrentTermParamNames, reorderPatterns, hasNamedPatterns, applyVarPermutation, fixRhsForConstructorPatterns, fixRhsForVariablePatterns, NamedArgMap, elabToKernel } from './elab';
import { TTKTerm, TTKContext, TTKClause, TTKPattern, prettyPrintPattern, prettyPrintPatternList, mkType } from './kernel';
import { TTerm, TPattern, TClause, mkULitTT, mkSortTT, mkUOmegaTT } from './surface';
import { arraySeg, fieldSeg, appendPath, ElabMap, IndexPath, SourceMap, serializeIndexPath } from '../types/source-position'
import { inferType } from './checker';
import { addDefinitionInTCEnv, countPiBinders, createTCEnv, DefinitionsMap, extractPiSpine, InductiveDefinition, MatchPartIndex, TCEnv, TCEnvError, TermDefinition, TermDefinitionPartIndex, validateTermNameNotDefined } from './term';
import { checkMatchClause, arePatternsAbsurd } from './patterns';
import { checkTotality, TotalityResult, CaseTree } from './totality';
import { checkStructuralRecursion } from './recursion';
import { resetWithCounter } from './with-desugar';
import { subst } from './subst';
import { IncrementalCache } from './incremental';
import { whnf } from './whnf';
import type { TypeInfoMap } from './type-info';
import { createInitialEngine, TacticEngine } from '../tactics/tacticsEngine';
import { ExactTactic, AssumptionTactic, IntroTactic, IntrosTactic, ApplyTactic, TacticSequence, Tactic } from '../tactics/tactic';
import { CasesTactic } from '../tactics/cases-tactic';
import { ReflexivityTactic } from '../tactics/reflexivity-tactic';
import { InductionTactic } from '../tactics/induction-tactic';
import { RewriteTactic } from '../tactics/rewrite-tactic';
import { SymmetryTactic } from '../tactics/symmetry-tactic';
import { TransitivityTactic } from '../tactics/transitivity-tactic';
import { CongTactic } from '../tactics/cong-tactic';
import { SubstTactic } from '../tactics/subst-tactic';
import { HaveTactic } from '../tactics/have-tactic';
import { ObtainTactic } from '../tactics/obtain-tactic';
import { SufficesTactic } from '../tactics/suffices-tactic';
import { UnfoldTactic } from '../tactics/unfold-tactic';
import { ConstructorTactic } from '../tactics/constructor-tactic';
import { FocusTactic } from '../tactics/focus-tactic';
import { TacticCommand, TTacticBlock, CaseBranch, allPatternVarNames } from './surface';
import { desugarNestedCaseBranch } from './case-pattern-desugar';
import { TacticInfoTree, TacticInfoNode, SourcePosition } from '../tactics/info-tree';
import { elaborateTacticArg, tacticCommandToTactic as sharedTacticCommandToTactic, shouldKeepArgAsName } from '../tactics/elaborate-tactic-arg';
import { extractGoalStates, engineToProofState } from '../tactics/proof-state';
import { parseTTSource } from './compile-parse';
import type {
  CompileOptions,
  CompileResult,
  ElabDeclaration,
  ProcessDeclarationResult,
} from './compile-types';
import {
  extractHoleLocations,
  extractSemanticTokens,
  extractWildcardInlayHints,
} from './compile-editor-data';
import {
  collectAppSpine,
  kernelTypeToSurface,
  lookupNamedArgMap,
} from './compile-bridge';
import { tryCaseSplitsInSearchOfAbsurdity } from './compile-term-value';
import { resolveWithScrutineeTypes } from './compile-with-scrutinee-resolution';
import {
  compileParsedBlocks,
  compileParsedBlocksIncrementally,
  reuseLastIncrementalResult,
} from './compile-loop-orchestration';
export type {
  CompileOptions,
  CompileResult,
  CompiledBlock,
  CompiledDeclaration,
  ElabDeclaration,
  NameResolutionErrorWithRange,
  ParseResult,
  ParsedBlock,
  ProcessDeclarationResult,
} from './compile-types';
export type { TotalityResult, CaseTree };
export {
  extractDirectiveTokens,
  extractHoleLocations,
  extractSemanticTokens,
  extractWildcardInlayHints,
  SHOW_WILDCARD_INLAY_HINTS,
  type HoleLocation,
  type SemanticToken,
  type SemanticTokenType,
  type WildcardInlayHint,
} from './compile-editor-data';

// ============================================================================
// SourceMap Adjustment Helper
// ============================================================================



export { parseTTSource };

/**
 * Convert a tactic command to a Tactic object — delegates to shared module.
 */
const tacticCommandToTactic = sharedTacticCommandToTactic;

/**
 * Recursively apply structured case branches to matching goals.
 *
 * This handles arbitrary nesting depth: each branch's tactics are applied,
 * and if any tactic itself has caseBranches (nested cases/induction),
 * those are processed recursively.
 */
function applyCaseBranchesRecursive(
  engine: TacticEngine,
  caseBranches: readonly CaseBranch[],
  definitions: DefinitionsMap,
  outerParamNameMap: Map<string, string>,
  parentInfoNode: TacticInfoNode,
  hasSorry: boolean,
  indexPathToSourcePosition: (indexPath: IndexPath | undefined, sourceMap: SourceMap) => SourcePosition,
  sourceMap: SourceMap
): { engine: TacticEngine; hasSorry: boolean } {
  for (const rawBranch of caseBranches) {
    // Desugar nested constructor patterns into sequential `cases` calls so
    // downstream logic only sees flat params (all `tag: 'var'`).
    const branch = desugarNestedCaseBranch(rawBranch);
    // Find the goal with matching caseTag
    const branchGoalId = engine.goals.find(gid => {
      const meta = engine.metaVars.get(gid);
      return meta && meta.caseTag === branch.constructor;
    });

    if (!branchGoalId) {
      throw new Error(`Structured cases: no goal found for constructor '${branch.constructor}'`);
    }

    // Set focus to this branch goal
    const branchGoalIndex = engine.goals.indexOf(branchGoalId);
    engine = engine.withUpdates({ focusIndex: branchGoalIndex });

    // Build paramNameMap once from the initial branch context (before any branch tactics run).
    // Pattern params (e.g., 'n'' in '| Succ n' IH =>') map to the actual context names
    // assigned by the cases/induction tactic. This mapping must stay fixed even as later
    // tactics (like intro) extend the context.
    // Include outer branch mappings so nested cases can reference outer params.
    const initialBranchGoal = engine.getFocusedGoal()!;
    const initialCtx: string[] = initialBranchGoal.ctx.map(b => b.name);
    const paramNameMap = new Map<string, string>(outerParamNameMap);
    // After desugarNestedCaseBranch, branch.params is flat (all `tag: 'var'`),
    // so collapsing to names matches the context positions directly.
    const branchParamNames = allPatternVarNames(branch.params);
    for (let i = 0; i < branchParamNames.length; i++) {
      const patternParamName = branchParamNames[i];
      const ctxIndex = initialCtx.length - branchParamNames.length + i;
      if (ctxIndex >= 0 && ctxIndex < initialCtx.length) {
        paramNameMap.set(patternParamName, initialCtx[ctxIndex]);
      }
    }

    // Apply the branch's tactics
    for (const branchTactic of branch.tactics) {
      const branchGoal = engine.getFocusedGoal();
      const branchGoalId2 = engine.getFocusedGoalId();

      if (!branchGoal || !branchGoalId2) {
        throw new Error(`Structured cases: no active goal for constructor '${branch.constructor}'`);
      }

      const branchElabArgs: Array<TTerm | TTKTerm> = branchTactic.args.map((arg, i) => {
        if (shouldKeepArgAsName(branchTactic.name, i, branchTactic.args.length)) {
          return arg;
        }
        return elaborateTacticArg(arg, branchGoal.ctx, definitions, 0, paramNameMap);
      });

      // Elaborate focused tactics (· bullets) recursively if present
      let branchFocused: Tactic[] | undefined;
      if (branchTactic.focusedTactics && branchTactic.focusedTactics.length > 0) {
        function elabBranchFocused(ft: TacticCommand): Tactic {
          const ftArgs: Array<TTerm | TTKTerm> = ft.args.map((arg, i) => {
            if (shouldKeepArgAsName(ft.name, i, ft.args.length)) return arg;
            return elaborateTacticArg(arg, branchGoal!.ctx, definitions, 0, paramNameMap);
          });
          let nested: Tactic[] | undefined;
          if (ft.focusedTactics && ft.focusedTactics.length > 0) {
            nested = ft.focusedTactics.map(inner => elabBranchFocused(inner));
          }
          const t = sharedTacticCommandToTactic({ name: ft.name, args: ftArgs, focusedTactics: nested });
          if (t === 'sorry') {
            hasSorry = true;
            return { name: 'sorry', apply: (_eng: TacticEngine) => ({ success: true, newEngine: _eng }) } as Tactic;
          }
          return t;
        }
        branchFocused = branchTactic.focusedTactics.map(elabBranchFocused);
      }

      // Get goals before applying tactic
      const branchGoalsBefore = extractGoalStates(engineToProofState(engine));

      const branchTacticObj = sharedTacticCommandToTactic({ name: branchTactic.name, args: branchElabArgs, focusedTactics: branchFocused });

      // sorry: leave goal unsolved
      if (branchTacticObj === 'sorry') {
        hasSorry = true;
        continue;
      }

      const branchResult = branchTacticObj.apply(engine, branchGoal, branchGoalId2);

      if (!branchResult.success) {
        const errorMsg = `Structured cases (${branch.constructor}): tactic '${branchTactic.name}' failed: ${branchResult.error}`;
        if (branchTactic.indexPath) {
          const tacticEnv = createTCEnv({ definitions, indexPath: branchTactic.indexPath, options: { mode: 'check' } });
          throw TCEnvError.create(errorMsg, tacticEnv);
        } else {
          throw new Error(errorMsg);
        }
      }

      engine = branchResult.newEngine;

      // Get goals after applying tactic
      const branchGoalsAfter = extractGoalStates(engineToProofState(engine));

      // Get position for this branch tactic
      const branchPosition = branchTactic.indexPath
        ? indexPathToSourcePosition(branchTactic.indexPath, sourceMap)
        : { line: 0, col: 0 };

      // Create InfoTree node for branch tactic and add as child of parent node
      const branchTacticNode: TacticInfoNode = {
        position: branchPosition,
        goalsBefore: branchGoalsBefore,
        goalsAfter: branchGoalsAfter,
        tactic: { tag: branchTactic.name } as any,
        children: []
      };
      parentInfoNode.children.push(branchTacticNode);

      // Handle nested structured cases/induction recursively
      if ((branchTactic.name === 'cases' || branchTactic.name === 'induction') && branchTactic.caseBranches) {
        const nestedResult = applyCaseBranchesRecursive(
          engine, branchTactic.caseBranches, definitions, paramNameMap, branchTacticNode,
          hasSorry, indexPathToSourcePosition, sourceMap
        );
        engine = nestedResult.engine;
        hasSorry = nestedResult.hasSorry;
      }
    }
  }

  return { engine, hasSorry };
}

/**
 * Elaborate a TacticBlock to a kernel term by executing the tactics.
 *
 * @param tacticBlock - The surface-level tactic block
 * @param expectedType - The expected type for the proof (kernel term)
 * @param definitions - Definitions map for type checking
 * @param elabMap - Elaboration map for elaborating tactic arguments
 * @param context - Optional typing context (for nested proofs)
 * @returns The proof term (kernel term)
 */
function elaborateTacticBlock(
  tacticBlock: TTacticBlock,
  expectedType: TTKTerm,
  definitions: DefinitionsMap,
  _elabMap: ElabMap,
  sourceMap: SourceMap,
  context: TTKContext = []
): { term: TTKTerm; infoTree: TacticInfoTree } {
  // Check if empty
  if (tacticBlock.tactics.length === 0) {
    throw new Error('Tactic proof has no tactics (unsolved goals)');
  }

  // Helper: Convert IndexPath to SourcePosition
  function indexPathToSourcePosition(
    indexPath: IndexPath | undefined,
    sourceMap: SourceMap
  ): SourcePosition {
    if (!indexPath) return { line: 0, col: 0 };

    const serialized = serializeIndexPath(indexPath);
    let range = sourceMap.get(serialized);

    // If not found, try the tactic name field (parser records name but not the command itself)
    if (!range) {
      const namePathSerialized = serializeIndexPath([...indexPath, { kind: 'field', name: 'name' }]);
      range = sourceMap.get(namePathSerialized);
    }

    if (!range) return { line: 0, col: 0 };

    return {
      line: range.start.line,
      col: range.start.col,
      endLine: range.end.line,
      endCol: range.end.col
    };
  }

  // Create initial tactic engine
  let engine = createInitialEngine(expectedType, context, definitions);
  let hasSorry = false;

  // Create InfoTree root
  const rootNode: TacticInfoNode = {
    position: { line: 0, col: 0 },
    goalsBefore: extractGoalStates(engineToProofState(engine)),
    goalsAfter: extractGoalStates(engineToProofState(engine)),
    tactic: { tag: 'Intro' } as any, // Dummy
    children: []
  };

  // Execute each tactic, elaborating arguments in the current goal's context
  for (const cmd of tacticBlock.tactics) {
    const goal = engine.getFocusedGoal();
    const goalId = engine.getFocusedGoalId();

    if (!goal || !goalId) {
      throw new Error('Tactic proof: no active goal');
    }

    // Elaborate arguments in the CURRENT goal's context using shared elaboration
    const elabArgs: Array<TTerm | TTKTerm> = cmd.args.map((arg, argIndex) => {
      if (shouldKeepArgAsName(cmd.name, argIndex, cmd.args.length)) {
        return arg;
      }
      return elaborateTacticArg(arg, goal.ctx, definitions);
    });

    // Elaborate focused tactics (for bullet syntax and suffices closing tactics)
    let elabFocusedTactics: Tactic[] | undefined;
    if (cmd.focusedTactics && cmd.focusedTactics.length > 0) {
      // For suffices, the closing tactics see the hypothesis name in scope
      const sufficesHypName = cmd.name === 'suffices' && cmd.args.length >= 1 && cmd.args[0].tag === 'Const'
        ? (cmd.args[0] as any).name as string
        : undefined;

      // Recursively elaborate focused tactics (handles nested bullets)
      function elabOneFocusedTactic(focusedCmd: TacticCommand, ctx: TTKContext): Tactic {
        const focusedElabArgs: Array<TTerm | TTKTerm> = focusedCmd.args.map((arg, i) => {
          if (shouldKeepArgAsName(focusedCmd.name, i, focusedCmd.args.length)) return arg;
          return elaborateTacticArg(arg, ctx, definitions);
        });
        // Recurse: if this focused tactic itself has focusedTactics, elaborate them
        let nestedFocused: Tactic[] | undefined;
        if (focusedCmd.focusedTactics && focusedCmd.focusedTactics.length > 0) {
          nestedFocused = focusedCmd.focusedTactics.map(ft => elabOneFocusedTactic(ft, ctx));
        }
        const t = sharedTacticCommandToTactic({ name: focusedCmd.name, args: focusedElabArgs, focusedTactics: nestedFocused });
        if (t === 'sorry') {
          hasSorry = true;
          return { name: 'sorry', apply: (_eng, _goal, _goalId) => ({ success: true, newEngine: _eng }) } as Tactic;
        }
        return t;
      }
      const focusedCtx = sufficesHypName
        ? [...goal.ctx, { name: sufficesHypName, type: { tag: 'Hole' as const, id: '_suffices_type' } }]
        : goal.ctx;
      elabFocusedTactics = cmd.focusedTactics.map(fc => elabOneFocusedTactic(fc, focusedCtx));
    }

    // Record goals before tactic application
    const goalsBefore = extractGoalStates(engineToProofState(engine));
    const position = indexPathToSourcePosition(cmd.indexPath, sourceMap);

    // Convert command to Tactic object with elaborated args
    const tactic = sharedTacticCommandToTactic({ name: cmd.name, args: elabArgs, focusedTactics: elabFocusedTactics });

    // sorry tactic: leave goal unsolved (produces a Hole in the proof term)
    if (tactic === 'sorry') {
      hasSorry = true;
      // Record in InfoTree
      const tacticNode: TacticInfoNode = {
        position,
        goalsBefore,
        goalsAfter: goalsBefore,
        tactic: { tag: 'sorry' } as any,
        children: []
      };
      rootNode.children.push(tacticNode);
      continue;
    }

    const result = tactic.apply(engine, goal, goalId);

    if (!result.success) {
      // Record failed tactic in InfoTree
      const errorNode: TacticInfoNode = {
        position,
        goalsBefore,
        goalsAfter: goalsBefore,
        tactic: { tag: cmd.name } as any,
        error: result.error,
        children: []
      };
      rootNode.children.push(errorNode);

      // Create TCEnvError with tactic's indexPath for accurate error positioning
      const errorMsg = `Tactic '${tactic.name}' failed: ${result.error}`;
      if (cmd.indexPath) {
        // Create a temporary env with the tactic's indexPath for error location
        const tacticEnv = createTCEnv({ definitions, indexPath: cmd.indexPath, options: { mode: 'check' } });
        throw TCEnvError.create(errorMsg, tacticEnv);
      } else {
        throw new Error(errorMsg);
      }
    }

    engine = result.newEngine;

    // Record successful tactic in InfoTree
    const goalsAfter = extractGoalStates(engineToProofState(engine));
    const tacticNode: TacticInfoNode = {
      position,
      goalsBefore,
      goalsAfter,
      tactic: { tag: cmd.name } as any,
      children: []
    };
    rootNode.children.push(tacticNode);

    // Handle structured cases/induction: if cmd has caseBranches, apply each branch's tactics to matching goals
    if ((cmd.name === 'cases' || cmd.name === 'induction') && cmd.caseBranches) {
      const branchResult = applyCaseBranchesRecursive(
        engine, cmd.caseBranches, definitions, new Map(), tacticNode,
        hasSorry, indexPathToSourcePosition, sourceMap
      );
      engine = branchResult.engine;
      hasSorry = branchResult.hasSorry;
    }
  }

  // Check that all goals are solved (sorry leaves goals unsolved intentionally)
  const remainingGoals = engine.getUnsolvedGoals();
  if (remainingGoals.length > 0 && !hasSorry) {
    throw new Error(`Tactic proof has unsolved goals: ${remainingGoals.length} remaining`);
  }

  // Zonk (substitute solved metas) to get the final proof term
  return {
    term: engine.zonk(),
    infoTree: new TacticInfoTree(rootNode)
  };
}

/**
 * Parse @assumeK directive from source code.
 *
 * Recognizes (with or without -- prefix):
 *   @assumeK         (equivalent to @assumeK=true)
 *   @assumeK=true
 *   @assumeK=false
 *
 * @returns true if @assumeK or @assumeK=true, false if @assumeK=false, undefined if not present
 */
function parseAssumeKDirective(source: string): boolean | undefined {
  const lines = source.split('\n');
  for (const line of lines) {
    const trimmed = line.trim();
    // Match @assumeK directive (with optional -- comment prefix)
    const match = trimmed.match(/^(?:--\s*)?@assumeK(?:=(\w+))?/);
    if (match) {
      const value = match[1];
      if (!value || value === 'true') return true;
      if (value === 'false') return false;
      // Warning instead of throw for incomplete/invalid directive
      console.warn(`Warning: Invalid @assumeK directive value '${value}'. Expected 'true' or 'false'. Treating as 'false'.`);
      return false;
    }
  }
  return undefined;
}

// ============================================================================
// Zonked Term Rechecking
// ============================================================================

/**
 * Check that a zonked term contains no leftover Meta or Hole nodes.
 * This validates that zonking was complete — all metas were solved and substituted.
 *
 * Skips Match nodes (pattern-match compilation output) since Match nodes
 * are trusted compilation output that may contain internal metas.
 */

function recheckZonkedTerm(
  term: TTKTerm,
  definitions: DefinitionsMap,
  label: string,
): string | undefined {
  // Skip Match values — trusted compilation output
  if (term.tag === 'Match') return undefined;

  // Phase 1: AST walk for leftover metas/holes
  const leftoverMetas: string[] = [];
  const leftoverHoles: string[] = [];

  function walk(t: TTKTerm): void {
    switch (t.tag) {
      case 'Meta':
        leftoverMetas.push(t.id);
        break;
      case 'Hole':
        // Holes that start with ? are user-written holes (?todo etc) — those are fine
        if (!t.id.startsWith('?')) {
          leftoverHoles.push(t.id);
        }
        break;
      case 'App':
        walk(t.fn);
        walk(t.arg);
        break;
      case 'Binder':
        walk(t.domain);
        walk(t.body);
        break;
      case 'Sort':
        walk(t.level);
        break;
      case 'Annot':
        walk(t.term);
        walk(t.type);
        break;
      case 'Match':
        // Skip Match internals — trusted compilation output
        break;
      // Var, Const, ULevel, ULit, UOmega — leaf nodes, nothing to check
    }
  }

  walk(term);

  if (leftoverMetas.length > 0) {
    return `Zonk recheck failed for ${label}: ${leftoverMetas.length} unsolved meta(s) remaining: ${leftoverMetas.join(', ')}`;
  }
  if (leftoverHoles.length > 0) {
    return `Zonk recheck failed for ${label}: ${leftoverHoles.length} unresolved hole(s) remaining: ${leftoverHoles.join(', ')}`;
  }

  // Phase 2: Re-type-check in a fresh environment.
  // This catches type mismatches, wrong de Bruijn indices, and incorrect
  // universe levels that the AST walk cannot detect.
  try {
    const freshEnv = createTCEnv({ definitions, options: { mode: 'check' } });
    const resultEnv = inferType(freshEnv.withValue(term));

    // Solve any constraints generated during inference
    const solvedEnv = resultEnv.solveMetasAndConstraints({ liftMetasToFullContext: false });

    // Check that no unsolved metas were generated (zonked terms should be fully explicit)
    const unsolvedIds: string[] = [];
    for (const [id, m] of solvedEnv.metaVars) {
      if (!m.solution && !m.isHole) unsolvedIds.push(id);
    }
    if (unsolvedIds.length > 0) {
      return `Zonk recheck failed for ${label}: re-type-check generated ${unsolvedIds.length} unsolved meta(s): ${unsolvedIds.join(', ')}`;
    }
  } catch (e) {
    const msg = e instanceof TCEnvError ? e.fullMessage
      : e instanceof Error ? e.message
        : String(e);
    return `Zonk recheck (re-type-check) failed for ${label}: ${msg}`;
  }
  return undefined;
}

// ============================================================================
// Main Compile Function
// ============================================================================

// ============================================================================
// Full compilation
// ============================================================================

/**
 * Compile TT source code to elaborated kernel terms.
 *
 * Pipeline:
 * 1. Parse the source file
 * 2. For each block, for each definition...
 * 3. If it is an inductive type def: elaborate & check signature, add name+sig to context,
 *    elab+check each constructor, add all constructors to context, check sizing/positivity
 * 4. If it is a term: elaborate & check signature with meta solving, for each clause
 *    elaborate LHS, unify, elaborate RHS under LHS context, check RHS, then run
 *    totality and recursion checkers, add to context if no errors
 *
 * @param source - The full source code
 * @returns CompileResult with elaborated declarations
 */
export function compileTTFromText(source: string, options?: CompileOptions): CompileResult {
  // Reset counters for fresh compilation
  resetWildcardCounter();
  resetWithCounter();

  // Parse @assumeK directive from source (overrides options)
  const sourceAssumeK = parseAssumeKDirective(source);
  // Default to true to match Lean's behavior (K enabled by default)
  const assumeK = sourceAssumeK ?? options?.assumeK ?? true;

  if (sourceAssumeK !== undefined) {
  }

  // 1. Parse the source file (parser skips directive lines)
  const parseResult = parseTTSource(source);

  return compileParsedBlocks(parseResult, {
    assumeK,
    elaborateTacticBlock,
    recheckZonkedTerm,
    options,
  });
}
// ============================================================================
// Incremental compilation
// ============================================================================


/**
 * Incrementally compile TT source, reusing cached results for unchanged blocks.
 *
 * Algorithm:
 * 1. Parse the source, compare block texts with cache to find changed blocks
 * 2. Compute the transitive recheck set via dependency DAG
 * 3. Walk blocks in order: replay cached contributions or recompile
 * 4. Return CompileResult (same shape as compileTTFromText)
 *
 * The cache is mutated in-place for efficiency (designed for useRef).
 */
export function compileIncrementalTT(
  source: string,
  cache: IncrementalCache,
  options?: CompileOptions
): CompileResult {
  const reusableResult = reuseLastIncrementalResult(source, cache);
  if (reusableResult) {
    return reusableResult;
  }

  // Reset counters for fresh compilation
  resetWildcardCounter();
  resetWithCounter();

  const sourceAssumeK = parseAssumeKDirective(source);
  const assumeK = sourceAssumeK ?? options?.assumeK ?? true;

  // 1. Parse the source
  const parseResult = parseTTSource(source);

  return compileParsedBlocksIncrementally(parseResult, cache, {
    assumeK,
    elaborateTacticBlock,
    recheckZonkedTerm,
    options,
  });
}

// ============================================================================
// Helper Functions for Absurdity Checking
// ============================================================================
