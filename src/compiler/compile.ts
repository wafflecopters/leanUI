/**
 * Fresh TT Compiler - A clean implementation of the compilation pipeline
 *
 * This module provides a simple interface for compiling TT source code
 * to elaborated kernel terms (TTK).
 */

import { groupByIndentation } from '../parser/indentation-grouper';
import { ParsedDeclaration, ParseError } from '../parser/parser';
import { elabToKernelWithMap, elabPatternToKernel, elabPatternToKernelWithMap, buildConstructorParamNames, setConstructorParamNames, resetWildcardCounter, extractConstructorParamNames, setCurrentTermParamNames, extractNamedArgMap, extractArgNamedArgInfos, countParameters, reorderPatterns, hasNamedPatterns, applyVarPermutation, fixRhsForConstructorPatterns, fixRhsForVariablePatterns, ConstructorParamNames, NamedArgMap, NamedArgElabError, elabToKernel } from './elab';
import { TTKTerm, TTKContext, TTKClause, TTKPattern, prettyPrint as prettyPrintTTK, prettyPrintFormatted, prettyPrintPattern, prettyPrintPatternList, mkType } from './kernel';
import { TTerm, TPattern, TClause, mkULitTT, mkSortTT, mkUOmegaTT } from './surface';
import { validateDeclarations, emptySymbolContext, SymbolContext } from '../types/name-resolution';
import { resolvePatternsInDeclarations } from '../parser/pattern-resolution';
import { arraySeg, fieldSeg, appendPath, ElabMap, IndexPath, SourceMap, serializeIndexPath, deserializeIndexPath } from '../types/source-position'
import { checkType, inferType } from './checker';
import { addDefinition, addDefinitionInTCEnv, countPiBinders, createDefinitionsMap, createNamedArgInfoLookup, createNamedArgLookup, createTCEnv, DefinitionsMap, extractPiSpine, InductiveDefinition, MatchPartIndex, registerIntImpl, registerNatImpl, registerNatOp, registerOfNat, registerOfRat, registerRatImpl, registerRatOp, setDefinitionValueInTCEnv, TCEnv, TCEnvError, TermDefinition, TermDefinitionPartIndex, validateTermNameNotDefined } from './term';
import { checkInductiveDeclaration } from './inductive';
import { checkMatchClause, arePatternsAbsurd } from './patterns';
import { checkTotality, TotalityResult, CaseTree } from './totality';
import { checkStructuralRecursion } from './recursion';
import { desugarWithClauses, resetWithCounter } from './with-desugar';
import { subst } from './subst';
import { BlockContributions, IncrementalCache, extractBlockDepInfo, computeRecheckSet } from './incremental';
import { whnf, countPiBindersWhnf } from './whnf';
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
import { TacticSession } from '../tactics/tactic-session';
import { extractGoalStates, engineToProofState } from '../tactics/proof-state';
import {
  createCompiledDeclaration,
  createElabErrorResult,
} from './compile-declaration-result';
import {
  adjustSourceMapToAbsolute,
  computeCodeStartLine,
} from './compile-source-utils';
import { parseTTSource } from './compile-parse';
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
import {
  addRecordCtorTypeElabMappings,
  buildRecordTypeFromParams,
  buildSurfaceConstructorType,
  buildSurfaceRecordType,
  extractZonkedFieldTypes,
} from './compile-record-utils';
import { processRecordDeclaration } from './compile-record-processing';
import { processInductiveDeclaration } from './compile-inductive-processing';
import { checkTermValue, tryCaseSplitsInSearchOfAbsurdity } from './compile-term-value';
import { resolveWithScrutineeTypes } from './compile-with-scrutinee-resolution';
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
// Parse Result Types
// ============================================================================

/**
 * A single parsed block - either declarations, a comment, or an error
 */
export type ParsedBlock =
  | { kind: 'declarations'; declarations: ParsedDeclaration[]; sourceMaps: SourceMap[]; sourceLines: string[]; startLine: number; posOffset: number }
  | { kind: 'comment'; sourceLines: string[]; startLine: number; posOffset: number }
  | { kind: 'error'; errors: ParseError[]; sourceLines: string[]; startLine: number; posOffset: number };

/**
 * Result of parsing source text
 */
export interface ParseResult {
  blocks: ParsedBlock[];
  totalErrors: number;
}

// ============================================================================
// Elaboration Result Types
// ============================================================================

/**
 * A single elaborated declaration (TT -> TTK)
 */
export interface ElabDeclaration {
  name: string | undefined;
  kind: 'inductive' | 'term';
  // Surface (parsed) terms - used for syntax highlighting
  surfaceType?: TTerm;
  surfaceValue?: TTerm;
  surfaceConstructors?: Array<{ name: string; type: TTerm }>;
  // Elaborated kernel terms
  kernelType?: TTKTerm;
  kernelValue?: TTKTerm;
  kernelConstructors?: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }>;
  /** Maps kernel paths to surface paths (for error mapping) */
  elabMap?: ElabMap;
  /** Maps surface paths to source ranges (for error mapping) */
  sourceMap?: SourceMap;
  /** Error that occurred during elaboration (e.g., named argument errors) */
  elabError?: string;
  /** Serialized surface path where elaboration error occurred */
  elabErrorPath?: string;
  /** Postulate: type-only declaration with no value (axiom) */
  isPostulate?: boolean;
  /** @syntax annotation pattern string for structured math editor */
  syntax?: string;
  /** @syntax annotations on constructors */
  constructorSyntax?: Array<{ name: string; syntax: string }>;
  /** For with-clause auxiliaries: metadata needed for scrutinee type resolution */
  withScrutineeCount?: number;
  newScrutineeCount?: number; // For nested withs: how many scrutinees are NEW (vs inherited from parent)
  withScrutineeExprs?: TTerm[];
}

/**
 * A single elaborated block
 */
export type ElabBlock =
  | { kind: 'declarations'; declarations: ElabDeclaration[]; sourceLines: string[]; startLine: number }
  | { kind: 'comment'; sourceLines: string[]; startLine: number }
  | { kind: 'error'; errors: ParseError[]; sourceLines: string[]; startLine: number };

/**
 * Result of elaborating parsed source
 */
export interface ElabResult {
  blocks: ElabBlock[];
}

// ============================================================================
// Compile Result Types
// ============================================================================

/**
 * Result of compiling a single declaration
 */
export interface CompiledDeclaration {
  name: string | undefined;
  kind: 'inductive' | 'term';

  // Surface (parsed) terms - used for syntax highlighting
  surfaceType?: TTerm;
  surfaceValue?: TTerm;
  surfaceConstructors?: Array<{ name: string; type: TTerm }>;

  // Record-specific surface info for syntax highlighting
  isRecord?: boolean;
  surfaceParams?: Array<{ name: string; type: TTerm }>;
  surfaceFields?: Array<{ name: string; type: TTerm }>;
  surfaceExtendsExprs?: TTerm[];

  // Elaborated kernel terms
  kernelType?: TTKTerm;
  kernelValue?: TTKTerm;
  kernelConstructors?: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }>;

  // For term declarations: map from parameter names to positions
  namedArgMap?: NamedArgMap;

  // For inductive types: positions that are indices (not parameters)
  indexPositions?: number[];

  // Pretty-printed versions for display
  prettyType?: string;
  prettyValue?: string;
  prettyConstructors?: Array<{ name: string; prettyType: string }>;

  // Record-specific: generated projection signatures
  prettyProjections?: Array<{ name: string; prettyType: string }>;

  // Type checking results
  checkSuccess: boolean;
  checkErrors: TCEnvError[];

  // Totality checking results (for pattern matching terms)
  totalityResult?: TotalityResult;

  // Source mapping for error locations
  elabMap?: ElabMap;
  sourceMap?: SourceMap;

  // Elaboration error source path (for locating errors in source)
  elabErrorPath?: string;

  // Whether this declaration is a with-clause auxiliary
  isWithAuxiliary?: boolean;

  // For with-clause auxiliaries: metadata needed for scrutinee type resolution
  withScrutineeCount?: number;
  newScrutineeCount?: number; // For nested withs: how many scrutinees are NEW (vs inherited)
  withScrutineeExprs?: TTerm[];

  // Errors promoted from failed with-clause auxiliaries (displayed on the main declaration)
  withClauseErrors?: TCEnvError[];

  // ElabMap from failed auxiliaries, for mapping withClauseErrors to source ranges
  withClauseElabMap?: ElabMap;

  // Type info map for type-at-cursor feature
  typeInfoMap?: TypeInfoMap;

  // Tactic InfoTree for goal-at-cursor feature
  tacticInfoTree?: TacticInfoTree;

  // Tactic trace: engine state after each tactic step (for proof tree rendering)
  tacticTrace?: import('../tactics/tactic-session').TacticStepTrace[];

  // Proof tree built from parsed tactic commands (for proof tree rendering)
  proofTree?: import('../proof-tree/proof-tree').ProofNode;

  // @syntax annotation pattern string for structured math editor
  syntax?: string;
  // @syntax annotations on constructors
  constructorSyntax?: Array<{ name: string; syntax: string }>;
}

/**
 * Name resolution error with source range for squiggly display
 */
export interface NameResolutionErrorWithRange {
  message: string;
  symbolName: string;
  /** Serialized IndexPath for looking up source range */
  path?: string;
  /** Index of the declaration this error belongs to (for sourceMap lookup) */
  declarationIndex?: number;
}

/**
 * Result of compiling a block of source code
 */
export interface CompiledBlock {
  blockIndex: number;
  sourceLines: string[];
  startLine: number;
  /** Line number of the first actual code line (skipping comments and @syntax directives).
   *  Use this for error fallback positions instead of startLine. */
  codeStartLine: number;

  // Parsing
  parseSuccess: boolean;
  parseErrors: ParseError[];

  // Name resolution
  nameResolutionSuccess: boolean;
  nameResolutionErrors: NameResolutionErrorWithRange[];

  // Elaborated declarations
  declarations: CompiledDeclaration[];

  // Block metadata
  isComment: boolean;
}

/**
 * Full result of compiling source text
 */
export interface CompileResult {
  success: boolean;
  blocks: CompiledBlock[];
  totalParseErrors: number;
  totalNameErrors: number;
  totalCheckErrors: number;
  definitions: DefinitionsMap;  // For debugging/testing
}

// ============================================================================
// SourceMap Adjustment Helper
// ============================================================================



export { parseTTSource };

// ============================================================================
// Elaboration Function
// ============================================================================

/**
 * Options for elaboration phases
 */
export interface ElabOptions {
  /** Whether to elaborate term values (default: true). Set to false for phase 1. */
  elabValues?: boolean;
}

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
 * Elaborate parsed TT to kernel terms (TTK).
 *
 * Pipeline:
 * 1. Name resolution (validate all identifiers are defined)
 * 2. Pattern resolution (resolve PCtor vs PVar in patterns)
 * 3. Elaborate TT -> TTK
 *
 * @param parseResult - Result from parseTTSource
 * @param _initialContext - Optional initial typing context (for imports/prelude)
 * @param options - Elaboration options (e.g., whether to elaborate values)
 * @returns ElabResult with elaborated blocks
 */
export function elabTT(parseResult: ParseResult, _initialContext: TTKContext = [], options: ElabOptions = {}): ElabResult {
  const { elabValues = true } = options;
  const elabBlocks: ElabBlock[] = [];

  // Collect all declarations from all blocks for resolution
  let allDeclarations: ParsedDeclaration[] = [];
  for (const block of parseResult.blocks) {
    if (block.kind === 'declarations') {
      allDeclarations = [...allDeclarations, ...block.declarations];
    }
  }

  // Phase 1: Name resolution
  let symbolContext: SymbolContext = emptySymbolContext();
  for (const decl of allDeclarations) {
    const result = validateDeclarations([decl], symbolContext);
    if (result.success) {
      symbolContext = result.value;
    }
    // Note: We could collect resolution errors here and convert blocks to error blocks
    // For now, we continue and let type checking catch unresolved names
  }

  // Phase 2: Pattern resolution
  allDeclarations = resolvePatternsInDeclarations(allDeclarations, symbolContext);

  // Build a map from declaration name to resolved declaration
  const resolvedDeclMap = new Map<string, ParsedDeclaration>();
  for (const decl of allDeclarations) {
    if (decl.name) {
      resolvedDeclMap.set(decl.name, decl);
    }
  }

  for (const block of parseResult.blocks) {
    // Pass through comment blocks
    if (block.kind === 'comment') {
      elabBlocks.push({
        kind: 'comment',
        sourceLines: block.sourceLines,
        startLine: block.startLine
      });
      continue;
    }

    // Pass through error blocks
    if (block.kind === 'error') {
      elabBlocks.push({
        kind: 'error',
        errors: block.errors,
        sourceLines: block.sourceLines,
        startLine: block.startLine
      });
      continue;
    }

    // Elaborate declaration blocks
    const elabDeclarations: ElabDeclaration[] = [];

    for (let declIndex = 0; declIndex < block.declarations.length; declIndex++) {
      const origDecl = block.declarations[declIndex];

      // Notation declarations are parser directives — skip elaboration
      if (origDecl.kind === 'notation') continue;

      // Adjust sourceMap to file-absolute positions
      const sourceMap = adjustSourceMapToAbsolute(block.sourceMaps[declIndex], block.startLine, block.posOffset);
      // Use resolved declaration if available, otherwise fall back to original
      const decl = (origDecl.name && resolvedDeclMap.get(origDecl.name)) || origDecl;
      const elabMap: ElabMap = new Map();

      let kernelType: TTKTerm | undefined;
      let kernelValue: TTKTerm | undefined;
      let kernelConstructors: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }> | undefined;

      try {
        // Elaborate type
        if (decl.type) {
          const typePath: IndexPath = [{ kind: 'field', name: 'type' }];
          kernelType = elabToKernelWithMap(decl.type, elabMap, typePath, typePath);
        }

        // Elaborate value (only if elabValues is true)
        if (elabValues && decl.value) {
          // Check if value is a TacticBlock - skip elaboration here, will be handled during type-checking
          if (decl.value.tag === 'TacticBlock') {
            // TacticBlock will be elaborated during type-checking when we have definitions
            kernelValue = undefined;
          } else {
            const valuePath: IndexPath = [{ kind: 'field', name: 'value' }];
            // Extract namedArgMap and totalArity from type for pattern validation and reordering
            const namedArgMap = decl.type ? extractNamedArgMap(decl.type) : undefined;
            const totalArity = decl.type ? countParameters(decl.type) : undefined;
            // For with-auxiliary functions and functions that call them, defer elaboration to type-checking
            // phase when we have definitions. This allows the elaborator to look up namedArgMaps.
            // With-auxiliaries are marked with withScrutineeCount, and functions calling with-auxiliaries
            // have names ending with the original function's name (main function references auxiliary).
            const isWithRelated = decl.withScrutineeCount !== undefined ||
                                  (decl.name && decl.name.includes('-with-'));
            if (isWithRelated) {
              kernelValue = undefined;
            } else {
              kernelValue = elabToKernelWithMap(decl.value, elabMap, valuePath, valuePath, namedArgMap, undefined, totalArity);
            }
          }
        }

        // Elaborate constructors
        if (decl.constructors) {
          // Extract the inductive type's named arg map and arity so constructor types
          // can reference the inductive type with named arguments
          const inductiveNamedArgMap = decl.type ? extractNamedArgMap(decl.type) : undefined;
          const inductiveTotalArity = decl.type ? countParameters(decl.type) : undefined;

          // Create a lookup that includes this inductive type's named arg info
          // This is needed because the inductive type isn't registered in definitions yet
          const inductiveArgNamedArgInfos = decl.type ? extractArgNamedArgInfos(decl.type) : undefined;
          const ctorAppLookup = decl.name && inductiveNamedArgMap && inductiveNamedArgMap.size > 0
            ? (name: string) => name === decl.name ? { namedArgMap: inductiveNamedArgMap, totalArity: inductiveTotalArity, argNamedArgInfos: inductiveArgNamedArgInfos?.size ? inductiveArgNamedArgInfos : undefined } as import('./term').NamedArgInfo : undefined
            : undefined;

          kernelConstructors = decl.constructors.map((ctor, ctorIndex) => {
            const ctorTypePath: IndexPath = [
              { kind: 'field', name: 'constructors' },
              { kind: 'array', index: ctorIndex },
              { kind: 'field', name: 'type' }
            ];
            // Extract namedArgMap from the constructor's surface type
            const ctorNamedArgMap = extractNamedArgMap(ctor.type);
            return {
              name: ctor.name,
              type: elabToKernelWithMap(ctor.type, elabMap, ctorTypePath, ctorTypePath, undefined, ctorAppLookup),
              namedArgMap: ctorNamedArgMap.size > 0 ? ctorNamedArgMap : undefined,
            };
          });
        }

        // Collect @syntax annotations from constructors
        const constructorSyntax = decl.constructors
          ?.filter(c => c.syntax !== undefined)
          .map(c => ({ name: c.name, syntax: c.syntax! }));

        elabDeclarations.push({
          name: decl.name,
          kind: decl.kind === 'inductive' ? 'inductive' : 'term',
          // Surface terms for syntax highlighting
          surfaceType: decl.type,
          surfaceValue: decl.value,
          surfaceConstructors: decl.constructors,
          // Kernel terms for type checking
          kernelType,
          kernelValue,
          kernelConstructors,
          isPostulate: decl.isPostulate,
          elabMap,
          sourceMap,
          syntax: decl.syntax,
          ...(constructorSyntax && constructorSyntax.length > 0 ? { constructorSyntax } : {}),
        });
      } catch (e) {
        // Elaboration error - record the error for later reporting
        const errorMessage = e instanceof Error ? e.message : String(e);
        // Extract surfacePath if this is a NamedArgElabError
        const elabErrorPath = e instanceof NamedArgElabError && e.surfacePath
          ? serializeIndexPath(e.surfacePath)
          : undefined;
        const constructorSyntaxErr = decl.constructors
          ?.filter(c => c.syntax !== undefined)
          .map(c => ({ name: c.name, syntax: c.syntax! }));

        elabDeclarations.push({
          name: decl.name,
          kind: decl.kind === 'inductive' ? 'inductive' : 'term',
          surfaceType: decl.type,
          surfaceValue: decl.value,
          surfaceConstructors: decl.constructors,
          elabMap,
          sourceMap,
          elabError: errorMessage,
          elabErrorPath,
          syntax: decl.syntax,
          ...(constructorSyntaxErr && constructorSyntaxErr.length > 0 ? { constructorSyntax: constructorSyntaxErr } : {}),
        });
      }
    }

    elabBlocks.push({
      kind: 'declarations',
      declarations: elabDeclarations,
      sourceLines: block.sourceLines,
      startLine: block.startLine
    });
  }

  return { blocks: elabBlocks };
}

/**
 * Collect constructor param names from checked inductive declarations.
 * This should be called after phase 1 type checking.
 */
function collectConstructorParamNames(compiledBlocks: CompiledBlock[]): ConstructorParamNames {
  const result: ConstructorParamNames = new Map();

  for (const block of compiledBlocks) {
    for (const decl of block.declarations) {
      if (decl.kind === 'inductive' && decl.checkSuccess && decl.kernelConstructors) {
        const ctorParamNames = buildConstructorParamNames(decl.kernelConstructors);
        for (const [ctorName, paramInfo] of ctorParamNames) {
          result.set(ctorName, paramInfo);
        }
      }
    }
  }

  return result;
}

// ============================================================================
// Compile Options
// ============================================================================

export interface CompileOptions {
  /** After zonking, re-check zonked terms in a fresh TCEnv with no metas. */
  recheckZonkedTerms?: boolean;

  /**
   * Assume axiom K (Uniqueness of Identity Proofs).
   *
   * When true, pattern matching on indexed families (like Equal) is unrestricted.
   * When false (default), the deletion rule is enforced: indices must be definitionally equal.
   *
   * Without K, proofs like UIP become unprovable, making the system compatible with
   * HoTT and Cubical Type Theory.
   *
   * Can be overridden per-file with @assumeK directive.
   *
   * Default: false (no K axiom)
   */
  assumeK?: boolean;
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

/**
 * Check if a term contains a reference to the given name (Const node).
 * Used to detect self-references in simple (non-pattern-matching) definitions.
 */
function containsSelfReference(term: TTKTerm, name: string): boolean {
  switch (term.tag) {
    case 'Const': return term.name === name;
    case 'App': return containsSelfReference(term.fn, name) || containsSelfReference(term.arg, name);
    case 'Binder': return containsSelfReference(term.domain, name) || containsSelfReference(term.body, name);
    case 'Sort': return containsSelfReference(term.level, name);
    case 'Annot': return containsSelfReference(term.term, name) || containsSelfReference(term.type, name);
    case 'Match': return term.clauses.some(c => containsSelfReference(c.rhs, name));
    default: return false;
  }
}

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
// Type Checking Functions
// ============================================================================

/**
 * Result of checking a single declaration
 */
interface CheckDeclarationResult {
  compiled: CompiledDeclaration;
  newDefinitions: DefinitionsMap;
  errorCount: number;
}

/**
 * Check a single declaration and return the compiled result with updated context.
 */
function checkDeclaration(
  decl: ElabDeclaration,
  definitions: DefinitionsMap,
  assumeK?: boolean,
): CheckDeclarationResult {
  let checkSuccess = true;
  const checkErrors: TCEnvError[] = [];
  const warnings: TCEnvError[] = [];
  let newDefinitions = definitions;
  let errorCount = 0;
  let indexPositions: number[] | undefined;
  let totalityResult: TotalityResult | undefined;
  let checkedValue: TTKTerm | undefined;
  let zonkedConstructors: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }> | undefined;
  const typeInfoMap: TypeInfoMap = new Map();
  let tacticInfoTree: TacticInfoTree | undefined;

  // Check for elaboration errors first (e.g., named argument errors)
  if (decl.elabError) {
    checkSuccess = false;
    // Create TCEnv with the error path so the error points to the correct source location
    const errorPath = decl.elabErrorPath ? deserializeIndexPath(decl.elabErrorPath) : [];
    const env = createTCEnv({ definitions, indexPath: errorPath, options: { mode: 'check', assumeK } });
    const error = TCEnvError.create(decl.elabError, env);
    checkErrors.push(error);
    errorCount = 1;
  } else if (decl.kind === 'inductive') {
    const result = checkInductiveTypeDeclaration(decl, definitions, typeInfoMap);
    if (result.success) {
      newDefinitions = result.definitions;
      indexPositions = result.indexPositions;
      zonkedConstructors = result.zonkedConstructors;
    } else {
      checkSuccess = false;
      checkErrors.push(...result.errors);
      errorCount = result.errors.length;
    }
  } else if (decl.kind === 'term') {
    const result = checkTermDeclaration(decl, definitions, { typeInfoCollector: typeInfoMap, warningsCollector: warnings, assumeK });
    if (result.success) {
      newDefinitions = result.definitions;
      totalityResult = result.totalityResult;
      checkedValue = result.checkedValue;
      tacticInfoTree = result.tacticInfoTree;
    } else {
      checkSuccess = false;
      checkErrors.push(...result.errors);
      errorCount = result.errors.length;
      // Still capture totalityResult even on failure (for UI visualization)
      totalityResult = result.totalityResult;
    }
    // Add warnings to checkErrors (warnings don't fail the check)
    checkErrors.push(...warnings);
  } else {
    checkSuccess = false;
    const error = TCEnvError.create('Declaration is not an inductive or term', createTCEnv({ definitions, options: { mode: 'check', assumeK } }));
    checkErrors.push(error);
    errorCount = 1;
  }

  // Build compiled declaration with pretty-printed versions
  // Use zonkedConstructors (with solved metas) if available, otherwise fall back to elaborated kernelConstructors
  const effectiveConstructors = zonkedConstructors ?? decl.kernelConstructors;
  const compiled: CompiledDeclaration = {
    name: decl.name,
    kind: decl.kind,
    // Surface terms (for syntax highlighting)
    surfaceType: decl.surfaceType,
    surfaceValue: decl.surfaceValue,
    surfaceConstructors: decl.surfaceConstructors,
    // Kernel terms
    kernelType: decl.kernelType,
    kernelValue: checkedValue ?? decl.kernelValue,
    kernelConstructors: effectiveConstructors,
    indexPositions,
    prettyType: decl.kernelType ? prettyPrintTTK(decl.kernelType) : undefined,
    // Use checkedValue (with solutions) if available, otherwise fall back to elaborated kernelValue
    // Use formatted pretty print for better readability of match/let expressions
    // Pass namedArgLookup to show implicit args with their labels
    prettyValue: (checkedValue ?? decl.kernelValue) ? prettyPrintFormatted(
      checkedValue ?? decl.kernelValue!,
      [],
      undefined,
      { namedArgLookup: createNamedArgLookup(newDefinitions) }
    ) : undefined,
    prettyConstructors: effectiveConstructors?.map(c => ({
      name: c.name,
      prettyType: prettyPrintTTK(c.type)
    })),
    checkSuccess,
    checkErrors,
    totalityResult,
    elabMap: decl.elabMap,
    sourceMap: decl.sourceMap,
    elabErrorPath: decl.elabErrorPath,
    withScrutineeCount: decl.withScrutineeCount,
    newScrutineeCount: decl.newScrutineeCount,
    withScrutineeExprs: decl.withScrutineeExprs,
    typeInfoMap: typeInfoMap.size > 0 ? typeInfoMap : undefined,
    tacticInfoTree: tacticInfoTree,
    // Build tactic trace for proof tree rendering (avoids re-running tactics in UI)
    // tacticTrace is computed in createCompiledDeclaration (the standard path).
    // This path (checkDeclaration) is for the older compilation flow.
    tacticTrace: (() => {
      const sv = decl.surfaceValue as any;
      if (!checkSuccess || !decl.kernelType || !sv || sv.tag !== 'TacticBlock') return undefined;
      try {
        const session = TacticSession.create(decl.kernelType, newDefinitions);
        const final = session.applyCommands(sv.tactics);
        return final.trace.length > 0 ? [...final.trace] : undefined;
      } catch {
        return undefined;
      }
    })(),
    syntax: decl.syntax,
    constructorSyntax: decl.constructorSyntax,
  };

  return { compiled, newDefinitions, errorCount };
}

function checkInductiveTypeDeclaration(
  decl: ElabDeclaration,
  definitions: DefinitionsMap,
  typeInfoCollector?: TypeInfoMap,
): { success: false, errors: TCEnvError[] } | { success: true, definitions: DefinitionsMap, indexPositions: number[], zonkedConstructors: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }> } {
  if (decl.kind !== 'inductive') {
    return failCheck('Declaration is not an inductive type', createTCEnv({ definitions, options: { mode: 'check' } }))
  }

  if (!decl.kernelType) {
    return failCheck('Inductive type declaration is ill-formed', createTCEnv({ definitions, options: { mode: 'check' } }))
  }
  if (!decl.kernelConstructors) {
    return failCheck('Inductive type declaration is ill-formed', createTCEnv({ definitions, options: { mode: 'check' } }))
  }

  // Extract namedArgMap from the surface type for the inductive type itself
  const inductiveNamedArgMap = decl.surfaceType ? extractNamedArgMap(decl.surfaceType) : undefined;

  const result = checkInductiveDeclaration(
    decl.name || 'anonymous',
    decl.kernelType,
    decl.kernelConstructors,
    definitions,
    inductiveNamedArgMap && inductiveNamedArgMap.size > 0 ? inductiveNamedArgMap : undefined,
    undefined,  // recordInfo
    typeInfoCollector,
  );
  if (!result.success) {
    return result
  } else {
    return {
      success: true,
      definitions: result.newDefinitions,
      indexPositions: result.indexPositions,
      zonkedConstructors: result.zonkedConstructors,
    }
  }
}

/**
 * Remap an auxiliary with-function's elabMap to map its kernel clause paths
 * to the original with-clause surface paths in the block sourceMap.
 *
 * The auxiliary has clauses[0..N] which correspond to withClauses[0..N]
 * in some main clause. The sourceMap records paths like:
 *   value.clauses[mainIdx].withClauses[i].patterns[j]
 *   value.clauses[mainIdx].withClauses[i].rhs
 *
 * We need elabMap entries so the reverse lookup (surface→kernel) works:
 *   kernel: value.clauses[i].rhs  →  surface: value.clauses[mainIdx].withClauses[i].rhs
 */
function remapWithClauseElabMap(
  compiled: CompiledDeclaration,
  sourceMap: SourceMap,
  withScrutineeCount: number,
  newScrutineeCount: number,
): void {
  if (!compiled.elabMap) return;

  // Determine the number of function patterns (before with-patterns) in each aux clause.
  // The kernel clauses have: [funcPat0, funcPat1, ..., withPat0, withPat1, ...]
  // withScrutineeCount tells us how many with-patterns there are at the end.
  let numFunctionPatterns = 0;
  if (compiled.kernelValue?.tag === 'Match' && compiled.kernelValue.clauses.length > 0) {
    const totalPatterns = compiled.kernelValue.clauses[0].patterns.length;
    numFunctionPatterns = totalPatterns - withScrutineeCount;
  } else if (compiled.surfaceValue?.tag === 'Match' && compiled.surfaceValue.clauses.length > 0) {
    // Fallback to surface value when kernel value is unavailable (e.g., elaboration failed)
    const totalPatterns = compiled.surfaceValue.clauses[0].patterns.length;
    numFunctionPatterns = totalPatterns - withScrutineeCount;
  }

  // Detect nested Match structure: when the auxiliary has a single clause whose
  // RHS is itself a Match, the with-branches are inside that nested Match
  // (e.g., value.clauses[0].rhs is a Match with sub-clauses for each with-branch).
  let hasNestedMatch = false;
  const surfaceMatch = compiled.surfaceValue?.tag === 'Match' ? compiled.surfaceValue : null;
  if (surfaceMatch && surfaceMatch.clauses.length === 1) {
    const rhs = surfaceMatch.clauses[0].rhs;
    if (rhs.tag === 'Match') {
      hasNestedMatch = true;
    }
  }

  // Find with-clause entries in the sourceMap for this auxiliary
  // Pattern: match paths that contain .withClauses[M].*
  // This includes both direct and nested with-clauses:
  // - value.clauses[N].withClauses[M].*
  // - value.clauses[N].withClauses[M].rhs.withClauses[K].*
  const withClausePattern = /^value\.clauses\[(\d+)\]\.withClauses\[(\d+)\](.*)/;

  const remapPatternSuffix = (rawSuffix: string, functionPatternCount: number): string => {
    const patternMatch = rawSuffix.match(/^\.patterns\[(\d+)\](.*)/);
    if (!patternMatch) return rawSuffix;

    const withPatIdx = parseInt(patternMatch[1]);
    const patSuffix = patternMatch[2];
    return `.patterns[${functionPatternCount + withPatIdx}]${patSuffix}`;
  };

  for (const [path] of sourceMap) {
    // Check if this path contains any withClauses segment
    if (!path.includes('.withClauses[')) continue;

    // Find the LAST occurrence of .withClauses[N] in the path
    // This handles nested with-clauses where we want to map the innermost level
    const lastWithMatch = path.match(/^(.*\.withClauses\[)(\d+)\](.*)/);
    if (!lastWithMatch) continue;

    // For nested with-clauses, find ALL withClauses segments
    const allWithMatches = path.match(/\.withClauses\[(\d+)\]/g);
    if (!allWithMatches) continue;

    // If there's only one withClauses segment, use the original logic
    if (allWithMatches.length === 1) {
      const match = path.match(withClausePattern);
      if (!match) continue;

      const withIdx = parseInt(match[2]);
      const rawSuffix = match[3]; // e.g., '.patterns[0]', '.rhs', '.rhs.fn'

      // Offset pattern indices: with-pattern j → kernel pattern (numFunctionPatterns + j)
      const suffix = remapPatternSuffix(rawSuffix, numFunctionPatterns);

      const kernelPath = `value.clauses[${withIdx}]${suffix}`;
      compiled.elabMap.set(kernelPath, path);

    } else {
      // Paths with multiple .withClauses[...] segments belong to a nested auxiliary.
      // The current auxiliary should only claim them when it already carries
      // inherited scrutinees from a parent with-clause.
      if (newScrutineeCount >= withScrutineeCount) continue;

      // For nested with-clauses (e.g., value.clauses[0].withClauses[1].rhs.withClauses[2].*),
      // extract the LAST withClauses[N] index and map it to the auxiliary's kernel clauses.
      const lastWithIndex = path.lastIndexOf('.withClauses[');
      const remainder = path.substring(lastWithIndex);
      const remainderMatch = remainder.match(/^\.withClauses\[(\d+)\](.*)/);
      if (!remainderMatch) continue;

      const withIdx = parseInt(remainderMatch[1]);
      const rawSuffix = remainderMatch[2];

      // Offset pattern indices for nested with-clauses
      const suffix = remapPatternSuffix(rawSuffix, numFunctionPatterns + (withScrutineeCount - newScrutineeCount));

      const kernelPath = `value.clauses[${withIdx}]${suffix}`;
      compiled.elabMap.set(kernelPath, path);

    }
  }

  // Map scrutinee paths from auxiliary's RHS to main function's with-clause scrutinee paths
  // The auxiliary's RHS contains the call to the nested auxiliary (or final result),
  // and the last arguments are the scrutinee expressions.
  // We need to map: value.clauses[N].rhs.arg.* → value.clauses[M].withClauses[N].rhs.scrutinee.*
  for (const [path] of sourceMap) {
    // Find scrutinee entries in the main function's sourceMap
    const scrutineeMatch = path.match(/^value\.clauses\[(\d+)\]\.withClauses\[(\d+)\]\.rhs\.scrutinee(.*)$/);
    if (scrutineeMatch) {
      const withIdx = parseInt(scrutineeMatch[2]);
      const suffix = scrutineeMatch[3];

      // The auxiliary's scrutinee is the last argument in the RHS call
      // Map auxiliary kernel path value.clauses[withIdx].rhs.arg* to surface scrutinee path
      const kernelPath = `value.clauses[${withIdx}].rhs.arg${suffix}`;
      compiled.elabMap.set(kernelPath, path);
    }
  }

  // For nested Match: map value.clauses[0].rhs (the whole nested Match)
  // to the parent with-clause entry rather than a specific branch.
  // This ensures errors about the entire Match point to the with-clause line,
  // not to one arbitrary branch.
  if (hasNestedMatch) {
    const parentWithPattern = /^value\.clauses\[(\d+)\]\.withClauses\[0\]/;
    for (const [path] of sourceMap) {
      const m = path.match(parentWithPattern);
      if (m) {
        const clauseIdx = m[1];
        const parentEntry = `value.clauses[${clauseIdx}]`;
        if (sourceMap.has(parentEntry)) {
          compiled.elabMap.set('value.clauses[0].rhs', parentEntry);
          break;
        }
      }
    }
  }
}

/**
 * Remap scrutinee paths from the main declaration's elabMap so type info
 * is accessible for the scrutinee expression in a with-clause.
 *
 * The sourceMap has: value.clauses[N].scrutinee, value.clauses[N].scrutinee.fn, etc.
 * These need to map into the main declaration's kernel paths.
 */
function remapWithScrutineeInMainElabMap(
  compiled: CompiledDeclaration,
  sourceMap: SourceMap,
): void {
  if (!compiled.elabMap) return;

  // Find scrutinee entries in the sourceMap
  // Pattern: paths containing .scrutinee (direct or nested in with-clauses)
  // - value.clauses[N].scrutinee*
  // - value.clauses[N].withClauses[M].rhs.scrutinee*
  const scrutineePattern = /^value\.clauses\[(\d+)\]\.scrutinee/;
  const nestedScrutineePattern = /\.scrutinee($|\.)/;

  for (const [path] of sourceMap) {
    // Check if this is a direct scrutinee path (top-level with-clause)
    const directMatch = path.match(scrutineePattern);
    if (directMatch) {
      // The scrutinee in the main function is desugared into the RHS
      // (a call to the auxiliary). Map scrutinee paths to the RHS path
      // so type info can be found.
      const clauseIdx = parseInt(directMatch[1]);
      const suffix = path.substring(`value.clauses[${clauseIdx}].scrutinee`.length);
      // The scrutinee expression appears in the RHS of the main clause
      // as arguments to the auxiliary function call.
      // Map it to the corresponding RHS sub-path.
      const kernelRhsBase = `value.clauses[${clauseIdx}].rhs`;
      // For the full scrutinee, map to RHS.arg (last argument to aux call)
      // For scrutinee.fn, map to RHS.arg.fn, etc.
      if (suffix === '' || suffix === '.fn' || suffix === '.arg') {
        const kernelPath = suffix === '' ? `${kernelRhsBase}.arg` : `${kernelRhsBase}.arg${suffix}`;
        compiled.elabMap.set(kernelPath, path);
      }
    } else if (path.includes('.withClauses[') && nestedScrutineePattern.test(path)) {
      // Handle nested with-clause scrutinees
      // Pattern: value.clauses[N].withClauses[M].rhs.scrutinee*
      // The scrutinee in a nested with-clause doesn't need remapping because it's
      // already stored in the typeInfoMap under its surface path by the auxiliary's
      // type checking. We just need to ensure the path is accessible.
      // Actually, for nested with-clauses, the scrutinee is part of the auxiliary
      // function's RHS, and the auxiliary's typeInfoMap already has entries for it.
      // The mergeAuxTypeInfoIntoMain function will copy those entries.
      // So we don't need to do anything special here - just continue.
      continue;
    }
  }
}

/**
 * Merge an auxiliary with-clause declaration's typeInfoMap and elabMap into the
 * main declaration so that type-at-cursor works for with-clause patterns and RHS.
 *
 * The auxiliary's elabMap (after remapWithClauseElabMap) maps auxiliary kernel paths
 * to the main declaration's surface paths (e.g., value.clauses[1].withClauses[0].rhs.fn).
 * We store each auxiliary typeInfoMap entry under its surface path so that
 * resolveTypeInfo's direct surface-path lookup finds them.
 */
function mergeAuxTypeInfoIntoMain(
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

  // Build reverse map: kernel path → surface path (from aux elabMap)
  const auxReverse = new Map<string, string>();
  for (const [kernelPath, surfacePath] of auxCompiled.elabMap) {
    auxReverse.set(kernelPath, surfacePath);
  }

  // Merge typeInfoMap entries: store under surface path for direct lookup
  for (const [kernelPath, entry] of auxCompiled.typeInfoMap) {
    const surfacePath = auxReverse.get(kernelPath);
    if (surfacePath) {
      // Store under the surface path so resolveTypeInfo finds it directly
      mainCompiled.typeInfoMap.set(surfacePath, {
        ...entry,
        kernelPath: surfacePath,
      });
    } else {
      // Walk up kernel path to find a mapped ancestor, append suffix
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

  // Note: we intentionally do NOT merge the auxiliary's elabMap entries into the
  // main's elabMap. The auxiliary's kernel paths (e.g., value.clauses[1].rhs.fn)
  // conflict with the main's own entries at the same paths. Instead, the typeInfoMap
  // entries stored under surface paths are found via direct surface-path lookup.
}

function failCheck(message: string, env: TCEnv<unknown>): { success: false, errors: TCEnvError[] } {
  return {
    success: false,
    errors: [TCEnvError.create(message, env)],
  }
}

/**
 * Convert any remaining unsolved Meta nodes in a term to Hole nodes.
 * Used after zonking the elaborated type from signature checking: the elaborated type
 * includes implicit argument insertions (Metas from the type checker), and after zonking,
 * solved Metas are replaced with their solutions. Any remaining Metas are unsolved —
 * converting them to Holes allows the pattern matcher's hole-filling code to handle them
 * (e.g., with-clause placeholder Holes like `_scrut0_type` that were converted to Metas
 * during type checking).
 */
function unsolvedMetasToHoles(term: TTKTerm): TTKTerm {
  switch (term.tag) {
    case 'Meta':
      return { tag: 'Hole', id: term.id };
    case 'App':
      return { tag: 'App', fn: unsolvedMetasToHoles(term.fn), arg: unsolvedMetasToHoles(term.arg) };
    case 'Binder': {
      const bk = term.binderKind.tag === 'BLet'
        ? { tag: 'BLet' as const, defVal: unsolvedMetasToHoles(term.binderKind.defVal) }
        : term.binderKind;
      return { tag: 'Binder', name: term.name, binderKind: bk, domain: unsolvedMetasToHoles(term.domain), body: unsolvedMetasToHoles(term.body) };
    }
    case 'Sort': {
      const level = unsolvedMetasToHoles(term.level);
      return level === term.level ? term : { tag: 'Sort', level };
    }
    case 'Annot':
      return { tag: 'Annot', term: unsolvedMetasToHoles(term.term), type: unsolvedMetasToHoles(term.type) };
    case 'Match':
      return { tag: 'Match', scrutinee: unsolvedMetasToHoles(term.scrutinee), clauses: term.clauses.map(c => ({ ...c, rhs: unsolvedMetasToHoles(c.rhs) })) };
    default:
      // Var, Const, Hole, ULevel, ULit, UOmega — no Metas inside
      return term;
  }
}

function checkTermDeclaration(
  decl: ElabDeclaration,
  definitions: DefinitionsMap,
  options?: { allowUnsolvedSigMetas?: boolean; skipTotality?: boolean; withScrutineeCount?: number; newScrutineeCount?: number; typeInfoCollector?: TypeInfoMap; warningsCollector?: TCEnvError[]; assumeK?: boolean },
): { success: false, errors: TCEnvError[], totalityResult?: TotalityResult } | { success: true, definitions: DefinitionsMap, checkedValue: TTKTerm, zonkedType: TTKTerm, totalityResult?: TotalityResult, tacticInfoTree?: TacticInfoTree } {

  if (!decl.name) {
    return failCheck('Term declaration is ill-formed (no name)', createTCEnv({ definitions, options: { mode: 'check', assumeK: options?.assumeK } }))
  }

  let env = createTCEnv({ definitions, options: { mode: 'check', allowDuplicatePiNames: options?.allowUnsolvedSigMetas, assumeK: options?.assumeK }, typeInfoCollector: options?.typeInfoCollector, warningsCollector: options?.warningsCollector })

  if (decl.kind !== 'term') {
    return failCheck('Declaration is not a term', env)
  }

  if (!decl.kernelType) {
    return failCheck('Term declaration is ill-formed', env)
  }

  try {
    // Create a placeholder kernel value - actual clause elaboration happens in checkTermValue
    // following the flow: for each clause, elaborate LHS, unify, then elaborate RHS
    const placeholderValue: TTKTerm = {
      tag: 'Match',
      scrutinee: { tag: 'Hole', id: '_scrutinee' },
      clauses: []
    };

    let termEnv = env.withValue<TermDefinition>({
      name: decl.name,
      type: decl.kernelType,
      value: placeholderValue,
    });

    // Check for duplicate names
    validateTermNameNotDefined(termEnv);

    const sigResult = inferType(termEnv.inTermType());
    // Solve meta constraints before checking for unsolved metas
    const solvedSigResult = sigResult.solveMetasAndConstraints({ liftMetasToFullContext: false });
    const unsolvedSigMetas = Array.from(solvedSigResult.metaVars.values()).filter(m => !m.solution && !m.isHole);
    if (unsolvedSigMetas.length > 0 && !options?.allowUnsolvedSigMetas) {
      return {
        success: false, errors: [
          TCEnvError.create('Checking the signature produced unsolved metas.', env)
        ]
      }
    }

    // Extract named arg info from type for use in definition and pattern elaboration
    const namedArgMap = decl.surfaceType ? extractNamedArgMap(decl.surfaceType) : undefined;
    const argNamedArgInfos = decl.surfaceType ? extractArgNamedArgInfos(decl.surfaceType) : undefined;
    const totalArity = decl.surfaceType ? countParameters(decl.surfaceType) : undefined;

    // Zonk the kernel type to substitute any solved metas (e.g., implicit params inferred from arguments).
    // Use the elaborated term from signature checking if available, because it includes implicit argument
    // insertions for constructors used as arguments in the type (e.g., bare `refl` in `Equal p refl`
    // becomes `refl A x` with its implicit args filled). The raw kernelType retains bare Const nodes
    // that the type checker later wraps with implicit applications — but those wrappings aren't
    // reflected back into the kernel type. After zonking, any remaining unsolved Metas (e.g., with-clause
    // placeholder Holes like `_scrut0_type` that became Metas during checking) are converted back to
    // Holes so the pattern matcher's hole-filling code can handle them.
    const sigElaboratedType = sigResult.elaboratedTerm ?? decl.kernelType;
    const zonkedKernelType = unsolvedMetasToHoles(solvedSigResult.zonkTerm(sigElaboratedType));

    // Add to context for subsequent declarations, including namedArgMap for lookup
    if (decl.name) {
      termEnv = addDefinitionInTCEnv(termEnv, decl.name, zonkedKernelType, namedArgMap, argNamedArgInfos?.size ? argNamedArgInfos : undefined);
    }

    // Handle postulates: type signature with no value (declared with `postulate` keyword)
    // The name is added to definitions (above) so subsequent declarations can reference it,
    // but no value is checked. The postulate is opaque — it cannot be reduced.
    if (decl.isPostulate) {
      return {
        success: true,
        definitions: termEnv.definitions,
        checkedValue: { tag: 'Hole', id: '_postulate' },
        zonkedType: zonkedKernelType,
      };
    }

    // Handle #absurd clauses from surface value
    // These are filtered out during elaboration, so we validate them here
    const absurdClauseErrors: TCEnvError[] = [];
    const annotatedAbsurdClauses: number[] = [];

    if (decl.surfaceValue?.tag === 'Match') {
      for (let i = 0; i < decl.surfaceValue.clauses.length; i++) {
        const clause = decl.surfaceValue.clauses[i];
        if (clause.rhs.tag === 'AbsurdMarker') {
          // Normalize the return type (after all Pi binders) to handle definitions like Not
          // that expand to function types (e.g., Not A = A -> Void).
          // We can't just call whnf on the whole type because whnf doesn't reduce under binders.
          // Instead, we extract the return type and normalize it.
          const piSpine = extractPiSpine(zonkedKernelType);
          const normalizedReturnType = whnf(piSpine.body, { definitions: termEnv.definitions, fuel: 100 });

          // Reconstruct the full type with normalized return type
          let normalizedType = normalizedReturnType;
          for (let i = piSpine.binders.length - 1; i >= 0; i--) {
            const binder = piSpine.binders[i];
            normalizedType = {
              tag: 'Binder',
              name: binder.name,
              binderKind: { tag: 'BPi' },
              domain: binder.type,
              body: normalizedType,
            };
          }

          // Count parameters from the normalized type for correct arity
          const normalizedArity = countPiBinders(normalizedType);

          // First validate pattern structure - check for positional patterns in implicit positions
          // Use the normalized arity to account for type aliases like Not
          if (namedArgMap && namedArgMap.size > 0) {
            const reorderResult = reorderPatterns(clause.patterns, namedArgMap, clause.namedPatterns, normalizedArity);
            if ('error' in reorderResult && reorderResult.error !== undefined) {
              absurdClauseErrors.push(TCEnvError.create(reorderResult.error, termEnv));
              continue; // Skip absurdity check if pattern structure is invalid
            }
          }

          // Elaborate the patterns to TTKPattern for validation
          const kernelPatterns = clause.patterns.map(p => elabPatternToKernel(p));
          const patternsEnv = termEnv.withValue(kernelPatterns);

          // First try basic absurdity check
          let isAbsurd = arePatternsAbsurd(decl.name, patternsEnv, normalizedType);

          // If basic check passes (not absurd), try Agda-style recursive splitting
          // This handles cases like Fin Zero where the type is uninhabited
          if (!isAbsurd) {
            isAbsurd = tryCaseSplitsInSearchOfAbsurdity(
              decl.name,
              kernelPatterns,
              normalizedType,
              termEnv.definitions,
              termEnv
            );
          }

          if (isAbsurd) {
            // Valid #absurd annotation - track for totality display
            annotatedAbsurdClauses.push(i);
          } else {
            // Patterns are NOT absurd but #absurd was used - error
            absurdClauseErrors.push(TCEnvError.create(
              `#absurd used but case is not absurd: patterns can be inhabited`,
              termEnv
            ));
          }
        }
      }
    }

    if (absurdClauseErrors.length > 0) {
      return { success: false, errors: absurdClauseErrors };
    }

    // Handle non-Match values (simple definitions like `test = True`)
    // These don't involve pattern matching, so we elaborate and check directly
    if (decl.surfaceValue && decl.surfaceValue.tag !== 'Match') {
      const valuePath: IndexPath = [{ kind: 'field', name: 'value' }];
      const appNamedArgLookup = createNamedArgInfoLookup(termEnv.definitions);

      // Special handling for TacticBlock - elaborate by executing tactics
      let kernelValue: TTKTerm;
      let tacticInfoTree: TacticInfoTree | undefined;
      if (decl.surfaceValue.tag === 'TacticBlock') {
        try {
          const tacticResult = elaborateTacticBlock(
            decl.surfaceValue,
            zonkedKernelType,
            termEnv.definitions,
            decl.elabMap ?? new Map(),
            decl.sourceMap ?? new Map(),
            [] // Empty context for top-level definitions
          );
          kernelValue = tacticResult.term;
          tacticInfoTree = tacticResult.infoTree;
        } catch (e) {
          // If error already has proper location info (TCEnvError), re-throw it
          // This preserves the specific tactic indexPath set by elaborateTacticBlock
          if (e instanceof TCEnvError) {
            throw e;
          }
          // Otherwise convert generic errors to TCEnvErrors
          const errorMsg = e instanceof Error ? e.message : String(e);
          throw TCEnvError.create(errorMsg, termEnv);
        }
      } else {
        kernelValue = elabToKernelWithMap(
          decl.surfaceValue,
          decl.elabMap ?? new Map(),
          valuePath,
          valuePath,
          namedArgMap,
          appNamedArgLookup
        );
      }

      // Tactic-produced terms are already validated step-by-step by the tactic engine
      // (ExactTactic uses checkType, ApplyTactic uses inferType+unify, etc.).
      // The outer checkType is redundant and fails for Match terms produced by
      // cases/induction tactics, since the type checker doesn't handle Match inference.
      // Skip re-checking and trust the tactic engine's validation.
      if (decl.surfaceValue.tag === 'TacticBlock') {
        const resultEnv = setDefinitionValueInTCEnv(termEnv, decl.name, kernelValue);
        return { success: true, definitions: resultEnv.definitions, checkedValue: kernelValue, zonkedType: zonkedKernelType, tacticInfoTree: tacticInfoTree };
      }

      try {
        const valueEnv = termEnv.withValue(kernelValue);
        const result = checkType(valueEnv, zonkedKernelType);

        // Solve meta constraints before checking for unsolved metas
        let solvedResult: typeof result;
        try {
          solvedResult = result.solveMetasAndConstraints({ liftMetasToFullContext: false });
        } catch (e) {
          // Convert plain Errors (e.g. from meta constraint solving) to TCEnvErrors
          // so they carry the value-level indexPath for accurate error location.
          if (e instanceof Error && !(e instanceof TCEnvError)) {
            throw TCEnvError.create(e.message, result);
          }
          throw e;
        }
        // Check for UNSOLVED metas in the value (solved metas have a 'solution' property)
        // Exclude hole metas — those are intentionally unsolved (user wrote ?name)
        const unsolvedMetas = Array.from(solvedResult.metaVars.values()).filter(m => !m.solution && !m.isHole);
        if (unsolvedMetas.length > 0) {
          return {
            success: false, errors: [
              TCEnvError.create('Checking the value produced unsolved metas.', termEnv)
            ]
          };
        }
        // Zonk the value to substitute solved metas with their solutions
        const zonkedValue = solvedResult.zonkTerm(solvedResult.value);

        // Check for self-reference in non-pattern-matching definitions.
        // A simple definition `f = expr` with `f` appearing in `expr` is always
        // non-terminating since there's no structural decrease without pattern matching.
        if (decl.name && containsSelfReference(zonkedValue, decl.name)) {
          return {
            success: false, errors: [
              TCEnvError.create(
                `Definition '${decl.name}' is non-terminating: simple definitions cannot be recursive. Use pattern matching for recursive definitions.`,
                termEnv
              )
            ]
          };
        }

        const resultEnv = setDefinitionValueInTCEnv(termEnv, decl.name, zonkedValue);
        return { success: true, definitions: resultEnv.definitions, checkedValue: zonkedValue, zonkedType: zonkedKernelType };
      } catch (e) {
        if (e instanceof TCEnvError) {
          return { success: false, errors: [e] };
        }
        return { success: false, errors: [TCEnvError.create(String(e), termEnv)] };
      }
    }

    // Get surface clauses for incremental elaboration (pattern matching case)
    // IMPORTANT: Preserve original surface indices when filtering absurd clauses
    // This ensures the ElabMap correctly maps kernel clause indices to surface clause indices
    const surfaceClausesWithIndices: Array<{ clause: TClause; originalIndex: number }> =
      decl.surfaceValue?.tag === 'Match'
        ? decl.surfaceValue.clauses
            .map((clause, index) => ({ clause, originalIndex: index }))
            .filter(({ clause }) => clause.rhs.tag !== 'AbsurdMarker')
        : [];
    const surfaceClauses = surfaceClausesWithIndices.map(({ clause }) => clause);
    const surfaceClauseIndices = surfaceClausesWithIndices.map(({ originalIndex }) => originalIndex);

    // Use WHNF-aware arity so type aliases like `Not A = A -> Void` expose hidden Pi binders
    const effectiveTotalArity = totalArity !== undefined
      ? countPiBindersWhnf(zonkedKernelType, termEnv.definitions)
      : undefined;

    const result = checkTermValue(
      decl.name,
      termEnv,
      zonkedKernelType,  // Use zonked type - Holes from signature elaboration are resolved
      surfaceClauses,
      surfaceClauseIndices,
      decl.elabMap ?? new Map(),
      namedArgMap,
      effectiveTotalArity,
      annotatedAbsurdClauses,
      { skipTotality: options?.skipTotality, withScrutineeCount: options?.withScrutineeCount, newScrutineeCount: options?.newScrutineeCount },
      argNamedArgInfos
    );
    if (!result.success) {
      return { success: false, errors: result.errors, totalityResult: result.totalityResult }
    }

    const resultEnv = setDefinitionValueInTCEnv(termEnv, decl.name, result.checkedValue);
    return { success: true, definitions: resultEnv.definitions, checkedValue: result.checkedValue, zonkedType: zonkedKernelType, totalityResult: result.totalityResult }
  } catch (e) {
    if (e instanceof TCEnvError) {
      return {
        success: false,
        errors: [e],
      }
    } else {
      return {
        success: false,
        errors: [TCEnvError.create(e instanceof Error ? e.message : String(e), env)],
      }
    }
  }
}

/**
 * Result of checking a single block
 */
interface CheckBlockResult {
  compiled: CompiledBlock;
  newDefinitions: DefinitionsMap;
  errorCount: number;
}

/**
 * Check a single block and return the compiled result with updated context.
 */
function checkBlock(
  block: ElabBlock,
  blockIndex: number,
  definitions: DefinitionsMap,
  assumeK?: boolean,
): CheckBlockResult {
  // Handle comment blocks
  if (block.kind === 'comment') {
    return {
      compiled: {
        blockIndex,
        sourceLines: block.sourceLines,
        startLine: block.startLine,
        codeStartLine: computeCodeStartLine(block.sourceLines, block.startLine),
        parseSuccess: true,
        parseErrors: [],
        nameResolutionSuccess: true,
        nameResolutionErrors: [],
        declarations: [],
        isComment: true
      },
      newDefinitions: definitions,
      errorCount: 0
    };
  }

  // Handle error blocks
  if (block.kind === 'error') {
    return {
      compiled: {
        blockIndex,
        sourceLines: block.sourceLines,
        startLine: block.startLine,
        codeStartLine: computeCodeStartLine(block.sourceLines, block.startLine),
        parseSuccess: false,
        parseErrors: block.errors,
        nameResolutionSuccess: true,
        nameResolutionErrors: [],
        declarations: [],
        isComment: false
      },
      newDefinitions: definitions,
      errorCount: 0
    };
  }

  // Handle declaration blocks - type check each declaration
  const compiledDeclarations: CompiledDeclaration[] = [];
  let currentDefinitions = definitions;
  let totalErrors = 0;

  for (const decl of block.declarations) {
    const result = checkDeclaration(decl, currentDefinitions, assumeK);
    compiledDeclarations.push(result.compiled);
    currentDefinitions = result.newDefinitions;
    totalErrors += result.errorCount;
  }

  return {
    compiled: {
      blockIndex,
      sourceLines: block.sourceLines,
      startLine: block.startLine,
      codeStartLine: computeCodeStartLine(block.sourceLines, block.startLine),
      parseSuccess: true,
      parseErrors: [],
      nameResolutionSuccess: true,
      nameResolutionErrors: [],
      declarations: compiledDeclarations,
      isComment: false
    },
    newDefinitions: currentDefinitions,
    errorCount: totalErrors
  };
}

/**
 * Result of checking all blocks
 */
interface CheckBlocksResult {
  blocks: CompiledBlock[];
  totalCheckErrors: number;
  finalDefinitions: DefinitionsMap;
}

/**
 * Options for type checking phases
 */
interface CheckOptions {
  /** Only check declarations of this kind (default: check all) */
  onlyKind?: 'inductive' | 'term';
  /** Existing compiled blocks to merge with (for phase 2) */
  existingBlocks?: CompiledBlock[];
}

/**
 * Check all elaborated blocks and return compiled blocks with type check results.
 */
function checkBlocks(
  _parseResult: ParseResult,
  elabResult: ElabResult,
  initialDefinitions: DefinitionsMap = createDefinitionsMap(),
  options: CheckOptions = {},
  assumeK?: boolean,
): CheckBlocksResult {
  const { onlyKind, existingBlocks } = options;
  const compiledBlocks: CompiledBlock[] = [];
  let currentDefinitions = initialDefinitions;
  let totalCheckErrors = 0;

  for (let blockIndex = 0; blockIndex < elabResult.blocks.length; blockIndex++) {
    const block = elabResult.blocks[blockIndex];

    // If we're filtering by kind, we need to handle it specially
    if (onlyKind && block.kind === 'declarations') {
      // Filter declarations to only include the specified kind
      const filteredDecls = block.declarations.filter(d => d.kind === onlyKind);

      if (filteredDecls.length === 0) {
        // No declarations of this kind - use existing block or create placeholder
        if (existingBlocks && existingBlocks[blockIndex]) {
          compiledBlocks.push(existingBlocks[blockIndex]);
        } else {
          compiledBlocks.push({
            blockIndex,
            sourceLines: block.sourceLines,
            startLine: block.startLine,
            codeStartLine: computeCodeStartLine(block.sourceLines, block.startLine),
            parseSuccess: true,
            parseErrors: [],
            nameResolutionSuccess: true,
            nameResolutionErrors: [],
            declarations: [],
            isComment: false
          });
        }
        continue;
      }

      // Create a filtered elab block
      const filteredBlock: ElabBlock = {
        kind: 'declarations',
        declarations: filteredDecls,
        sourceLines: block.sourceLines,
        startLine: block.startLine,
      };

      const result = checkBlock(filteredBlock, blockIndex, currentDefinitions, assumeK);

      // Merge with existing blocks if provided (for phase 2, merge with phase 1 results)
      if (existingBlocks && existingBlocks[blockIndex]) {
        const existingDecls = existingBlocks[blockIndex].declarations;
        // Merge: keep existing checked declarations, add newly checked ones
        const mergedDecls: CompiledDeclaration[] = [];

        // Add existing declarations that weren't in this phase
        for (const existingDecl of existingDecls) {
          if (existingDecl.kind !== onlyKind) {
            mergedDecls.push(existingDecl);
          }
        }
        // Add newly checked declarations
        mergedDecls.push(...result.compiled.declarations);

        result.compiled.declarations = mergedDecls;
      }

      compiledBlocks.push(result.compiled);
      currentDefinitions = result.newDefinitions;
      totalCheckErrors += result.errorCount;
    } else {
      // No filtering - check all declarations
      const result = checkBlock(block, blockIndex, currentDefinitions, assumeK);
      compiledBlocks.push(result.compiled);
      currentDefinitions = result.newDefinitions;
      totalCheckErrors += result.errorCount;
    }
  }

  return {
    blocks: compiledBlocks,
    totalCheckErrors,
    finalDefinitions: currentDefinitions
  };
}

// ============================================================================
// Main Compile Function
// ============================================================================

/**
 * Result of processing a single declaration
 */
export interface ProcessDeclarationResult {
  success: boolean;
  compiled: CompiledDeclaration;
  newDefinitions: DefinitionsMap;
  errorCount: number;
}

/**
 * Process a single inductive declaration: elaborate and check.
 *
 * Following the flow:
 * 1. Elaborate & check signature. Add name+sig to context.
 * 2. Elab+Check each constructor in that extended context.
 * 3. Add all constructors to the context.
 * 4. Check sizing rules on indices and check for positive definiteness in ctors.
 *    (Return original context if any failure, along with errors)
 */
/**
 * Process a single term declaration: elaborate and check.
 *
 * Following the flow:
 * a. Elaborate, check, and solve metas in signature.
 * b. For each clause: elaborate the LHS args, unify the LHS args & constraints solve,
 *    then elaborate the RHS under the context created from LHS elab, and check RHS
 *    under refined return type (from LHS unification).
 * c. Run totality checker on checked clauses.
 * d. Run safe recursion checker on checked clauses.
 * e. Add to context if no errors.
 */
function processTermDeclaration(
  decl: ParsedDeclaration,
  sourceMap: SourceMap,
  definitions: DefinitionsMap,
  options?: { allowUnsolvedSigMetas?: boolean; skipTotality?: boolean; withScrutineeCount?: number; newScrutineeCount?: number; assumeK?: boolean },
): ProcessDeclarationResult {

  const elabMap: ElabMap = new Map();
  const typeInfoMap: TypeInfoMap = new Map();
  const warnings: TCEnvError[] = [];

  // a. Elaborate signature
  let kernelType: TTKTerm | undefined;
  if (decl.type) {
    try {
      // For auxiliary with-functions, infer scrutinee types from expressions
      // and substitute them into the type signature before elaboration
      let typeToElaborate = decl.type;
      if (decl.withScrutineeExprs && decl.withScrutineeExprs.length > 0) {
        typeToElaborate = resolveWithScrutineeTypes(
          decl.type,
          decl.withScrutineeExprs,
          definitions
        );
      }

      const typePath: IndexPath = [{ kind: 'field', name: 'type' }];
      // Pass appNamedArgLookup so named arguments in the type signature can be resolved
      const appNamedArgLookup = createNamedArgInfoLookup(definitions);
      kernelType = elabToKernelWithMap(typeToElaborate, elabMap, typePath, typePath, undefined, appNamedArgLookup);
    } catch (e) {
      return createElabErrorResult(e, decl, sourceMap, elabMap, definitions);
    }
  }

  // NOTE: We do NOT elaborate the value here. Per step (b) above, clause elaboration
  // happens incrementally in checkTermDeclaration: for each clause, we elaborate
  // LHS patterns, unify & solve, THEN elaborate RHS under the resulting context.

  // Create ElabDeclaration for checkTermDeclaration
  const elabDecl: ElabDeclaration = {
    name: decl.name,
    kind: 'term',
    surfaceType: decl.type,
    surfaceValue: decl.value,
    kernelType,
    // kernelValue is NOT set here - elaboration happens clause-by-clause in checkTermDeclaration
    isPostulate: decl.isPostulate,
    elabMap,
    sourceMap,
    syntax: decl.syntax,
    withScrutineeCount: decl.withScrutineeCount,
    newScrutineeCount: decl.newScrutineeCount,
    withScrutineeExprs: decl.withScrutineeExprs,
  };

  // Check the term declaration
  // (This handles: signature check & meta solving, clause checking with LHS/RHS,
  //  totality, recursion, and adds to context if no errors)
  const result = checkTermDeclaration(elabDecl, definitions, { ...options, typeInfoCollector: typeInfoMap, warningsCollector: warnings });
  const finalTypeInfoMap = typeInfoMap.size > 0 ? typeInfoMap : undefined;

  if (!result.success) {
    return {
      success: false,
      compiled: createCompiledDeclaration(
        decl, kernelType, undefined, undefined, elabMap, sourceMap,
        false, [...result.errors, ...warnings], definitions, result.totalityResult,
        undefined, undefined, undefined, undefined, undefined, undefined, undefined, finalTypeInfoMap,
        undefined // tacticInfoTree
      ),
      newDefinitions: definitions,
      errorCount: result.errors.length
    };
  }

  return {
    success: true,
    compiled: createCompiledDeclaration(
      decl, result.zonkedType, result.checkedValue, undefined, elabMap, sourceMap,
      true, warnings, result.definitions, result.totalityResult,
      undefined, undefined, undefined, undefined, undefined, undefined, undefined, finalTypeInfoMap,
      result.tacticInfoTree // tacticInfoTree
    ),
    newDefinitions: result.definitions,
    errorCount: 0
  };
}

// ============================================================================
// Single-block compilation (extracted for incremental reuse)
// ============================================================================

interface CompileOneBlockResult {
  compiled: CompiledBlock;
  newDefinitions: DefinitionsMap;
  newSymbolContext: SymbolContext;
  newConstructorParamNames: ConstructorParamNames;
  checkErrorCount: number;
  nameErrorCount: number;
}

/**
 * Compile a single parsed block given the accumulated state from prior blocks.
 * This is the extracted inner loop of compileTTFromText.
 */
function compileOneBlock(
  block: ParsedBlock,
  blockIndex: number,
  definitions: DefinitionsMap,
  symbolContext: SymbolContext,
  constructorParamNames: ConstructorParamNames,
  assumeK: boolean,
  options?: CompileOptions
): CompileOneBlockResult {
  let checkErrorCount = 0;
  let nameErrorCount = 0;
  // Clone constructorParamNames so we don't mutate caller's copy
  constructorParamNames = new Map(constructorParamNames);

  // Handle comment blocks
  if (block.kind === 'comment') {
    return {
      compiled: {
        blockIndex, sourceLines: block.sourceLines, startLine: block.startLine,
        codeStartLine: computeCodeStartLine(block.sourceLines, block.startLine),
        parseSuccess: true, parseErrors: [],
        nameResolutionSuccess: true, nameResolutionErrors: [],
        declarations: [], isComment: true
      },
      newDefinitions: definitions, newSymbolContext: symbolContext,
      newConstructorParamNames: constructorParamNames,
      checkErrorCount: 0, nameErrorCount: 0,
    };
  }

  // Handle parse error blocks
  if (block.kind === 'error') {
    return {
      compiled: {
        blockIndex, sourceLines: block.sourceLines, startLine: block.startLine,
        codeStartLine: computeCodeStartLine(block.sourceLines, block.startLine),
        parseSuccess: false, parseErrors: block.errors,
        nameResolutionSuccess: true, nameResolutionErrors: [],
        declarations: [], isComment: false
      },
      newDefinitions: definitions, newSymbolContext: symbolContext,
      newConstructorParamNames: constructorParamNames,
      checkErrorCount: 0, nameErrorCount: 0,
    };
  }

  // Process declarations in this block
  const compiledDecls: CompiledDeclaration[] = [];
  const blockNameErrors: NameResolutionErrorWithRange[] = [];

  for (let declIndex = 0; declIndex < block.declarations.length; declIndex++) {
    const origDecl = block.declarations[declIndex];

    // Notation declarations are parser directives — skip elaboration and type checking
    if (origDecl.kind === 'notation') continue;

    const sourceMap = adjustSourceMapToAbsolute(block.sourceMaps[declIndex], block.startLine, block.posOffset);

    // Name resolution for this declaration (using current symbol context)
    const nameResult = validateDeclarations([origDecl], symbolContext);
    if (nameResult.success) {
      symbolContext = nameResult.value;
    } else {
      for (const err of nameResult.errors) {
        blockNameErrors.push({
          message: err.message,
          symbolName: err.symbolName,
          path: serializeIndexPath(err.path),
          declarationIndex: declIndex
        });
        nameErrorCount++;
      }
      if (origDecl.name) {
        symbolContext = new Set([...symbolContext, origDecl.name]);
      }
      if (origDecl.constructors) {
        for (const ctor of origDecl.constructors) {
          symbolContext = new Set([...symbolContext, ctor.name]);
        }
      }
    }

    // Pattern resolution for this declaration (using current symbol context)
    const [resolvedDecl] = resolvePatternsInDeclarations([origDecl], symbolContext);

    // Save original surface value before desugaring (for semantic highlighting)
    const originalSurfaceValue = resolvedDecl.value;

    // Desugar with-clauses (may produce auxiliary declarations)
    const desugaredDecls = desugarWithClauses([resolvedDecl]);
    const mainDecl = desugaredDecls[0];
    const auxiliaryDecls = desugaredDecls.slice(1);

    if (auxiliaryDecls.length > 0 && originalSurfaceValue) {
      mainDecl.originalSurfaceValue = originalSurfaceValue;
    }

    // Register all auxiliary declarations in symbol context
    for (const auxDecl of auxiliaryDecls) {
      const auxNameResult = validateDeclarations([auxDecl], symbolContext);
      if (auxNameResult.success) {
        symbolContext = auxNameResult.value;
      }
    }

    // Pre-register the main function's type signature if there are auxiliaries
    if (auxiliaryDecls.length > 0 && mainDecl.kind === 'def' && mainDecl.type && mainDecl.name) {
      try {
        const typePath: IndexPath = [{ kind: 'field', name: 'type' }];
        const appNamedArgLookup = createNamedArgInfoLookup(definitions);
        const elabMap: ElabMap = new Map();
        const mainKernelType = elabToKernelWithMap(mainDecl.type, elabMap, typePath, typePath, undefined, appNamedArgLookup);
        const mainNamedArgMap = extractNamedArgMap(mainDecl.type);
        const mainArgNamedArgInfos = extractArgNamedArgInfos(mainDecl.type);
        definitions = addDefinition(definitions, mainDecl.name, mainKernelType, undefined, mainNamedArgMap.size > 0 ? mainNamedArgMap : undefined, mainArgNamedArgInfos.size > 0 ? mainArgNamedArgInfos : undefined);
      } catch (_e) {
        // If type elaboration fails, continue - error will be caught later
      }
    }

    // Process auxiliary declarations FIRST
    const failedAuxNames = new Set<string>();
    const auxErrorsForMain: TCEnvError[] = [];
    const auxElabMapForMain: ElabMap = new Map();
    const compiledAuxiliaries: CompiledDeclaration[] = [];

    for (const auxDecl of auxiliaryDecls) {
      const result = processTermDeclaration(auxDecl, sourceMap, definitions, { allowUnsolvedSigMetas: true, withScrutineeCount: auxDecl.withScrutineeCount, newScrutineeCount: auxDecl.newScrutineeCount, assumeK });
      remapWithClauseElabMap(
        result.compiled,
        sourceMap,
        auxDecl.withScrutineeCount ?? 0,
        auxDecl.newScrutineeCount ?? auxDecl.withScrutineeCount ?? 0,
      );
      result.compiled.isWithAuxiliary = true;
      compiledAuxiliaries.push(result.compiled);
      compiledDecls.push(result.compiled);
      if (result.success) {
        definitions = result.newDefinitions;
      } else {
        if (auxDecl.name) failedAuxNames.add(auxDecl.name);
        const mainName = mainDecl.name ?? '';
        for (const err of result.compiled.checkErrors) {
          if (auxDecl.name && mainName && err.message.includes(auxDecl.name)) {
            auxErrorsForMain.push(TCEnvError.create(err.message.split(auxDecl.name).join(mainName), err.env));
          } else {
            auxErrorsForMain.push(err);
          }
        }
        if (result.compiled.elabMap) {
          for (const [key, value] of result.compiled.elabMap) {
            auxElabMapForMain.set(key, value);
          }
        }
      }
      checkErrorCount += result.errorCount;
    }

    // Now process the main declaration
    if (mainDecl.kind === 'inductive') {
      const result = processInductiveDeclaration(mainDecl, sourceMap, definitions);
      compiledDecls.push(result.compiled);
      if (result.success) {
        definitions = result.newDefinitions;
        if (result.compiled.kernelConstructors) {
          const newCtorParamNames = buildConstructorParamNames(result.compiled.kernelConstructors);
          for (const [ctorName, paramInfo] of newCtorParamNames) {
            constructorParamNames.set(ctorName, paramInfo);
          }
          setConstructorParamNames(constructorParamNames);
        }
        if (options?.recheckZonkedTerms && result.compiled.kernelConstructors) {
          for (const ctor of result.compiled.kernelConstructors) {
            const recheckErr = recheckZonkedTerm(ctor.type, definitions, `${mainDecl.name}.${ctor.name} constructor type`);
            if (recheckErr) {
              const errEnv = createTCEnv({ definitions, options: { mode: 'check' } });
              result.compiled.checkErrors.push(TCEnvError.create(recheckErr, errEnv));
              result.compiled.checkSuccess = false;
              checkErrorCount++;
            }
          }
        }
      }
      checkErrorCount += result.errorCount;
    } else if (mainDecl.kind === 'record') {
      const result = processRecordDeclaration(mainDecl, sourceMap, definitions);
      compiledDecls.push(result.compiled);
      if (result.success) {
        definitions = result.newDefinitions;
        if (result.compiled.kernelConstructors) {
          const newCtorParamNames = buildConstructorParamNames(result.compiled.kernelConstructors);
          for (const [ctorName, paramInfo] of newCtorParamNames) {
            constructorParamNames.set(ctorName, paramInfo);
          }
          setConstructorParamNames(constructorParamNames);
        }
        if (options?.recheckZonkedTerms && result.compiled.kernelConstructors) {
          for (const ctor of result.compiled.kernelConstructors) {
            const recheckErr = recheckZonkedTerm(ctor.type, definitions, `${mainDecl.name}.${ctor.name} constructor type`);
            if (recheckErr) {
              const errEnv = createTCEnv({ definitions, options: { mode: 'check' } });
              result.compiled.checkErrors.push(TCEnvError.create(recheckErr, errEnv));
              result.compiled.checkSuccess = false;
              checkErrorCount++;
            }
          }
        }
      }
      checkErrorCount += result.errorCount;
    } else {
      const result = processTermDeclaration(mainDecl, sourceMap, definitions, { assumeK });
      if (auxiliaryDecls.length > 0) {
        remapWithScrutineeInMainElabMap(result.compiled, sourceMap);
        for (const auxCompiled of compiledAuxiliaries) {
          mergeAuxTypeInfoIntoMain(result.compiled, auxCompiled);
        }
      }
      if (failedAuxNames.size > 0) {
        const originalCount = result.compiled.checkErrors.length;
        result.compiled.checkErrors = result.compiled.checkErrors.filter(err => {
          for (const auxName of failedAuxNames) {
            if (err.message.includes(`Type definition not found: ${auxName}`)) return false;
          }
          return true;
        });
        checkErrorCount -= (originalCount - result.compiled.checkErrors.length);
      }
      if (auxErrorsForMain.length > 0) {
        result.compiled.withClauseErrors = auxErrorsForMain;
        if (auxElabMapForMain.size > 0) {
          result.compiled.withClauseElabMap = auxElabMapForMain;
        }
      }
      compiledDecls.push(result.compiled);
      if (result.success) {
        definitions = result.newDefinitions;
        if (options?.recheckZonkedTerms && result.compiled.kernelType) {
          const recheckErr = recheckZonkedTerm(result.compiled.kernelType, definitions, `${mainDecl.name} type signature`);
          if (recheckErr) {
            const errEnv = createTCEnv({ definitions, options: { mode: 'check' } });
            result.compiled.checkErrors.push(TCEnvError.create(recheckErr, errEnv));
            result.compiled.checkSuccess = false;
            checkErrorCount++;
          }
        }
        if (options?.recheckZonkedTerms && result.compiled.kernelValue) {
          const recheckErr = recheckZonkedTerm(result.compiled.kernelValue, definitions, `${mainDecl.name} value`);
          if (recheckErr) {
            const errEnv = createTCEnv({ definitions, options: { mode: 'check' } });
            result.compiled.checkErrors.push(TCEnvError.create(recheckErr, errEnv));
            result.compiled.checkSuccess = false;
            checkErrorCount++;
          }
        }
      }
      checkErrorCount += result.errorCount;
    }
  }

  return {
    compiled: {
      blockIndex, sourceLines: block.sourceLines, startLine: block.startLine,
      codeStartLine: computeCodeStartLine(block.sourceLines, block.startLine),
      parseSuccess: true, parseErrors: [],
      nameResolutionSuccess: blockNameErrors.length === 0,
      nameResolutionErrors: blockNameErrors,
      declarations: compiledDecls, isComment: false
    },
    newDefinitions: definitions, newSymbolContext: symbolContext,
    newConstructorParamNames: constructorParamNames,
    checkErrorCount, nameErrorCount,
  };
}

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

  // 2. For each block, for each definition...
  // We build context incrementally as we process declarations
  let definitions = createDefinitionsMap();
  let constructorParamNames: ConstructorParamNames = new Map();
  let symbolContext: SymbolContext = emptySymbolContext();
  const compiledBlocks: CompiledBlock[] = [];
  let totalCheckErrors = 0;
  let totalNameErrors = 0;

  for (let blockIndex = 0; blockIndex < parseResult.blocks.length; blockIndex++) {
    const block = parseResult.blocks[blockIndex];
    const result = compileOneBlock(block, blockIndex, definitions, symbolContext, constructorParamNames, assumeK, options);
    compiledBlocks.push(result.compiled);
    definitions = result.newDefinitions;
    symbolContext = result.newSymbolContext;
    constructorParamNames = result.newConstructorParamNames;
    totalCheckErrors += result.checkErrorCount;
    totalNameErrors += result.nameErrorCount;
    // Register @impl=ROLE annotations EAGERLY (so subsequent blocks can use the
    // resulting kernel features, e.g., NatLit literals after @impl=nat declared).
    applyImplAnnotationsForBlock(result.compiled, definitions);
  }

  return {
    success: parseResult.totalErrors === 0 && totalNameErrors === 0 && totalCheckErrors === 0,
    blocks: compiledBlocks,
    totalParseErrors: parseResult.totalErrors,
    totalNameErrors,
    totalCheckErrors,
    definitions
  };
}

/**
 * Apply @impl=ROLE annotations from a single compiled block. Called eagerly
 * after each block compiles so subsequent blocks can use resulting features
 * (e.g., NatLit literals after @impl=nat is declared).
 */
function applyImplAnnotationsForBlock(block: CompiledBlock, definitions: DefinitionsMap): void {
  const implRegex = /^@impl=([a-zA-Z][a-zA-Z0-9_]*)$/;
  for (const decl of block.declarations) {
    if (!decl.syntax || !decl.name) continue;
    const trimmed = decl.syntax.trim();

    // @impl=ROLE: register inductive as a built-in role implementation
    const m = trimmed.match(implRegex);
    if (m) {
      const role = m[1];
      if (role === 'nat') {
        const err = registerNatImpl(definitions, decl.name);
        if (err) {
          console.warn(`@impl=nat verification failed for '${decl.name}': ${err}`);
        }
      } else if (role === 'int') {
        const err = registerIntImpl(definitions, decl.name);
        if (err) {
          console.warn(`@impl=int verification failed for '${decl.name}': ${err}`);
        }
      } else if (role === 'rat') {
        const err = registerRatImpl(definitions, decl.name);
        if (err) {
          console.warn(`@impl=rat verification failed for '${decl.name}': ${err}`);
        }
      }
      // Future: @impl=string, @impl=list, etc.
      continue;
    }

    // @ofNat: register this term definition as a Nat coercion
    if (trimmed === '@ofNat') {
      const err = registerOfNat(definitions, decl.name);
      if (err) {
        console.warn(`@ofNat verification failed for '${decl.name}': ${err}`);
      }
      continue;
    }

    // @ofRat: register this term definition as a Rat coercion
    if (trimmed === '@ofRat') {
      const err = registerOfRat(definitions, decl.name);
      if (err) {
        console.warn(`@ofRat verification failed for '${decl.name}': ${err}`);
      }
      continue;
    }

    // @natAdd / @natMul: register this term as a primitive nat operation
    // for WHNF fast-path computation on NatLit args.
    if (trimmed === '@natAdd') {
      const err = registerNatOp(definitions, decl.name, 'add');
      if (err) {
        console.warn(`@natAdd verification failed for '${decl.name}': ${err}`);
      }
      continue;
    }
    if (trimmed === '@natMul') {
      const err = registerNatOp(definitions, decl.name, 'mul');
      if (err) {
        console.warn(`@natMul verification failed for '${decl.name}': ${err}`);
      }
      continue;
    }

    // @ratAdd / @ratMul / @ratSub: register Rat primitive operations
    if (trimmed === '@ratAdd' || trimmed === '@ratMul' || trimmed === '@ratSub') {
      const kind = trimmed === '@ratAdd' ? 'add' : trimmed === '@ratMul' ? 'mul' : 'sub';
      const err = registerRatOp(definitions, decl.name, kind);
      if (err) {
        console.warn(`${trimmed} verification failed for '${decl.name}': ${err}`);
      }
      continue;
    }
  }
}

/**
 * Apply @impl=ROLE annotations across all blocks. Used by incremental compile
 * which doesn't drive the per-block loop with fresh registration.
 */
function applyImplAnnotations(blocks: CompiledBlock[], definitions: DefinitionsMap): void {
  for (const block of blocks) {
    applyImplAnnotationsForBlock(block, definitions);
  }
}

// ============================================================================
// Incremental compilation
// ============================================================================

/**
 * Compute what a single block contributed to the global state,
 * by diffing the state before and after compilation.
 */
function computeBlockContributions(
  beforeDefs: DefinitionsMap,
  afterDefs: DefinitionsMap,
  beforeSymbols: SymbolContext,
  afterSymbols: SymbolContext,
  beforeCtorParams: ConstructorParamNames,
  afterCtorParams: ConstructorParamNames,
): BlockContributions {
  const terms: [string, TermDefinition][] = [];
  for (const [name, def] of afterDefs.terms) {
    if (!beforeDefs.terms.has(name)) {
      terms.push([name, def]);
    }
  }

  const inductiveTypes: [string, InductiveDefinition][] = [];
  for (const [name, def] of afterDefs.inductiveTypes) {
    if (!beforeDefs.inductiveTypes.has(name)) {
      inductiveTypes.push([name, def]);
    }
  }

  const constructorMappings: [string, string][] = [];
  for (const [ctor, ind] of afterDefs.inductiveNameOfConstructor) {
    if (!beforeDefs.inductiveNameOfConstructor.has(ctor)) {
      constructorMappings.push([ctor, ind]);
    }
  }

  const symbolNames: string[] = [];
  for (const name of afterSymbols) {
    if (!beforeSymbols.has(name)) {
      symbolNames.push(name);
    }
  }

  const constructorParamEntries: [string, unknown[]][] = [];
  for (const [name, params] of afterCtorParams) {
    if (!beforeCtorParams.has(name)) {
      constructorParamEntries.push([name, params]);
    }
  }

  return { terms, inductiveTypes, constructorMappings, symbolNames, constructorParamEntries };
}

/**
 * Replay cached block contributions into the running state.
 */
function applyBlockContributions(
  definitions: DefinitionsMap,
  symbolContext: SymbolContext,
  constructorParamNames: ConstructorParamNames,
  contributions: BlockContributions,
): {
  definitions: DefinitionsMap;
  symbolContext: SymbolContext;
  constructorParamNames: ConstructorParamNames;
} {
  let newTerms = definitions.terms;
  if (contributions.terms.length > 0) {
    newTerms = new Map(newTerms);
    for (const [name, def] of contributions.terms) {
      newTerms.set(name, def);
    }
  }

  let newIndTypes = definitions.inductiveTypes;
  let newCtorMap = definitions.inductiveNameOfConstructor;
  if (contributions.inductiveTypes.length > 0) {
    newIndTypes = new Map(newIndTypes);
    for (const [name, def] of contributions.inductiveTypes) {
      newIndTypes.set(name, def);
    }
  }
  if (contributions.constructorMappings.length > 0) {
    newCtorMap = new Map(newCtorMap);
    for (const [ctor, ind] of contributions.constructorMappings) {
      newCtorMap.set(ctor, ind);
    }
  }

  definitions = {
    terms: newTerms,
    inductiveTypes: newIndTypes,
    inductiveNameOfConstructor: newCtorMap,
    natImplByCtor: definitions.natImplByCtor,
  };

  if (contributions.symbolNames.length > 0) {
    symbolContext = new Set(symbolContext);
    for (const name of contributions.symbolNames) {
      symbolContext.add(name);
    }
  }

  if (contributions.constructorParamEntries.length > 0) {
    constructorParamNames = new Map(constructorParamNames);
    for (const [name, params] of contributions.constructorParamEntries) {
      constructorParamNames.set(name, params as any);
    }
  }

  return { definitions, symbolContext, constructorParamNames };
}

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
  // 0. Fast path: check if any block content actually changed before parsing.
  //    groupByIndentation is cheap (string splitting); parsing is expensive (~62ms).
  //    Edits like inserting blank lines among blank lines shift blocks but don't
  //    change their content — skip everything in that case.
  const sourceBlocks = groupByIndentation(source);
  if (cache.lastResult && sourceBlocks.length === cache.blocks.length) {
    let allMatch = true;
    for (let i = 0; i < sourceBlocks.length; i++) {
      const sourceText = sourceBlocks[i].lines.join('\n');
      if (!cache.blocks[i] || cache.blocks[i]!.sourceText !== sourceText) {
        allMatch = false;
        break;
      }
    }
    if (allMatch) {
      return cache.lastResult;
    }
  }

  // Reset counters for fresh compilation
  resetWildcardCounter();
  resetWithCounter();

  const sourceAssumeK = parseAssumeKDirective(source);
  const assumeK = sourceAssumeK ?? options?.assumeK ?? true;

  // 1. Parse the source
  const parseResult = parseTTSource(source);

  // 2. Find changed blocks by comparing source text with cache
  const changedIndices = new Set<number>();
  for (let i = 0; i < parseResult.blocks.length; i++) {
    const block = parseResult.blocks[i];
    const sourceText = block.sourceLines.join('\n');
    const cached = cache.blocks[i];
    if (!cached || cached.sourceText !== sourceText) {
      changedIndices.add(i);
    }
  }

  // 3. Compute dependency DAG and recheck set
  const blockInfos = parseResult.blocks.map((block, i) => extractBlockDepInfo(block, i));
  const recheckSet = computeRecheckSet(blockInfos, changedIndices);

  // 4. Walk blocks: replay cached or recompile
  let definitions = createDefinitionsMap();
  let constructorParamNames: ConstructorParamNames = new Map();
  let symbolContext: SymbolContext = emptySymbolContext();
  const compiledBlocks: CompiledBlock[] = [];
  let totalCheckErrors = 0;
  let totalNameErrors = 0;

  for (let blockIndex = 0; blockIndex < parseResult.blocks.length; blockIndex++) {
    const block = parseResult.blocks[blockIndex];

    if (!recheckSet.has(blockIndex) && cache.blocks[blockIndex]) {
      // Replay cached result
      const cached = cache.blocks[blockIndex]!;
      compiledBlocks.push(cached.compiledBlock);

      const applied = applyBlockContributions(
        definitions, symbolContext, constructorParamNames,
        cached.contributions
      );
      definitions = applied.definitions;
      symbolContext = applied.symbolContext;
      constructorParamNames = applied.constructorParamNames;

      // Keep global constructor param state in sync
      setConstructorParamNames(constructorParamNames);

      totalCheckErrors += cached.checkErrorCount;
      totalNameErrors += cached.nameErrorCount;
    } else {
      // Ensure global constructor param state is current before compiling
      setConstructorParamNames(constructorParamNames);

      const beforeDefs = definitions;
      const beforeSymbols = symbolContext;
      const beforeCtorParams = constructorParamNames;

      const result = compileOneBlock(
        block, blockIndex, definitions, symbolContext,
        constructorParamNames, assumeK, options
      );

      compiledBlocks.push(result.compiled);
      definitions = result.newDefinitions;
      symbolContext = result.newSymbolContext;
      constructorParamNames = result.newConstructorParamNames;
      totalCheckErrors += result.checkErrorCount;
      totalNameErrors += result.nameErrorCount;

      // Compute and cache contributions
      const contributions = computeBlockContributions(
        beforeDefs, definitions,
        beforeSymbols, symbolContext,
        beforeCtorParams, constructorParamNames
      );

      const sourceText = block.sourceLines.join('\n');
      cache.blocks[blockIndex] = {
        sourceText,
        compiledBlock: result.compiled,
        contributions,
        checkErrorCount: result.checkErrorCount,
        nameErrorCount: result.nameErrorCount,
      };
    }
  }

  // Trim cache if source has fewer blocks now
  cache.blocks.length = parseResult.blocks.length;

  // Process @syntax @impl=ROLE annotations for kernel-level role registration.
  applyImplAnnotations(compiledBlocks, definitions);

  const result: CompileResult = {
    success: parseResult.totalErrors === 0 && totalNameErrors === 0 && totalCheckErrors === 0,
    blocks: compiledBlocks,
    totalParseErrors: parseResult.totalErrors,
    totalNameErrors,
    totalCheckErrors,
    definitions,
  };

  cache.lastResult = result;
  return result;
}

// ============================================================================
// Helper Functions for Absurdity Checking
// ============================================================================
