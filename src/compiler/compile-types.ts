import type { ParseError, ParsedDeclaration } from '../parser/parser';
import type { TacticInfoTree } from '../tactics/info-tree';
import type { ElabMap, SourceMap } from '../types/source-position';
import type { NamedArgMap } from './elab';
import type { TTKTerm } from './kernel';
import type { TTerm } from './surface';
import type { DefinitionsMap, TCEnvError } from './term';
import type { TotalityResult } from './totality';
import type { TypeInfoMap } from './type-info';

/**
 * A single parsed block - either declarations, a comment, or an error.
 */
export type ParsedBlock =
  | { kind: 'declarations'; declarations: ParsedDeclaration[]; sourceMaps: SourceMap[]; sourceLines: string[]; startLine: number; posOffset: number }
  | { kind: 'comment'; sourceLines: string[]; startLine: number; posOffset: number }
  | { kind: 'error'; errors: ParseError[]; sourceLines: string[]; startLine: number; posOffset: number };

/**
 * Result of parsing source text.
 */
export interface ParseResult {
  blocks: ParsedBlock[];
  totalErrors: number;
}

/**
 * A single elaborated declaration (TT -> TTK).
 */
export interface ElabDeclaration {
  name: string | undefined;
  kind: 'inductive' | 'term';
  surfaceType?: TTerm;
  surfaceValue?: TTerm;
  surfaceConstructors?: Array<{ name: string; type: TTerm }>;
  kernelType?: TTKTerm;
  kernelValue?: TTKTerm;
  kernelConstructors?: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }>;
  elabMap?: ElabMap;
  sourceMap?: SourceMap;
  elabError?: string;
  elabErrorPath?: string;
  isPostulate?: boolean;
  syntax?: string;
  constructorSyntax?: Array<{ name: string; syntax: string }>;
  withScrutineeCount?: number;
  newScrutineeCount?: number;
  withScrutineeExprs?: TTerm[];
}

/**
 * Result of compiling a single declaration.
 */
export interface CompiledDeclaration {
  name: string | undefined;
  kind: 'inductive' | 'term';
  surfaceType?: TTerm;
  surfaceValue?: TTerm;
  surfaceConstructors?: Array<{ name: string; type: TTerm }>;
  isRecord?: boolean;
  surfaceParams?: Array<{ name: string; type: TTerm }>;
  surfaceFields?: Array<{ name: string; type: TTerm }>;
  surfaceExtendsExprs?: TTerm[];
  kernelType?: TTKTerm;
  kernelValue?: TTKTerm;
  kernelConstructors?: Array<{ name: string; type: TTKTerm; namedArgMap?: NamedArgMap }>;
  namedArgMap?: NamedArgMap;
  indexPositions?: number[];
  prettyType?: string;
  prettyValue?: string;
  prettyConstructors?: Array<{ name: string; prettyType: string }>;
  prettyProjections?: Array<{ name: string; prettyType: string }>;
  checkSuccess: boolean;
  checkErrors: TCEnvError[];
  totalityResult?: TotalityResult;
  elabMap?: ElabMap;
  sourceMap?: SourceMap;
  elabErrorPath?: string;
  isWithAuxiliary?: boolean;
  withScrutineeCount?: number;
  newScrutineeCount?: number;
  withScrutineeExprs?: TTerm[];
  withClauseErrors?: TCEnvError[];
  withClauseElabMap?: ElabMap;
  typeInfoMap?: TypeInfoMap;
  tacticInfoTree?: TacticInfoTree;
  tacticTrace?: import('../tactics/tactic-session').TacticStepTrace[];
  proofTree?: import('../proof-tree/proof-tree').ProofNode;
  syntax?: string;
  constructorSyntax?: Array<{ name: string; syntax: string }>;
}

/**
 * Name resolution error with source range for squiggly display.
 */
export interface NameResolutionErrorWithRange {
  message: string;
  symbolName: string;
  path?: string;
  declarationIndex?: number;
}

/**
 * Result of compiling a block of source code.
 */
export interface CompiledBlock {
  blockIndex: number;
  sourceLines: string[];
  startLine: number;
  codeStartLine: number;
  parseSuccess: boolean;
  parseErrors: ParseError[];
  nameResolutionSuccess: boolean;
  nameResolutionErrors: NameResolutionErrorWithRange[];
  declarations: CompiledDeclaration[];
  isComment: boolean;
}

/**
 * Full result of compiling source text.
 */
export interface CompileResult {
  success: boolean;
  blocks: CompiledBlock[];
  totalParseErrors: number;
  totalNameErrors: number;
  totalCheckErrors: number;
  definitions: DefinitionsMap;
}

export interface ProcessDeclarationResult {
  success: boolean;
  compiled: CompiledDeclaration;
  newDefinitions: DefinitionsMap;
  errorCount: number;
}

export interface CompileOptions {
  /** After zonking, re-check zonked terms in a fresh TCEnv with no metas. */
  recheckZonkedTerms?: boolean;

  /**
   * Assume axiom K (Uniqueness of Identity Proofs).
   *
   * When true, pattern matching on indexed families (like Equal) is unrestricted.
   * When false, the deletion rule is enforced: indices must be definitionally equal.
   */
  assumeK?: boolean;
}
