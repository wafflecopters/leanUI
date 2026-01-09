/**
 * Pattern Elaboration Stepper
 *
 * A step-by-step state machine for pattern matching elaboration.
 * Each call to `step()` advances the elaboration by one atomic operation,
 * making it perfect for visualization and debugging.
 *
 * This is the CANONICAL implementation of pattern elaboration.
 * The typechecker should use this for actual type checking.
 *
 * Usage:
 *   const stepper = createPatternElabStepper(clause, fnType, env);
 *   while (!stepper.isDone()) {
 *     console.log(stepper.describeState());
 *     stepper.step();
 *   }
 *   console.log(stepper.getResult());
 */

import {
  TTKTerm,
  TTKPattern,
  TTKClause,
  TTKContext,
  mkVar,
  mkApp,
  mkConst,
  mkType,
  mkPi,
  mkLambda,
  subst,
  shiftTerm,
  prettyPrint
} from './tt-kernel';

// =============================================================================
// Constructor Information (for pattern elaboration)
// =============================================================================

export interface ConstructorInfo {
  name: string;
  params: Array<{ name: string; type: TTKTerm }>;
  returnType: TTKTerm;
}

// =============================================================================
// Metavariable State
// =============================================================================

export interface MetaInfo {
  id: string;
  type: TTKTerm;
  solution: TTKTerm | null;
  createdAt: string;  // Description of when/why it was created
}

export interface MetaState {
  metas: Map<string, MetaInfo>;
  counter: number;
}

function freshMeta(state: MetaState, type: TTKTerm, reason: string, prefix = 'm'): { state: MetaState; meta: TTKTerm } {
  const id = `?${prefix}${state.counter}`;
  const newMetas = new Map(state.metas);
  newMetas.set(id, { id, type, solution: null, createdAt: reason });
  return {
    state: { metas: newMetas, counter: state.counter + 1 },
    meta: { tag: 'Hole', id, type, context: [] }
  };
}

function solveMeta(state: MetaState, id: string, solution: TTKTerm): { state: MetaState; success: boolean } {
  const meta = state.metas.get(id);
  if (!meta) return { state, success: false };
  if (meta.solution !== null) {
    // Already solved - check consistency (simplified)
    return { state, success: true };
  }
  const newMetas = new Map(state.metas);
  newMetas.set(id, { ...meta, solution });
  return { state: { ...state, metas: newMetas }, success: true };
}

function zonk(state: MetaState, term: TTKTerm): TTKTerm {
  switch (term.tag) {
    case 'Hole': {
      const meta = state.metas.get(term.id);
      if (meta?.solution) return zonk(state, meta.solution);
      return term;
    }
    case 'Var':
    case 'Sort':
      return term;
    case 'Const':
      return { ...term, type: zonk(state, term.type) };
    case 'App':
      return { tag: 'App', fn: zonk(state, term.fn), arg: zonk(state, term.arg) };
    case 'Binder': {
      const domain = zonk(state, term.domain);
      const body = zonk(state, term.body);
      let binderKind = term.binderKind;
      if (binderKind.tag === 'BLet') {
        binderKind = { tag: 'BLet', defVal: zonk(state, binderKind.defVal) };
      }
      return { tag: 'Binder', name: term.name, binderKind, domain, body };
    }
    case 'Annot':
      return { tag: 'Annot', term: zonk(state, term.term), type: zonk(state, term.type) };
    case 'Match':
      return {
        tag: 'Match',
        scrutinee: zonk(state, term.scrutinee),
        clauses: term.clauses.map(c => ({ patterns: c.patterns, rhs: zonk(state, c.rhs) }))
      };
  }
}

// =============================================================================
// Elaboration State Machine
// =============================================================================

/**
 * The different phases of elaboration
 */
export type ElabPhase =
  | { tag: 'Init' }
  | { tag: 'UnwrappingType'; piIndex: number }
  | { tag: 'ElaboratingPattern'; patternIndex: number; subPhase: PatternSubPhase }
  | { tag: 'ComputingReturnType' }
  | { tag: 'CheckingRHS' }
  | { tag: 'Done' }
  | { tag: 'Error'; message: string };

export type PatternSubPhase =
  | { tag: 'Start' }
  | { tag: 'CreatingMeta'; reason: string }
  | { tag: 'BindingVariable'; name: string }
  | { tag: 'ProcessingConstructor'; ctorName: string; step: ConstructorStep }
  | { tag: 'Finished'; term: TTKTerm };

export type ConstructorStep =
  | { tag: 'LookingUpCtor' }
  | { tag: 'CreatingParamMetas'; paramIndex: number }
  | { tag: 'ComputingReturnType' }
  | { tag: 'Unifying' }
  | { tag: 'ProcessingSubPattern'; argIndex: number }
  | { tag: 'BuildingTerm' };

/**
 * A constraint generated during elaboration
 */
export interface Constraint {
  lhs: TTKTerm;
  rhs: TTKTerm;
  reason: string;
}

/**
 * A binding introduced by a pattern
 */
export interface Binding {
  name: string;
  type: TTKTerm;
  introducedBy: string;  // Description of which pattern introduced this
}

/**
 * The complete state of the elaboration process
 */
export interface ElabState {
  // Input
  clause: TTKClause;
  fnType: TTKTerm;
  env: Map<string, ConstructorInfo>;

  // Current phase
  phase: ElabPhase;

  // Metavariable state
  metaState: MetaState;

  // Unwrapped function type
  argTypes: Array<{ name: string; type: TTKTerm }>;
  returnType: TTKTerm | null;

  // Pattern elaboration progress
  patternTerms: TTKTerm[];           // Term each pattern elaborates to
  bindings: Binding[];            // Variables bound by patterns
  currentPatternStack: TTKPattern[]; // Stack for nested pattern processing

  // Sub-pattern terms map: maps pattern path to elaborated term
  // Path format: "patternIndex" for top-level, "patternIndex.subIndex" for sub-patterns
  // e.g., for pattern 3 being (VNil _), "3" -> (VNil ?A3), "3.0" -> ?A3
  subPatternTerms: Map<string, TTKTerm>;

  // Constraints and solutions
  constraints: Constraint[];      // Unification constraints generated
  solvedConstraints: Constraint[]; // Constraints that have been solved

  // Step counter for debugging
  stepNumber: number;

  // History of steps taken (for visualization)
  history: StepRecord[];
}

export interface StepRecord {
  stepNumber: number;
  description: string;
  phase: ElabPhase;
  action: string;
  metaChanges: string[];  // Which metas were created/solved
}

// =============================================================================
// Pretty Printing
// =============================================================================

export function prettyTerm(term: TTKTerm, metaState?: MetaState): string {
  const t = metaState ? zonk(metaState, term) : term;
  switch (t.tag) {
    case 'Hole': return t.id;
    case 'Var': return `#${t.index}`;
    case 'Sort': return t.level === 0 ? 'Prop' : `Type${t.level > 1 ? t.level : ''}`;
    case 'Const': return t.name;
    case 'App': {
      const args: TTKTerm[] = [];
      let fn: TTKTerm = t;
      while (fn.tag === 'App') {
        args.unshift(fn.arg);
        fn = fn.fn;
      }
      if (args.length === 0) return prettyTerm(fn, metaState);
      return `(${prettyTerm(fn, metaState)} ${args.map(a => prettyTerm(a, metaState)).join(' ')})`;
    }
    case 'Binder': {
      const dom = prettyTerm(t.domain, metaState);
      const cod = prettyTerm(t.body, metaState);
      if (t.binderKind.tag === 'BPi') {
        if (t.name === '_') return `(${dom} → ${cod})`;
        return `(${t.name} : ${dom}) → ${cod}`;
      } else if (t.binderKind.tag === 'BLam') {
        return `λ${t.name}. ${cod}`;
      } else {
        return `let ${t.name} = ${prettyTerm(t.binderKind.defVal, metaState)} in ${cod}`;
      }
    }
    case 'Annot':
      return `(${prettyTerm(t.term, metaState)} : ${prettyTerm(t.type, metaState)})`;
    case 'Match':
      return `match ${prettyTerm(t.scrutinee, metaState)} { ... }`;
  }
}

export function prettyPattern(p: TTKPattern): string {
  switch (p.tag) {
    case 'PVar':
      return p.name === '_' || p.name.startsWith('_w') ? '_' : p.name;
    case 'PCtor':
      if (p.args.length === 0) return p.name;
      return `(${p.name} ${p.args.map(prettyPattern).join(' ')})`;
  }
}

export function prettyPhase(phase: ElabPhase): string {
  switch (phase.tag) {
    case 'Init': return 'Initializing';
    case 'UnwrappingType': return `Unwrapping Pi type (position ${phase.piIndex})`;
    case 'ElaboratingPattern': return `Elaborating pattern ${phase.patternIndex + 1}`;
    case 'ComputingReturnType': return 'Computing refined return type';
    case 'CheckingRHS': return 'Checking RHS';
    case 'Done': return 'Done!';
    case 'Error': return `Error: ${phase.message}`;
  }
}

// =============================================================================
// Substitution helpers
// =============================================================================

function substitute(term: TTKTerm, index: number, replacement: TTKTerm): TTKTerm {
  return subst(index, replacement, term);
}

function shift(term: TTKTerm, cutoff: number, amount: number): TTKTerm {
  return shiftTerm(term, amount, cutoff);
}

// =============================================================================
// Simple WHNF Reduction (for visualization)
// =============================================================================

/**
 * Performs simple WHNF reduction for known functions.
 * This is a minimal implementation for demonstration purposes.
 */
function whnf(term: TTKTerm, metaState: MetaState): TTKTerm {
  const t = zonk(metaState, term);

  switch (t.tag) {
    case 'App': {
      const fn = whnf(t.fn, metaState);

      // Check for (plus Zero n) -> n
      // Note: fn should be (plus Zero) which is (App (Const plus) Zero)
      if (fn.tag === 'App' &&
          fn.fn.tag === 'Const' && fn.fn.name === 'plus') {
        const firstArg = whnf(fn.arg, metaState);
        if (firstArg.tag === 'Const' && firstArg.name === 'Zero') {
          // (plus Zero n) -> n
          return whnf(t.arg, metaState);
        }

        // Check for (plus (Succ m) n) -> Succ (plus m n)
        if (firstArg.tag === 'App' &&
            firstArg.fn.tag === 'Const' && firstArg.fn.name === 'Succ') {
          const m = firstArg.arg;
          const n = t.arg;
          const plusConst = mkConst('plus', mkType(0)); // Type is placeholder
          const succConst = mkConst('Succ', mkType(0));
          return whnf(
            mkApp(succConst, mkApp(mkApp(plusConst, m), n)),
            metaState
          );
        }
      }

      return { ...t, fn };
    }

    default:
      return t;
  }
}

/**
 * Deep reduction - applies WHNF recursively to all subterms.
 * Used for normalization before display.
 */
function deepReduce(term: TTKTerm, metaState: MetaState): TTKTerm {
  const t = whnf(term, metaState);

  switch (t.tag) {
    case 'App': {
      return {
        tag: 'App',
        fn: deepReduce(t.fn, metaState),
        arg: deepReduce(t.arg, metaState)
      };
    }
    case 'Binder':
      return {
        tag: 'Binder',
        name: t.name,
        binderKind: t.binderKind,
        domain: deepReduce(t.domain, metaState),
        body: deepReduce(t.body, metaState)
      };
    default:
      return t;
  }
}

// =============================================================================
// Helper: check if pattern is a wildcard
// =============================================================================

function isWildcard(p: TTKPattern): boolean {
  return p.tag === 'PVar' && (p.name === '_' || p.name.startsWith('_w'));
}

// =============================================================================
// The Stepper Class
// =============================================================================

export class PatternElabStepper {
  private state: ElabState;

  constructor(clause: TTKClause, fnType: TTKTerm, env: Map<string, ConstructorInfo>) {
    this.state = {
      clause,
      fnType,
      env,
      phase: { tag: 'Init' },
      metaState: { metas: new Map(), counter: 0 },
      argTypes: [],
      returnType: null,
      patternTerms: [],
      bindings: [],
      currentPatternStack: [],
      subPatternTerms: new Map(),
      constraints: [],
      solvedConstraints: [],
      stepNumber: 0,
      history: []
    };
  }

  /** Get current state (for visualization) */
  getState(): Readonly<ElabState> {
    return this.state;
  }

  /** Check if elaboration is complete */
  isDone(): boolean {
    return this.state.phase.tag === 'Done' || this.state.phase.tag === 'Error';
  }

  /** Get a human-readable description of current state */
  describeState(): string {
    const s = this.state;
    const lines: string[] = [];

    lines.push(`\n${'='.repeat(60)}`);
    lines.push(`Step ${s.stepNumber}: ${prettyPhase(s.phase)}`);
    lines.push('='.repeat(60));

    // Show metas
    if (s.metaState.metas.size > 0) {
      lines.push('\nMetavariables:');
      for (const [id, info] of s.metaState.metas) {
        const sol = info.solution ? prettyTerm(info.solution, s.metaState) : '?';
        lines.push(`  ${id} : ${prettyTerm(info.type, s.metaState)} = ${sol}  (${info.createdAt})`);
      }
    }

    // Show pattern progress
    if (s.patternTerms.length > 0) {
      lines.push('\nPattern terms:');
      for (let i = 0; i < s.patternTerms.length; i++) {
        lines.push(`  ${i + 1}. ${prettyPattern(s.clause.patterns[i])} → ${prettyTerm(s.patternTerms[i], s.metaState)}`);
      }
    }

    // Show bindings
    if (s.bindings.length > 0) {
      lines.push('\nBindings:');
      for (let i = 0; i < s.bindings.length; i++) {
        const b = s.bindings[i];
        lines.push(`  #${i} ${b.name} : ${prettyTerm(b.type, s.metaState)}`);
      }
    }

    // Show constraints
    if (s.constraints.length > 0) {
      lines.push('\nPending constraints:');
      for (const c of s.constraints) {
        lines.push(`  ${prettyTerm(c.lhs, s.metaState)} =?= ${prettyTerm(c.rhs, s.metaState)}  (${c.reason})`);
      }
    }

    return lines.join('\n');
  }

  /** Take one step */
  step(): StepRecord {
    const record = this.doStep();
    this.state.history.push(record);
    this.state.stepNumber++;
    return record;
  }

  /** Run until done */
  runToCompletion(): StepRecord[] {
    const records: StepRecord[] = [];
    while (!this.isDone()) {
      records.push(this.step());
    }
    return records;
  }

  // =========================================================================
  // Step Implementation
  // =========================================================================

  private doStep(): StepRecord {
    const s = this.state;
    const phase = s.phase;

    switch (phase.tag) {
      case 'Init':
        return this.stepInit();

      case 'UnwrappingType':
        return this.stepUnwrapType(phase.piIndex);

      case 'ElaboratingPattern':
        return this.stepElaboratePattern(phase.patternIndex, phase.subPhase);

      case 'ComputingReturnType':
        return this.stepComputeReturnType();

      case 'CheckingRHS':
        return this.stepCheckRHS();

      case 'Done':
      case 'Error':
        return this.makeRecord('Already finished', 'none');
    }
  }

  private stepInit(): StepRecord {
    // Start unwrapping the function type
    this.state.phase = { tag: 'UnwrappingType', piIndex: 0 };
    return this.makeRecord(
      `Starting elaboration of clause with ${this.state.clause.patterns.length} patterns`,
      'Begin unwrapping function type'
    );
  }

  private stepUnwrapType(piIndex: number): StepRecord {
    const s = this.state;
    let currentType = s.fnType;

    // Skip to current position
    for (let i = 0; i < piIndex; i++) {
      if (currentType.tag === 'Binder' && currentType.binderKind.tag === 'BPi') {
        currentType = currentType.body;
      }
    }

    if (currentType.tag === 'Binder' && currentType.binderKind.tag === 'BPi' && piIndex < s.clause.patterns.length) {
      // Extract this argument type
      s.argTypes.push({ name: currentType.name, type: currentType.domain });
      s.phase = { tag: 'UnwrappingType', piIndex: piIndex + 1 };
      return this.makeRecord(
        `Unwrapped argument ${piIndex + 1}: ${currentType.name} : ${prettyTerm(currentType.domain, s.metaState)}`,
        'Extract Pi domain'
      );
    } else {
      // Done unwrapping, store return type and start pattern elaboration
      s.returnType = currentType;
      s.phase = {
        tag: 'ElaboratingPattern',
        patternIndex: 0,
        subPhase: { tag: 'Start' }
      };
      return this.makeRecord(
        `Finished unwrapping. Return type: ${prettyTerm(currentType, s.metaState)}`,
        'Begin pattern elaboration'
      );
    }
  }

  private stepElaboratePattern(patternIndex: number, subPhase: PatternSubPhase): StepRecord {
    const s = this.state;

    if (patternIndex >= s.clause.patterns.length) {
      // All patterns done, compute return type
      s.phase = { tag: 'ComputingReturnType' };
      return this.makeRecord('All patterns elaborated', 'Compute return type');
    }

    const pattern = s.clause.patterns[patternIndex];
    const argInfo = s.argTypes[patternIndex];

    // Compute expected type with substitutions
    let expectedType = argInfo.type;
    for (let j = 0; j < patternIndex; j++) {
      expectedType = substitute(expectedType, patternIndex - 1 - j, s.patternTerms[j]);
    }
    expectedType = zonk(s.metaState, expectedType);

    switch (subPhase.tag) {
      case 'Start':
        return this.stepPatternStart(patternIndex, pattern, expectedType);

      case 'CreatingMeta':
        return this.stepCreatingMeta(patternIndex, expectedType, subPhase.reason);

      case 'BindingVariable':
        return this.stepBindingVariable(patternIndex, subPhase.name, expectedType);

      case 'ProcessingConstructor':
        return this.stepProcessingConstructor(patternIndex, pattern as { tag: 'PCtor'; name: string; args: TTKPattern[] }, expectedType, subPhase);

      case 'Finished':
        // Move to next pattern
        s.phase = {
          tag: 'ElaboratingPattern',
          patternIndex: patternIndex + 1,
          subPhase: { tag: 'Start' }
        };
        return this.makeRecord(
          `Pattern ${patternIndex + 1} elaborated to ${prettyTerm(subPhase.term, s.metaState)}`,
          'Next pattern'
        );
    }
  }

  private stepPatternStart(patternIndex: number, pattern: TTKPattern, expectedType: TTKTerm): StepRecord {
    const s = this.state;

    switch (pattern.tag) {
      case 'PVar':
        if (isWildcard(pattern)) {
          s.phase = {
            tag: 'ElaboratingPattern',
            patternIndex,
            subPhase: { tag: 'CreatingMeta', reason: `wildcard at position ${patternIndex + 1}` }
          };
          return this.makeRecord(
            `Pattern ${patternIndex + 1} is wildcard _, expected type: ${prettyTerm(expectedType, s.metaState)}`,
            'Will create metavariable'
          );
        } else {
          s.phase = {
            tag: 'ElaboratingPattern',
            patternIndex,
            subPhase: { tag: 'BindingVariable', name: pattern.name }
          };
          return this.makeRecord(
            `Pattern ${patternIndex + 1} is variable ${pattern.name}, expected type: ${prettyTerm(expectedType, s.metaState)}`,
            'Will bind variable'
          );
        }

      case 'PCtor':
        s.phase = {
          tag: 'ElaboratingPattern',
          patternIndex,
          subPhase: {
            tag: 'ProcessingConstructor',
            ctorName: pattern.name,
            step: { tag: 'LookingUpCtor' }
          }
        };
        return this.makeRecord(
          `Pattern ${patternIndex + 1} is constructor ${pattern.name}, expected type: ${prettyTerm(expectedType, s.metaState)}`,
          'Will process constructor'
        );
    }
  }

  private stepCreatingMeta(patternIndex: number, expectedType: TTKTerm, reason: string): StepRecord {
    const s = this.state;
    const argName = s.argTypes[patternIndex].name;

    const { state: newMetaState, meta } = freshMeta(s.metaState, expectedType, reason, argName[0]);
    s.metaState = newMetaState;
    s.patternTerms.push(meta);

    s.phase = {
      tag: 'ElaboratingPattern',
      patternIndex,
      subPhase: { tag: 'Finished', term: meta }
    };

    const metaId = (meta as { tag: 'Hole'; id: string }).id;
    return this.makeRecord(
      `Created metavariable ${metaId} : ${prettyTerm(expectedType, s.metaState)}`,
      'Meta created',
      [metaId]
    );
  }

  private stepBindingVariable(patternIndex: number, name: string, expectedType: TTKTerm): StepRecord {
    const s = this.state;
    const index = s.bindings.length;
    const varTerm: TTKTerm = mkVar(index);

    s.bindings.push({
      name,
      type: expectedType,
      introducedBy: `pattern ${patternIndex + 1}`
    });
    s.patternTerms.push(varTerm);

    s.phase = {
      tag: 'ElaboratingPattern',
      patternIndex,
      subPhase: { tag: 'Finished', term: varTerm }
    };

    return this.makeRecord(
      `Bound variable ${name} : ${prettyTerm(expectedType, s.metaState)} at index #${index}`,
      'Variable bound'
    );
  }

  private stepProcessingConstructor(
    patternIndex: number,
    pattern: { tag: 'PCtor'; name: string; args: TTKPattern[] },
    expectedType: TTKTerm,
    subPhase: { tag: 'ProcessingConstructor'; ctorName: string; step: ConstructorStep }
  ): StepRecord {
    const s = this.state;
    const ctorInfo = s.env.get(pattern.name);

    switch (subPhase.step.tag) {
      case 'LookingUpCtor': {
        if (!ctorInfo) {
          s.phase = { tag: 'Error', message: `Unknown constructor: ${pattern.name}` };
          return this.makeRecord(`Constructor ${pattern.name} not found`, 'Error');
        }
        s.phase = {
          tag: 'ElaboratingPattern',
          patternIndex,
          subPhase: {
            tag: 'ProcessingConstructor',
            ctorName: pattern.name,
            step: { tag: 'CreatingParamMetas', paramIndex: 0 }
          }
        };
        // Store constructor info for later steps
        (s as any).currentCtorInfo = ctorInfo;
        (s as any).currentCtorMetas = [];
        return this.makeRecord(
          `Found constructor ${pattern.name} with ${ctorInfo.params.length} parameters`,
          'Lookup constructor'
        );
      }

      case 'CreatingParamMetas': {
        const paramIndex = subPhase.step.paramIndex;
        const ctorMetas: TTKTerm[] = (s as any).currentCtorMetas;

        if (paramIndex >= ctorInfo!.params.length) {
          // Done creating metas, compute return type
          s.phase = {
            tag: 'ElaboratingPattern',
            patternIndex,
            subPhase: {
              tag: 'ProcessingConstructor',
              ctorName: pattern.name,
              step: { tag: 'ComputingReturnType' }
            }
          };
          return this.makeRecord(
            `Created all ${ctorMetas.length} parameter metavariables`,
            'Prepare for unification'
          );
        }

        const param = ctorInfo!.params[paramIndex];
        let paramType = param.type;
        // Substitute earlier metas
        for (let i = 0; i < ctorMetas.length; i++) {
          paramType = substitute(paramType, ctorInfo!.params.length - 1 - i, ctorMetas[i]);
        }

        const { state: newMetaState, meta } = freshMeta(
          s.metaState,
          paramType,
          `${pattern.name} param ${param.name}`,
          param.name[0]
        );
        s.metaState = newMetaState;
        ctorMetas.push(meta);

        s.phase = {
          tag: 'ElaboratingPattern',
          patternIndex,
          subPhase: {
            tag: 'ProcessingConstructor',
            ctorName: pattern.name,
            step: { tag: 'CreatingParamMetas', paramIndex: paramIndex + 1 }
          }
        };

        const metaId = (meta as { tag: 'Hole'; id: string }).id;
        return this.makeRecord(
          `Created ${metaId} for constructor param ${param.name} : ${prettyTerm(paramType, s.metaState)}`,
          'Create param meta',
          [metaId]
        );
      }

      case 'ComputingReturnType': {
        const ctorMetas: TTKTerm[] = (s as any).currentCtorMetas;
        let ctorReturnType = ctorInfo!.returnType;
        for (let i = 0; i < ctorMetas.length; i++) {
          ctorReturnType = substitute(ctorReturnType, ctorInfo!.params.length - 1 - i, ctorMetas[i]);
        }
        (s as any).currentCtorReturnType = ctorReturnType;

        s.constraints.push({
          lhs: ctorReturnType,
          rhs: expectedType,
          reason: `${pattern.name} return type must match expected type`
        });

        s.phase = {
          tag: 'ElaboratingPattern',
          patternIndex,
          subPhase: {
            tag: 'ProcessingConstructor',
            ctorName: pattern.name,
            step: { tag: 'Unifying' }
          }
        };

        return this.makeRecord(
          `Constructor return type: ${prettyTerm(ctorReturnType, s.metaState)}. Need to unify with ${prettyTerm(expectedType, s.metaState)}`,
          'Add unification constraint'
        );
      }

      case 'Unifying': {
        // Perform the unification
        const constraint = s.constraints[s.constraints.length - 1];
        const solved = this.unify(constraint.lhs, constraint.rhs);

        if (!solved) {
          s.phase = { tag: 'Error', message: `Cannot unify ${prettyTerm(constraint.lhs, s.metaState)} with ${prettyTerm(constraint.rhs, s.metaState)}` };
          return this.makeRecord('Unification failed', 'Error');
        }

        s.constraints.pop();
        s.solvedConstraints.push(constraint);

        // Move to processing sub-patterns
        s.phase = {
          tag: 'ElaboratingPattern',
          patternIndex,
          subPhase: {
            tag: 'ProcessingConstructor',
            ctorName: pattern.name,
            step: { tag: 'ProcessingSubPattern', argIndex: 0 }
          }
        };
        (s as any).currentSubPatternIndex = 0;

        return this.makeRecord(
          `Unification successful!`,
          'Unify'
        );
      }

      case 'ProcessingSubPattern': {
        const argIndex = subPhase.step.argIndex;
        const ctorMetas: TTKTerm[] = (s as any).currentCtorMetas;

        if (argIndex >= pattern.args.length) {
          // Done with sub-patterns, build the term
          s.phase = {
            tag: 'ElaboratingPattern',
            patternIndex,
            subPhase: {
              tag: 'ProcessingConstructor',
              ctorName: pattern.name,
              step: { tag: 'BuildingTerm' }
            }
          };
          return this.makeRecord(
            `Finished processing ${argIndex} sub-patterns`,
            'Build constructor term'
          );
        }

        // For now, simplified sub-pattern handling
        // In a full implementation, this would recursively elaborate
        const subPattern = pattern.args[argIndex];
        let argType = ctorInfo!.params[argIndex].type;
        for (let j = 0; j < ctorMetas.length; j++) {
          argType = substitute(argType, ctorInfo!.params.length - 1 - j, ctorMetas[j]);
        }
        argType = zonk(s.metaState, argType);

        // Handle sub-pattern based on its type
        if (isWildcard(subPattern)) {
          // For wildcard sub-patterns, we use the corresponding constructor meta
          // that was already created in CreatingParamMetas phase.
          // This meta represents the elaborated term for this sub-pattern.
          const ctorMeta = ctorMetas[argIndex];

          // Store the sub-pattern term in the map for UI access
          const subPatternPath = `${patternIndex}.${argIndex}`;
          s.subPatternTerms.set(subPatternPath, ctorMeta);

          s.phase = {
            tag: 'ElaboratingPattern',
            patternIndex,
            subPhase: {
              tag: 'ProcessingConstructor',
              ctorName: pattern.name,
              step: { tag: 'ProcessingSubPattern', argIndex: argIndex + 1 }
            }
          };

          return this.makeRecord(
            `Sub-pattern ${argIndex + 1} is wildcard, elaborates to ${prettyTerm(ctorMeta, s.metaState)} : ${prettyTerm(argType, s.metaState)}`,
            'Process sub-pattern'
          );
        } else if (subPattern.tag === 'PVar') {
          // Bind variable
          const index = s.bindings.length;
          const varTerm: TTKTerm = mkVar(index);

          s.bindings.push({
            name: subPattern.name,
            type: argType,
            introducedBy: `${pattern.name} arg ${argIndex + 1}`
          });

          // Store the sub-pattern term (the variable) in the map
          const subPatternPath = `${patternIndex}.${argIndex}`;
          s.subPatternTerms.set(subPatternPath, varTerm);

          s.phase = {
            tag: 'ElaboratingPattern',
            patternIndex,
            subPhase: {
              tag: 'ProcessingConstructor',
              ctorName: pattern.name,
              step: { tag: 'ProcessingSubPattern', argIndex: argIndex + 1 }
            }
          };

          return this.makeRecord(
            `Sub-pattern ${argIndex + 1} binds ${subPattern.name} : ${prettyTerm(argType, s.metaState)} at #${index}`,
            'Process sub-pattern'
          );
        } else {
          // Nested constructor - for now, just note it
          s.phase = {
            tag: 'ElaboratingPattern',
            patternIndex,
            subPhase: {
              tag: 'ProcessingConstructor',
              ctorName: pattern.name,
              step: { tag: 'ProcessingSubPattern', argIndex: argIndex + 1 }
            }
          };
          return this.makeRecord(
            `Sub-pattern ${argIndex + 1} is nested constructor (simplified handling)`,
            'Process sub-pattern'
          );
        }
      }

      case 'BuildingTerm': {
        const ctorMetas: TTKTerm[] = (s as any).currentCtorMetas;
        let ctorTerm: TTKTerm = mkConst(pattern.name, mkType(0)); // Type is placeholder
        for (const meta of ctorMetas) {
          ctorTerm = mkApp(ctorTerm, zonk(s.metaState, meta));
        }

        s.patternTerms.push(ctorTerm);

        s.phase = {
          tag: 'ElaboratingPattern',
          patternIndex,
          subPhase: { tag: 'Finished', term: ctorTerm }
        };

        return this.makeRecord(
          `Built constructor term: ${prettyTerm(ctorTerm, s.metaState)}`,
          'Constructor done'
        );
      }
    }

    return this.makeRecord('Unknown constructor step', 'Error');
  }

  private stepComputeReturnType(): StepRecord {
    const s = this.state;

    // The return type has variables #0, #1, ... #(n-1) for the n patterns.
    // These are in binding order from the function signature.
    // We need to substitute each one with the corresponding pattern term.
    //
    // For vecConcat: (A : Type) → (a : Nat) → (b : Nat) → (xs : Vec A a) → (ys : Vec A b) → Vec A (plus a b)
    // The return type is: Vec #4 (plus #3 #2)  (in the context where A=#4, a=#3, b=#2, xs=#1, ys=#0)
    //
    // Actually, under the binders, the return type has:
    //   - #4 = A (outermost binder)
    //   - #3 = a
    //   - #2 = b
    //   - #1 = xs
    //   - #0 = ys (innermost binder)
    //
    // After unwrapping all Pis, we need to substitute pattern terms for these variables.
    // The substitution should go from inside out (highest index first).

    let refinedReturn = s.returnType!;

    // The return type's variables are numbered in reverse order from the pattern order.
    // Pattern 0 -> index (n-1), Pattern 1 -> index (n-2), ..., Pattern (n-1) -> index 0
    // where n is the number of patterns.
    //
    // To substitute correctly, we go from highest index to lowest.
    const n = s.patternTerms.length;
    for (let i = n - 1; i >= 0; i--) {
      // Variable at index i corresponds to pattern (n-1-i)
      const patternIndex = n - 1 - i;
      refinedReturn = substitute(refinedReturn, i, s.patternTerms[patternIndex]);
    }

    refinedReturn = zonk(s.metaState, refinedReturn);

    // Apply deep reduction to normalize (e.g., plus Zero n -> n)
    const reduced = deepReduce(refinedReturn, s.metaState);

    s.returnType = reduced;
    s.phase = { tag: 'CheckingRHS' };

    const beforeWhnf = prettyTerm(refinedReturn, s.metaState);
    const afterWhnf = prettyTerm(reduced, s.metaState);

    const description = beforeWhnf === afterWhnf
      ? `Refined return type: ${afterWhnf}`
      : `Refined return type: ${beforeWhnf} →β ${afterWhnf}`;

    return this.makeRecord(description, 'Return type computed');
  }

  private stepCheckRHS(): StepRecord {
    const s = this.state;

    // In a full implementation, we would type-check the RHS here
    // For now, just mark as done

    s.phase = { tag: 'Done' };

    return this.makeRecord(
      `RHS should have type: ${prettyTerm(s.returnType!, s.metaState)}`,
      'Elaboration complete'
    );
  }

  // =========================================================================
  // Unification (simplified)
  // =========================================================================

  private unify(t1: TTKTerm, t2: TTKTerm): boolean {
    const a = zonk(this.state.metaState, t1);
    const b = zonk(this.state.metaState, t2);

    if (a.tag === 'Hole') {
      const { state, success } = solveMeta(this.state.metaState, a.id, b);
      this.state.metaState = state;
      return success;
    }
    if (b.tag === 'Hole') {
      const { state, success } = solveMeta(this.state.metaState, b.id, a);
      this.state.metaState = state;
      return success;
    }

    if (a.tag !== b.tag) return false;

    switch (a.tag) {
      case 'Sort': return a.level === (b as typeof a).level;
      case 'Var': return a.index === (b as typeof a).index;
      case 'Const': return a.name === (b as typeof a).name;
      case 'App':
        return this.unify(a.fn, (b as typeof a).fn) && this.unify(a.arg, (b as typeof a).arg);
      case 'Binder':
        return this.unify(a.domain, (b as typeof a).domain) && this.unify(a.body, (b as typeof a).body);
      case 'Annot':
        return this.unify(a.term, (b as typeof a).term) && this.unify(a.type, (b as typeof a).type);
      case 'Match':
        // Simplified - match expressions rarely need unification
        return false;
    }

    return false;
  }

  // =========================================================================
  // Helpers
  // =========================================================================

  private makeRecord(description: string, action: string, metaChanges: string[] = []): StepRecord {
    return {
      stepNumber: this.state.stepNumber,
      description,
      phase: this.state.phase,
      action,
      metaChanges
    };
  }
}

// =============================================================================
// Factory function to create stepper from TTK types
// =============================================================================

/**
 * Create a pattern elaboration stepper from TTK types.
 * This is the main entry point for the visualization UI.
 */
export function createPatternElabStepper(
  clause: TTKClause,
  fnType: TTKTerm,
  env: Map<string, ConstructorInfo>
): PatternElabStepper {
  return new PatternElabStepper(clause, fnType, env);
}

// =============================================================================
// Test Functions (using TTK types)
// =============================================================================

function buildTestEnv(): Map<string, ConstructorInfo> {
  const env = new Map<string, ConstructorInfo>();
  const Nat: TTKTerm = mkConst('Nat', mkType(0));
  const Type: TTKTerm = mkType(0);
  const Zero: TTKTerm = mkConst('Zero', Nat);
  const Succ = (n: TTKTerm): TTKTerm => mkApp(mkConst('Succ', mkType(0)), n);
  const Vec = (A: TTKTerm, n: TTKTerm): TTKTerm => mkApp(mkApp(mkConst('Vec', mkType(0)), A), n);

  env.set('Zero', { name: 'Zero', params: [], returnType: Nat });
  env.set('Succ', { name: 'Succ', params: [{ name: 'n', type: Nat }], returnType: Nat });
  env.set('VNil', {
    name: 'VNil',
    params: [{ name: 'A', type: Type }],
    returnType: Vec(mkVar(0), Zero)
  });
  env.set('VCons', {
    name: 'VCons',
    params: [
      { name: 'A', type: Type },
      { name: 'n', type: Nat },
      { name: 'x', type: mkVar(1) },  // x : A (A is at index 1)
      { name: 'xs', type: Vec(mkVar(2), mkVar(1)) }  // xs : Vec A n
    ],
    returnType: Vec(mkVar(3), Succ(mkVar(2)))  // Vec A (Succ n)
  });

  return env;
}

export function testStepper(): void {
  console.log('\n' + '#'.repeat(70));
  console.log('# PATTERN ELABORATION STEPPER TEST');
  console.log('#'.repeat(70));

  const env = buildTestEnv();

  const Type: TTKTerm = mkType(0);
  const Nat: TTKTerm = mkConst('Nat', mkType(0));
  const Zero: TTKTerm = mkConst('Zero', Nat);
  const Vec = (A: TTKTerm, n: TTKTerm): TTKTerm => mkApp(mkApp(mkConst('Vec', mkType(0)), A), n);
  const plus = (a: TTKTerm, b: TTKTerm): TTKTerm => mkApp(mkApp(mkConst('plus', mkType(0)), a), b);

  // vecConcat type using TTK
  const vecConcatType: TTKTerm = mkPi(Type,
    mkPi(Nat,
      mkPi(Nat,
        mkPi(Vec(mkVar(2), mkVar(1)),
          mkPi(Vec(mkVar(3), mkVar(1)),
            Vec(mkVar(4), plus(mkVar(3), mkVar(2))),
          'ys'),
        'xs'),
      'b'),
    'a'),
  'A');

  // Clause 1: vecConcat _ _ _ (VNil _) v = v
  const clause1: TTKClause = {
    patterns: [
      { tag: 'PVar', name: '_' },
      { tag: 'PVar', name: '_' },
      { tag: 'PVar', name: '_' },
      { tag: 'PCtor', name: 'VNil', args: [{ tag: 'PVar', name: '_' }] },
      { tag: 'PVar', name: 'v' }
    ],
    rhs: mkVar(0)
  };

  console.log('\n' + '*'.repeat(70));
  console.log('* CLAUSE 1: vecConcat _ _ _ (VNil _) v = v');
  console.log('*'.repeat(70));

  const stepper = new PatternElabStepper(clause1, vecConcatType, env);

  // Step through one at a time
  while (!stepper.isDone()) {
    console.log(stepper.describeState());
    const record = stepper.step();
    console.log(`\n→ Action: ${record.action}`);
    console.log(`  ${record.description}`);
    if (record.metaChanges.length > 0) {
      console.log(`  Metas affected: ${record.metaChanges.join(', ')}`);
    }
  }

  console.log(stepper.describeState());
  console.log('\n✓ Elaboration complete!');
}

export function testSimple(): void {
  console.log('\n' + '#'.repeat(70));
  console.log('# SIMPLE TEST: isZero function');
  console.log('#'.repeat(70));

  const env = new Map<string, ConstructorInfo>();
  const Nat: TTKTerm = mkConst('Nat', mkType(0));
  const Bool: TTKTerm = mkConst('Bool', mkType(0));

  env.set('Zero', { name: 'Zero', params: [], returnType: Nat });
  env.set('Succ', {
    name: 'Succ',
    params: [{ name: 'n', type: Nat }],
    returnType: Nat
  });

  // isZero : Nat -> Bool
  const isZeroType: TTKTerm = mkPi(Nat, Bool, 'n');

  // Clause: isZero Zero = True
  const clause: TTKClause = {
    patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }],
    rhs: mkConst('True', Bool)
  };

  console.log('\nClause: isZero Zero = True');
  console.log('Type: Nat → Bool\n');

  const stepper = new PatternElabStepper(clause, isZeroType, env);

  while (!stepper.isDone()) {
    console.log(stepper.describeState());
    const record = stepper.step();
    console.log(`\n→ ${record.action}: ${record.description}`);
  }

  console.log(stepper.describeState());
}

export function testWithSucc(): void {
  console.log('\n' + '#'.repeat(70));
  console.log('# TEST: isZero (Succ n) - shows refinement!');
  console.log('#'.repeat(70));

  const env = new Map<string, ConstructorInfo>();
  const Nat: TTKTerm = mkConst('Nat', mkType(0));
  const Bool: TTKTerm = mkConst('Bool', mkType(0));

  env.set('Zero', { name: 'Zero', params: [], returnType: Nat });
  env.set('Succ', {
    name: 'Succ',
    params: [{ name: 'n', type: Nat }],
    returnType: Nat
  });

  // isZero : Nat -> Bool
  const isZeroType: TTKTerm = mkPi(Nat, Bool, 'n');

  // Clause: isZero (Succ n) = False
  const clause: TTKClause = {
    patterns: [{
      tag: 'PCtor',
      name: 'Succ',
      args: [{ tag: 'PVar', name: 'n' }]
    }],
    rhs: mkConst('False', Bool)
  };

  console.log('\nClause: isZero (Succ n) = False');
  console.log('Type: Nat → Bool');
  console.log('\nKey insight: matching Succ introduces a binding n : Nat\n');

  const stepper = new PatternElabStepper(clause, isZeroType, env);

  while (!stepper.isDone()) {
    console.log(stepper.describeState());
    const record = stepper.step();
    console.log(`\n→ ${record.action}: ${record.description}`);
  }

  console.log(stepper.describeState());
}

export function testVConsClause(): void {
  console.log('\n' + '#'.repeat(70));
  console.log('# TEST: vecConcat VCons clause - shows full dependent refinement!');
  console.log('#'.repeat(70));

  const env = buildTestEnv();

  const Type: TTKTerm = mkType(0);
  const Nat: TTKTerm = mkConst('Nat', mkType(0));
  const Vec = (A: TTKTerm, n: TTKTerm): TTKTerm => mkApp(mkApp(mkConst('Vec', mkType(0)), A), n);
  const plus = (a: TTKTerm, b: TTKTerm): TTKTerm => mkApp(mkApp(mkConst('plus', mkType(0)), a), b);
  const Succ = (n: TTKTerm): TTKTerm => mkApp(mkConst('Succ', mkType(0)), n);

  // vecConcat type
  const vecConcatType: TTKTerm = mkPi(Type,
    mkPi(Nat,
      mkPi(Nat,
        mkPi(Vec(mkVar(2), mkVar(1)),
          mkPi(Vec(mkVar(3), mkVar(1)),
            Vec(mkVar(4), plus(mkVar(3), mkVar(2))),
          'ys'),
        'xs'),
      'b'),
    'a'),
  'A');

  // Clause 2: vecConcat _ (Succ n) _ (VCons _ _ x xs) ys = ...
  const clause2: TTKClause = {
    patterns: [
      { tag: 'PVar', name: '_' },                                                    // _ : Type (A)
      { tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] },            // Succ n : Nat (a)
      { tag: 'PVar', name: '_' },                                                    // _ : Nat (b)
      { tag: 'PCtor', name: 'VCons', args: [                                         // VCons _ n x xs : Vec A (Succ n)
        { tag: 'PVar', name: '_' },                                                  // A implicit
        { tag: 'PVar', name: '_' },                                                  // n implicit (length of tail)
        { tag: 'PVar', name: 'x' },                                                  // x : A
        { tag: 'PVar', name: 'xs' }                                                  // xs : Vec A n
      ] },
      { tag: 'PVar', name: 'ys' }                                                    // ys : Vec A b
    ],
    rhs: mkConst('placeholder', mkType(0))  // RHS not important for this test
  };

  console.log('\nClause: vecConcat _ (Succ n) _ (VCons _ _ x xs) ys = ...');
  console.log('\nKey insights:');
  console.log('  1. Succ pattern introduces binding n : Nat');
  console.log('  2. VCons unifies: Vec ?A0 (Succ ?n0) =?= Vec A (Succ n)');
  console.log('  3. This solves ?n0 = n (the predecessor of a)');
  console.log('  4. Introduces bindings: x : A, xs : Vec A n');
  console.log('  5. Return type becomes Vec A (plus (Succ n) b) →β Vec A (Succ (plus n b))\n');

  const stepper = new PatternElabStepper(clause2, vecConcatType, env);

  // Run through, but only show key steps
  let stepCount = 0;
  while (!stepper.isDone()) {
    const record = stepper.step();
    stepCount++;

    // Show all steps for this demonstration
    if (stepCount <= 50) {
      console.log(`\n[${stepCount}] ${record.action}: ${record.description}`);
      if (record.metaChanges.length > 0) {
        console.log(`    Metas: ${record.metaChanges.join(', ')}`);
      }
    }
  }

  console.log('\n' + '-'.repeat(50));
  console.log('FINAL STATE:');
  console.log(stepper.describeState());
  console.log('\n✓ VCons clause elaboration complete!');
}

// Tests are available as exported functions: testSimple, testWithSucc, testStepper, testVConsClause
// To run tests manually:
//   import { testStepper } from './pattern-elab-stepper';
//   testStepper();
// Or from CLI: Create a separate test runner file
