/**
 * Pattern Elaboration Stepper
 *
 * A step-by-step state machine for pattern matching elaboration.
 * Each call to `step()` advances the elaboration by one atomic operation,
 * making it perfect for visualization and debugging.
 *
 * Usage:
 *   const stepper = new PatternElabStepper(clause, fnType, env);
 *   while (!stepper.isDone()) {
 *     console.log(stepper.describeState());
 *     stepper.step();
 *   }
 *   console.log(stepper.getResult());
 */

// =============================================================================
// Term Representation
// =============================================================================

export type Term =
  | { tag: 'Var'; name: string; index: number }
  | { tag: 'Meta'; id: string }
  | { tag: 'Type' }
  | { tag: 'Const'; name: string }
  | { tag: 'App'; fn: Term; arg: Term }
  | { tag: 'Pi'; name: string; domain: Term; codomain: Term }
  | { tag: 'Lam'; name: string; domain: Term; body: Term };

export type Pattern =
  | { tag: 'PWild' }
  | { tag: 'PVar'; name: string }
  | { tag: 'PCtor'; name: string; args: Pattern[] };

export interface Clause {
  patterns: Pattern[];
  rhs: Term;
}

export interface ConstructorInfo {
  name: string;
  params: Array<{ name: string; type: Term }>;
  returnType: Term;
}

// =============================================================================
// Metavariable State
// =============================================================================

export interface MetaInfo {
  id: string;
  type: Term;
  solution: Term | null;
  createdAt: string;  // Description of when/why it was created
}

export interface MetaState {
  metas: Map<string, MetaInfo>;
  counter: number;
}

function freshMeta(state: MetaState, type: Term, reason: string, prefix = 'm'): { state: MetaState; meta: Term } {
  const id = `?${prefix}${state.counter}`;
  const newMetas = new Map(state.metas);
  newMetas.set(id, { id, type, solution: null, createdAt: reason });
  return {
    state: { metas: newMetas, counter: state.counter + 1 },
    meta: { tag: 'Meta', id }
  };
}

function solveMeta(state: MetaState, id: string, solution: Term): { state: MetaState; success: boolean } {
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

function zonk(state: MetaState, term: Term): Term {
  switch (term.tag) {
    case 'Meta': {
      const meta = state.metas.get(term.id);
      if (meta?.solution) return zonk(state, meta.solution);
      return term;
    }
    case 'Var':
    case 'Type':
    case 'Const':
      return term;
    case 'App':
      return { tag: 'App', fn: zonk(state, term.fn), arg: zonk(state, term.arg) };
    case 'Pi':
      return { tag: 'Pi', name: term.name, domain: zonk(state, term.domain), codomain: zonk(state, term.codomain) };
    case 'Lam':
      return { tag: 'Lam', name: term.name, domain: zonk(state, term.domain), body: zonk(state, term.body) };
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
  | { tag: 'Finished'; term: Term };

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
  lhs: Term;
  rhs: Term;
  reason: string;
}

/**
 * A binding introduced by a pattern
 */
export interface Binding {
  name: string;
  type: Term;
  introducedBy: string;  // Description of which pattern introduced this
}

/**
 * The complete state of the elaboration process
 */
export interface ElabState {
  // Input
  clause: Clause;
  fnType: Term;
  env: Map<string, ConstructorInfo>;

  // Current phase
  phase: ElabPhase;

  // Metavariable state
  metaState: MetaState;

  // Unwrapped function type
  argTypes: Array<{ name: string; type: Term }>;
  returnType: Term | null;

  // Pattern elaboration progress
  patternTerms: Term[];           // Term each pattern elaborates to
  bindings: Binding[];            // Variables bound by patterns
  currentPatternStack: Pattern[]; // Stack for nested pattern processing

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

export function prettyTerm(term: Term, metaState?: MetaState): string {
  const t = metaState ? zonk(metaState, term) : term;
  switch (t.tag) {
    case 'Meta': return t.id;
    case 'Var': return t.name || `#${t.index}`;
    case 'Type': return 'Type';
    case 'Const': return t.name;
    case 'App': {
      const args: Term[] = [];
      let fn: Term = t;
      while (fn.tag === 'App') {
        args.unshift(fn.arg);
        fn = fn.fn;
      }
      if (args.length === 0) return prettyTerm(fn, metaState);
      return `(${prettyTerm(fn, metaState)} ${args.map(a => prettyTerm(a, metaState)).join(' ')})`;
    }
    case 'Pi': {
      const dom = prettyTerm(t.domain, metaState);
      const cod = prettyTerm(t.codomain, metaState);
      if (t.name === '_') return `(${dom} → ${cod})`;
      return `(${t.name} : ${dom}) → ${cod}`;
    }
    case 'Lam':
      return `λ${t.name}. ${prettyTerm(t.body, metaState)}`;
  }
}

export function prettyPattern(p: Pattern): string {
  switch (p.tag) {
    case 'PWild': return '_';
    case 'PVar': return p.name;
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
// Substitution
// =============================================================================

function substitute(term: Term, index: number, replacement: Term): Term {
  switch (term.tag) {
    case 'Var':
      if (term.index === index) return replacement;
      if (term.index > index) return { ...term, index: term.index - 1 };
      return term;
    case 'Meta':
    case 'Type':
    case 'Const':
      return term;
    case 'App':
      return { tag: 'App', fn: substitute(term.fn, index, replacement), arg: substitute(term.arg, index, replacement) };
    case 'Pi':
      return {
        tag: 'Pi', name: term.name,
        domain: substitute(term.domain, index, replacement),
        codomain: substitute(term.codomain, index + 1, shift(replacement, 0, 1))
      };
    case 'Lam':
      return {
        tag: 'Lam', name: term.name,
        domain: substitute(term.domain, index, replacement),
        body: substitute(term.body, index + 1, shift(replacement, 0, 1))
      };
  }
}

function shift(term: Term, cutoff: number, amount: number): Term {
  switch (term.tag) {
    case 'Var':
      return term.index >= cutoff ? { ...term, index: term.index + amount } : term;
    case 'Meta':
    case 'Type':
    case 'Const':
      return term;
    case 'App':
      return { tag: 'App', fn: shift(term.fn, cutoff, amount), arg: shift(term.arg, cutoff, amount) };
    case 'Pi':
      return { tag: 'Pi', name: term.name, domain: shift(term.domain, cutoff, amount), codomain: shift(term.codomain, cutoff + 1, amount) };
    case 'Lam':
      return { tag: 'Lam', name: term.name, domain: shift(term.domain, cutoff, amount), body: shift(term.body, cutoff + 1, amount) };
  }
}

// =============================================================================
// Simple WHNF Reduction (for visualization)
// =============================================================================

/**
 * Performs simple WHNF reduction for known functions.
 * This is a minimal implementation for demonstration purposes.
 */
function whnf(term: Term, metaState: MetaState): Term {
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
          return whnf({
            tag: 'App',
            fn: { tag: 'Const', name: 'Succ' },
            arg: { tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' }, arg: m }, arg: n }
          }, metaState);
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
function deepReduce(term: Term, metaState: MetaState): Term {
  const t = whnf(term, metaState);

  switch (t.tag) {
    case 'App': {
      return {
        tag: 'App',
        fn: deepReduce(t.fn, metaState),
        arg: deepReduce(t.arg, metaState)
      };
    }
    case 'Pi':
      return {
        tag: 'Pi',
        name: t.name,
        domain: deepReduce(t.domain, metaState),
        codomain: deepReduce(t.codomain, metaState)
      };
    case 'Lam':
      return {
        tag: 'Lam',
        name: t.name,
        domain: deepReduce(t.domain, metaState),
        body: deepReduce(t.body, metaState)
      };
    default:
      return t;
  }
}

// =============================================================================
// The Stepper Class
// =============================================================================

export class PatternElabStepper {
  private state: ElabState;

  constructor(clause: Clause, fnType: Term, env: Map<string, ConstructorInfo>) {
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
    const beforeStep = this.state.stepNumber;
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
      if (currentType.tag === 'Pi') {
        currentType = currentType.codomain;
      }
    }

    if (currentType.tag === 'Pi' && piIndex < s.clause.patterns.length) {
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
        return this.stepProcessingConstructor(patternIndex, pattern as { tag: 'PCtor'; name: string; args: Pattern[] }, expectedType, subPhase);

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

  private stepPatternStart(patternIndex: number, pattern: Pattern, expectedType: Term): StepRecord {
    const s = this.state;
    const argName = s.argTypes[patternIndex].name;

    switch (pattern.tag) {
      case 'PWild':
        s.phase = {
          tag: 'ElaboratingPattern',
          patternIndex,
          subPhase: { tag: 'CreatingMeta', reason: `wildcard at position ${patternIndex + 1}` }
        };
        return this.makeRecord(
          `Pattern ${patternIndex + 1} is wildcard _, expected type: ${prettyTerm(expectedType, s.metaState)}`,
          'Will create metavariable'
        );

      case 'PVar':
        s.phase = {
          tag: 'ElaboratingPattern',
          patternIndex,
          subPhase: { tag: 'BindingVariable', name: pattern.name }
        };
        return this.makeRecord(
          `Pattern ${patternIndex + 1} is variable ${pattern.name}, expected type: ${prettyTerm(expectedType, s.metaState)}`,
          'Will bind variable'
        );

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

  private stepCreatingMeta(patternIndex: number, expectedType: Term, reason: string): StepRecord {
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

    return this.makeRecord(
      `Created metavariable ${prettyTerm(meta)} : ${prettyTerm(expectedType, s.metaState)}`,
      'Meta created',
      [(meta as { tag: 'Meta'; id: string }).id]
    );
  }

  private stepBindingVariable(patternIndex: number, name: string, expectedType: Term): StepRecord {
    const s = this.state;
    const index = s.bindings.length;
    const varTerm: Term = { tag: 'Var', name, index };

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
    pattern: { tag: 'PCtor'; name: string; args: Pattern[] },
    expectedType: Term,
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
        const ctorMetas: Term[] = (s as any).currentCtorMetas;

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

        return this.makeRecord(
          `Created ${prettyTerm(meta)} for constructor param ${param.name} : ${prettyTerm(paramType, s.metaState)}`,
          'Create param meta',
          [(meta as { tag: 'Meta'; id: string }).id]
        );
      }

      case 'ComputingReturnType': {
        const ctorMetas: Term[] = (s as any).currentCtorMetas;
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
        const ctorMetas: Term[] = (s as any).currentCtorMetas;

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
        if (subPattern.tag === 'PWild') {
          // Create meta for wildcard
          const { state: newMetaState, meta } = freshMeta(
            s.metaState,
            argType,
            `${pattern.name} arg ${argIndex + 1} wildcard`,
            ctorInfo!.params[argIndex].name[0]
          );
          s.metaState = newMetaState;

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
            `Sub-pattern ${argIndex + 1} is wildcard, created ${prettyTerm(meta)} : ${prettyTerm(argType, s.metaState)}`,
            'Process sub-pattern',
            [(meta as { tag: 'Meta'; id: string }).id]
          );
        } else if (subPattern.tag === 'PVar') {
          // Bind variable
          const index = s.bindings.length;
          s.bindings.push({
            name: subPattern.name,
            type: argType,
            introducedBy: `${pattern.name} arg ${argIndex + 1}`
          });

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
        const ctorMetas: Term[] = (s as any).currentCtorMetas;
        let ctorTerm: Term = { tag: 'Const', name: pattern.name };
        for (const meta of ctorMetas) {
          ctorTerm = { tag: 'App', fn: ctorTerm, arg: zonk(s.metaState, meta) };
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

  private unify(t1: Term, t2: Term): boolean {
    const a = zonk(this.state.metaState, t1);
    const b = zonk(this.state.metaState, t2);

    if (a.tag === 'Meta') {
      const { state, success } = solveMeta(this.state.metaState, a.id, b);
      this.state.metaState = state;
      return success;
    }
    if (b.tag === 'Meta') {
      const { state, success } = solveMeta(this.state.metaState, b.id, a);
      this.state.metaState = state;
      return success;
    }

    if (a.tag !== b.tag) return false;

    switch (a.tag) {
      case 'Type': return true;
      case 'Var': return a.index === (b as typeof a).index;
      case 'Const': return a.name === (b as typeof a).name;
      case 'App':
        return this.unify(a.fn, (b as typeof a).fn) && this.unify(a.arg, (b as typeof a).arg);
      case 'Pi':
        return this.unify(a.domain, (b as typeof a).domain) && this.unify(a.codomain, (b as typeof a).codomain);
      case 'Lam':
        return this.unify(a.domain, (b as typeof a).domain) && this.unify(a.body, (b as typeof a).body);
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
// Test
// =============================================================================

function buildTestEnv(): Map<string, ConstructorInfo> {
  const env = new Map<string, ConstructorInfo>();
  const Nat: Term = { tag: 'Const', name: 'Nat' };
  const Type: Term = { tag: 'Type' };
  const Zero: Term = { tag: 'Const', name: 'Zero' };
  const Succ = (n: Term): Term => ({ tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: n });
  const Vec = (A: Term, n: Term): Term => ({ tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'Vec' }, arg: A }, arg: n });

  env.set('Zero', { name: 'Zero', params: [], returnType: Nat });
  env.set('Succ', { name: 'Succ', params: [{ name: 'n', type: Nat }], returnType: Nat });
  env.set('VNil', {
    name: 'VNil',
    params: [{ name: 'A', type: Type }],
    returnType: Vec({ tag: 'Var', name: 'A', index: 0 }, Zero)
  });
  env.set('VCons', {
    name: 'VCons',
    params: [
      { name: 'A', type: Type },
      { name: 'n', type: Nat },
      { name: 'x', type: { tag: 'Var', name: 'A', index: 1 } },
      { name: 'xs', type: Vec({ tag: 'Var', name: 'A', index: 2 }, { tag: 'Var', name: 'n', index: 1 }) }
    ],
    returnType: Vec({ tag: 'Var', name: 'A', index: 3 }, Succ({ tag: 'Var', name: 'n', index: 2 }))
  });

  return env;
}

export function testStepper(): void {
  console.log('\n' + '#'.repeat(70));
  console.log('# PATTERN ELABORATION STEPPER TEST');
  console.log('#'.repeat(70));

  const env = buildTestEnv();

  const Type: Term = { tag: 'Type' };
  const Nat: Term = { tag: 'Const', name: 'Nat' };
  const Zero: Term = { tag: 'Const', name: 'Zero' };
  const mkVar = (name: string, index: number): Term => ({ tag: 'Var', name, index });
  const Vec = (A: Term, n: Term): Term => ({ tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'Vec' }, arg: A }, arg: n });
  const plus = (a: Term, b: Term): Term => ({ tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' }, arg: a }, arg: b });

  // vecConcat type
  const vecConcatType: Term = {
    tag: 'Pi', name: 'A', domain: Type,
    codomain: {
      tag: 'Pi', name: 'a', domain: Nat,
      codomain: {
        tag: 'Pi', name: 'b', domain: Nat,
        codomain: {
          tag: 'Pi', name: 'xs', domain: Vec(mkVar('A', 2), mkVar('a', 1)),
          codomain: {
            tag: 'Pi', name: 'ys', domain: Vec(mkVar('A', 3), mkVar('b', 1)),
            codomain: Vec(mkVar('A', 4), plus(mkVar('a', 3), mkVar('b', 2)))
          }
        }
      }
    }
  };

  // Clause 1: vecConcat _ Zero _ (VNil _) v = v
  const clause1: Clause = {
    patterns: [
      { tag: 'PWild' },
      { tag: 'PCtor', name: 'Zero', args: [] },
      { tag: 'PWild' },
      { tag: 'PCtor', name: 'VNil', args: [{ tag: 'PWild' }] },
      { tag: 'PVar', name: 'v' }
    ],
    rhs: mkVar('v', 0)
  };

  console.log('\n' + '*'.repeat(70));
  console.log('* CLAUSE 1: vecConcat _ Zero _ (VNil _) v = v');
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

// =============================================================================
// Simpler Test - shows refinement clearly
// =============================================================================

export function testSimple(): void {
  console.log('\n' + '#'.repeat(70));
  console.log('# SIMPLE TEST: isZero function');
  console.log('#'.repeat(70));

  const env = new Map<string, ConstructorInfo>();
  const Nat: Term = { tag: 'Const', name: 'Nat' };
  const Bool: Term = { tag: 'Const', name: 'Bool' };

  env.set('Zero', { name: 'Zero', params: [], returnType: Nat });
  env.set('Succ', {
    name: 'Succ',
    params: [{ name: 'n', type: Nat }],
    returnType: Nat
  });

  // isZero : Nat -> Bool
  const isZeroType: Term = {
    tag: 'Pi', name: 'n', domain: Nat,
    codomain: Bool
  };

  // Clause: isZero Zero = True
  const clause: Clause = {
    patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }],
    rhs: { tag: 'Const', name: 'True' }
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
  const Nat: Term = { tag: 'Const', name: 'Nat' };
  const Bool: Term = { tag: 'Const', name: 'Bool' };

  env.set('Zero', { name: 'Zero', params: [], returnType: Nat });
  env.set('Succ', {
    name: 'Succ',
    params: [{ name: 'n', type: Nat }],
    returnType: Nat
  });

  // isZero : Nat -> Bool
  const isZeroType: Term = {
    tag: 'Pi', name: 'n', domain: Nat,
    codomain: Bool
  };

  // Clause: isZero (Succ n) = False
  // This refines the input to Succ ?n and introduces binding n : Nat
  const clause: Clause = {
    patterns: [{
      tag: 'PCtor',
      name: 'Succ',
      args: [{ tag: 'PVar', name: 'n' }]
    }],
    rhs: { tag: 'Const', name: 'False' }
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

// =============================================================================
// VCons clause test - shows refinement of indexed types
// =============================================================================

export function testVConsClause(): void {
  console.log('\n' + '#'.repeat(70));
  console.log('# TEST: vecConcat VCons clause - shows full dependent refinement!');
  console.log('#'.repeat(70));

  const env = buildTestEnv();

  const Type: Term = { tag: 'Type' };
  const Nat: Term = { tag: 'Const', name: 'Nat' };
  const mkVar = (name: string, index: number): Term => ({ tag: 'Var', name, index });
  const Vec = (A: Term, n: Term): Term => ({ tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'Vec' }, arg: A }, arg: n });
  const plus = (a: Term, b: Term): Term => ({ tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' }, arg: a }, arg: b });
  const Succ = (n: Term): Term => ({ tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: n });

  // vecConcat type
  const vecConcatType: Term = {
    tag: 'Pi', name: 'A', domain: Type,
    codomain: {
      tag: 'Pi', name: 'a', domain: Nat,
      codomain: {
        tag: 'Pi', name: 'b', domain: Nat,
        codomain: {
          tag: 'Pi', name: 'xs', domain: Vec(mkVar('A', 2), mkVar('a', 1)),
          codomain: {
            tag: 'Pi', name: 'ys', domain: Vec(mkVar('A', 3), mkVar('b', 1)),
            codomain: Vec(mkVar('A', 4), plus(mkVar('a', 3), mkVar('b', 2)))
          }
        }
      }
    }
  };

  // Clause 2: vecConcat _ (Succ n) _ (VCons _ _ x xs) ys = VCons _ _ x (vecConcat _ n _ xs ys)
  // Note: We simplify the VCons pattern to match variables/wildcards for the sub-patterns
  const clause2: Clause = {
    patterns: [
      { tag: 'PWild' },                                                    // _ : Type (A)
      { tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] }, // Succ n : Nat (a)
      { tag: 'PWild' },                                                    // _ : Nat (b)
      { tag: 'PCtor', name: 'VCons', args: [                              // VCons _ n x xs : Vec A (Succ n)
        { tag: 'PWild' },                                                  // A implicit
        { tag: 'PWild' },                                                  // n implicit (length of tail)
        { tag: 'PVar', name: 'x' },                                        // x : A
        { tag: 'PVar', name: 'xs' }                                        // xs : Vec A n
      ] },
      { tag: 'PVar', name: 'ys' }                                          // ys : Vec A b
    ],
    rhs: { tag: 'Const', name: 'placeholder' }  // RHS not important for this test
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
    const state = stepper.getState();
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
