/**
 * Pattern Elaboration Simulation
 *
 * This file simulates the pattern matching elaboration algorithm described
 * in the vecConcat walkthrough. The key phases are:
 *
 * 1. Signature checking: Verify the type signature is well-formed
 * 2. Clause elaboration: For each clause, unify patterns with expected types
 * 3. Constraint solving: Use pattern unification to solve metavariables
 *
 * The key insight is that dependent pattern matching REFINES types:
 * - Matching on a constructor tells us information about indices
 * - This refinement is essential for the return type to compute correctly
 */

// =============================================================================
// Types
// =============================================================================

/**
 * Terms in our type theory.
 * Using a simple representation for clarity.
 */
type Term =
  | { tag: 'Var'; name: string; index: number }  // De Bruijn + name for debugging
  | { tag: 'Meta'; id: string }                   // Metavariable ?m
  | { tag: 'Type' }                               // Type (universe)
  | { tag: 'Const'; name: string }                // Named constant (Nat, Vec, etc.)
  | { tag: 'App'; fn: Term; arg: Term }           // Application
  | { tag: 'Pi'; name: string; domain: Term; codomain: Term }  // Dependent function type
  | { tag: 'Lam'; name: string; domain: Term; body: Term }     // Lambda

/**
 * Patterns for pattern matching
 */
type Pattern =
  | { tag: 'PWild' }                              // Wildcard _
  | { tag: 'PVar'; name: string }                 // Variable binding
  | { tag: 'PCtor'; name: string; args: Pattern[] }  // Constructor pattern

/**
 * A clause in a function definition
 */
interface Clause {
  patterns: Pattern[];
  rhs: Term;
}

/**
 * Constructor info from the environment
 */
interface ConstructorInfo {
  name: string;
  // Full type as a telescope: [(name, type), ...] -> returnType
  // e.g., VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)
  params: Array<{ name: string; type: Term }>;
  returnType: Term;  // The return type (applied to params)
}

/**
 * Metavariable context - tracks created metas and their solutions
 */
class MetaCtx {
  private counter = 0;
  private metas: Map<string, { type: Term; solution: Term | null }> = new Map();

  /** Create a fresh metavariable */
  fresh(type: Term, prefix: string = 'm'): Term {
    const id = `?${prefix}${this.counter++}`;
    this.metas.set(id, { type, solution: null });
    return { tag: 'Meta', id };
  }

  /** Solve a metavariable */
  solve(id: string, solution: Term): boolean {
    const meta = this.metas.get(id);
    if (!meta) return false;
    if (meta.solution !== null) {
      // Already solved - check consistency
      return this.equal(meta.solution, solution);
    }
    // Occurs check
    if (this.occursIn(id, solution)) {
      console.log(`  [OCCURS CHECK FAILED] ${id} occurs in`, this.prettyTerm(solution));
      return false;
    }
    meta.solution = solution;
    console.log(`  [SOLVE] ${id} := ${this.prettyTerm(solution)}`);
    return true;
  }

  /** Check if a meta occurs in a term */
  occursIn(id: string, term: Term): boolean {
    switch (term.tag) {
      case 'Meta': return term.id === id;
      case 'Var':
      case 'Type':
      case 'Const': return false;
      case 'App': return this.occursIn(id, term.fn) || this.occursIn(id, term.arg);
      case 'Pi': return this.occursIn(id, term.domain) || this.occursIn(id, term.codomain);
      case 'Lam': return this.occursIn(id, term.domain) || this.occursIn(id, term.body);
    }
    return false;
  }

  /** Get solution for a meta */
  getSolution(id: string): Term | null {
    return this.metas.get(id)?.solution ?? null;
  }

  /** Zonk: substitute all solved metas */
  zonk(term: Term): Term {
    switch (term.tag) {
      case 'Meta': {
        const solution = this.getSolution(term.id);
        if (solution) return this.zonk(solution);
        return term;
      }
      case 'Var':
      case 'Type':
      case 'Const':
        return term;
      case 'App':
        return { tag: 'App', fn: this.zonk(term.fn), arg: this.zonk(term.arg) };
      case 'Pi':
        return { tag: 'Pi', name: term.name, domain: this.zonk(term.domain), codomain: this.zonk(term.codomain) };
      case 'Lam':
        return { tag: 'Lam', name: term.name, domain: this.zonk(term.domain), body: this.zonk(term.body) };
    }
  }

  /** Check structural equality (after zonking) */
  equal(t1: Term, t2: Term): boolean {
    const a = this.zonk(t1);
    const b = this.zonk(t2);
    if (a.tag !== b.tag) return false;
    switch (a.tag) {
      case 'Meta': return (b as typeof a).id === a.id;
      case 'Var': return (b as typeof a).index === a.index;
      case 'Type': return true;
      case 'Const': return (b as typeof a).name === a.name;
      case 'App': return this.equal(a.fn, (b as typeof a).fn) && this.equal(a.arg, (b as typeof a).arg);
      case 'Pi':
      case 'Lam': return this.equal(a.domain, (b as typeof a).domain) &&
                        this.equal((a as any).codomain ?? (a as any).body, (b as any).codomain ?? (b as any).body);
    }
    return false;
  }

  /** Pretty print a term */
  prettyTerm(term: Term): string {
    const t = this.zonk(term);
    switch (t.tag) {
      case 'Meta': return t.id;
      case 'Var': return t.name;
      case 'Type': return 'Type';
      case 'Const': return t.name;
      case 'App': {
        // Collect all args for nicer printing
        const args: Term[] = [];
        let fn: Term = t;
        while (fn.tag === 'App') {
          args.unshift(fn.arg);
          fn = fn.fn;
        }
        const fnStr = this.prettyTerm(fn);
        const argsStr = args.map(a => this.prettyTerm(a)).join(' ');
        return `(${fnStr} ${argsStr})`;
      }
      case 'Pi': {
        if (t.name === '_') {
          return `(${this.prettyTerm(t.domain)} → ${this.prettyTerm(t.codomain)})`;
        }
        return `((${t.name} : ${this.prettyTerm(t.domain)}) → ${this.prettyTerm(t.codomain)})`;
      }
      case 'Lam':
        return `(λ${t.name}. ${this.prettyTerm(t.body)})`;
    }
  }

  /** Print all metas and their solutions */
  printState(): void {
    console.log('\n  Meta solutions:');
    for (const [id, { type, solution }] of this.metas) {
      const solStr = solution ? this.prettyTerm(solution) : 'unsolved';
      console.log(`    ${id} : ${this.prettyTerm(type)} = ${solStr}`);
    }
  }
}

// =============================================================================
// Unification
// =============================================================================

/**
 * Unify two terms, solving metavariables.
 * This implements a simplified version of Miller's pattern unification.
 */
function unify(mctx: MetaCtx, t1: Term, t2: Term): boolean {
  const a = mctx.zonk(t1);
  const b = mctx.zonk(t2);

  console.log(`  [UNIFY] ${mctx.prettyTerm(a)} =?= ${mctx.prettyTerm(b)}`);

  // Same term
  if (a.tag === b.tag) {
    switch (a.tag) {
      case 'Type': return true;
      case 'Var': return a.index === (b as typeof a).index;
      case 'Const': return a.name === (b as typeof a).name;
      case 'Meta': {
        if (a.id === (b as typeof a).id) return true;
        // Two different metas - solve one to the other
        return mctx.solve(a.id, b);
      }
      case 'App': {
        // Decompose: (f a) = (g b) => f = g && a = b
        const bApp = b as typeof a;
        return unify(mctx, a.fn, bApp.fn) && unify(mctx, a.arg, bApp.arg);
      }
      case 'Pi': {
        const bPi = b as typeof a;
        return unify(mctx, a.domain, bPi.domain) && unify(mctx, a.codomain, bPi.codomain);
      }
      case 'Lam': {
        const bLam = b as typeof a;
        return unify(mctx, a.domain, bLam.domain) && unify(mctx, a.body, bLam.body);
      }
    }
  }

  // Flex-rigid: meta = term
  if (a.tag === 'Meta') {
    return mctx.solve(a.id, b);
  }
  if (b.tag === 'Meta') {
    return mctx.solve(b.id, a);
  }

  // Rigid-rigid mismatch
  console.log(`  [UNIFY FAIL] Cannot unify ${mctx.prettyTerm(a)} with ${mctx.prettyTerm(b)}`);
  return false;
}

// =============================================================================
// Environment - Constructors and Types
// =============================================================================

/**
 * Build the environment for our vecConcat example
 */
function buildEnvironment(): Map<string, ConstructorInfo> {
  const env = new Map<string, ConstructorInfo>();

  const Nat: Term = { tag: 'Const', name: 'Nat' };
  const Type: Term = { tag: 'Type' };
  const Zero: Term = { tag: 'Const', name: 'Zero' };
  const Succ = (n: Term): Term => ({ tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: n });
  const Vec = (A: Term, n: Term): Term => ({ tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'Vec' }, arg: A }, arg: n });
  const plus = (a: Term, b: Term): Term => ({ tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' }, arg: a }, arg: b });

  // Zero : Nat
  env.set('Zero', {
    name: 'Zero',
    params: [],
    returnType: Nat
  });

  // Succ : Nat -> Nat
  env.set('Succ', {
    name: 'Succ',
    params: [{ name: 'n', type: Nat }],
    returnType: Nat
  });

  // VNil : (A : Type) -> Vec A Zero
  env.set('VNil', {
    name: 'VNil',
    params: [{ name: 'A', type: Type }],
    returnType: Vec({ tag: 'Var', name: 'A', index: 0 }, Zero)
  });

  // VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)
  env.set('VCons', {
    name: 'VCons',
    params: [
      { name: 'A', type: Type },
      { name: 'n', type: Nat },
      { name: 'x', type: { tag: 'Var', name: 'A', index: 1 } },  // A is 1 level up
      { name: 'xs', type: Vec({ tag: 'Var', name: 'A', index: 2 }, { tag: 'Var', name: 'n', index: 1 }) }
    ],
    returnType: Vec({ tag: 'Var', name: 'A', index: 3 }, Succ({ tag: 'Var', name: 'n', index: 2 }))
  });

  return env;
}

// =============================================================================
// Pattern Context - tracks bindings during elaboration
// =============================================================================

interface PatternBinding {
  name: string;
  type: Term;
}

class PatternCtx {
  bindings: PatternBinding[] = [];

  /** Add a binding */
  bind(name: string, type: Term): void {
    this.bindings.push({ name, type });
  }

  /** Look up a binding by name */
  lookup(name: string): { index: number; type: Term } | null {
    for (let i = this.bindings.length - 1; i >= 0; i--) {
      if (this.bindings[i].name === name) {
        return { index: this.bindings.length - 1 - i, type: this.bindings[i].type };
      }
    }
    return null;
  }

  /** Get the number of bindings */
  size(): number {
    return this.bindings.length;
  }

  /** Clone the context */
  clone(): PatternCtx {
    const c = new PatternCtx();
    c.bindings = [...this.bindings];
    return c;
  }
}

// =============================================================================
// Pattern Elaboration
// =============================================================================

interface ElabResult {
  /** Substitution from pattern variables to their refined values */
  refinement: Map<string, Term>;
  /** New bindings introduced by the pattern */
  bindings: PatternBinding[];
}

/**
 * Elaborate a pattern against an expected type.
 *
 * This is the heart of dependent pattern matching:
 * - Wildcards create fresh metavariables
 * - Variables bind in the pattern context
 * - Constructors REFINE the type through unification
 */
function elaboratePattern(
  pattern: Pattern,
  expectedType: Term,
  pctx: PatternCtx,
  mctx: MetaCtx,
  env: Map<string, ConstructorInfo>
): ElabResult {
  console.log(`\n  Elaborating pattern against ${mctx.prettyTerm(expectedType)}`);

  switch (pattern.tag) {
    case 'PWild': {
      // Wildcard: create a fresh meta
      const meta = mctx.fresh(expectedType, 'w');
      console.log(`    Wildcard _ -> ${mctx.prettyTerm(meta)}`);
      return { refinement: new Map(), bindings: [] };
    }

    case 'PVar': {
      // Variable: bind in the pattern context
      console.log(`    Variable ${pattern.name} : ${mctx.prettyTerm(expectedType)}`);
      return {
        refinement: new Map(),
        bindings: [{ name: pattern.name, type: expectedType }]
      };
    }

    case 'PCtor': {
      // Constructor: this is where the magic happens
      const ctorInfo = env.get(pattern.name);
      if (!ctorInfo) {
        throw new Error(`Unknown constructor: ${pattern.name}`);
      }

      console.log(`    Constructor ${pattern.name}`);

      // Create fresh metas for each constructor parameter
      const paramMetas: Term[] = [];
      for (const param of ctorInfo.params) {
        // The type may reference earlier params, so substitute
        let paramType = param.type;
        for (let i = 0; i < paramMetas.length; i++) {
          paramType = substitute(paramType, ctorInfo.params.length - 1 - i, paramMetas[i]);
        }
        const meta = mctx.fresh(paramType, param.name[0]);
        paramMetas.push(meta);
        console.log(`      Fresh meta for ${param.name}: ${mctx.prettyTerm(meta)}`);
      }

      // Compute the constructor's return type with metas substituted
      let returnType = ctorInfo.returnType;
      for (let i = 0; i < paramMetas.length; i++) {
        returnType = substitute(returnType, ctorInfo.params.length - 1 - i, paramMetas[i]);
      }
      console.log(`      Constructor return type: ${mctx.prettyTerm(returnType)}`);

      // THE KEY STEP: Unify constructor return type with expected type
      // This may solve metas and refine indices!
      console.log(`      Unifying with expected type...`);
      if (!unify(mctx, returnType, expectedType)) {
        throw new Error(`Constructor ${pattern.name} cannot match type ${mctx.prettyTerm(expectedType)}`);
      }

      // Now recursively elaborate the sub-patterns
      const allBindings: PatternBinding[] = [];
      const refinement = new Map<string, Term>();

      // Match up pattern args with constructor params
      // Note: some params may be implicit (filled by metas), some explicit (matched by patterns)
      // For simplicity, we assume pattern.args corresponds to all params
      if (pattern.args.length !== ctorInfo.params.length) {
        throw new Error(`Constructor ${pattern.name} expects ${ctorInfo.params.length} args, got ${pattern.args.length}`);
      }

      for (let i = 0; i < pattern.args.length; i++) {
        // The expected type for this arg is the param type with metas substituted
        let argType = ctorInfo.params[i].type;
        for (let j = 0; j < paramMetas.length; j++) {
          argType = substitute(argType, ctorInfo.params.length - 1 - j, paramMetas[j]);
        }
        // Zonk to apply any solutions from unification
        argType = mctx.zonk(argType);

        const result = elaboratePattern(pattern.args[i], argType, pctx, mctx, env);
        for (const [k, v] of result.refinement) {
          refinement.set(k, v);
        }
        for (const b of result.bindings) {
          allBindings.push(b);
          pctx.bind(b.name, b.type);
        }
      }

      return { refinement, bindings: allBindings };
    }
  }
}

/**
 * Substitute a term for a De Bruijn index
 */
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
      return {
        tag: 'App',
        fn: substitute(term.fn, index, replacement),
        arg: substitute(term.arg, index, replacement)
      };
    case 'Pi':
      return {
        tag: 'Pi',
        name: term.name,
        domain: substitute(term.domain, index, replacement),
        codomain: substitute(term.codomain, index + 1, shift(replacement, 0, 1))
      };
    case 'Lam':
      return {
        tag: 'Lam',
        name: term.name,
        domain: substitute(term.domain, index, replacement),
        body: substitute(term.body, index + 1, shift(replacement, 0, 1))
      };
  }
}

/**
 * Shift De Bruijn indices
 */
function shift(term: Term, cutoff: number, amount: number): Term {
  switch (term.tag) {
    case 'Var':
      if (term.index >= cutoff) return { ...term, index: term.index + amount };
      return term;
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
// Clause Elaboration
// =============================================================================

/**
 * Elaborate a clause against an expected function type.
 *
 * THE KEY INSIGHT from the walkthrough:
 * - Each pattern position corresponds to a Pi binder in the function type
 * - When we match a constructor pattern, we REFINE the type
 * - This refinement is recorded as a substitution that affects subsequent types
 *
 * Steps:
 * 1. Unwrap the function type to get arg types and return type
 * 2. For each pattern:
 *    a. Create a fresh meta or bind a variable
 *    b. If constructor pattern, unify and potentially refine
 *    c. Apply any refinements to subsequent types
 * 3. Compute the refined return type
 * 4. Check the RHS against the refined return type
 */
function elaborateClause(
  clause: Clause,
  fnType: Term,
  mctx: MetaCtx,
  env: Map<string, ConstructorInfo>
): void {
  console.log('\n' + '='.repeat(60));
  console.log('ELABORATING CLAUSE');
  console.log('='.repeat(60));

  // Unwrap function type to get arg types
  // IMPORTANT: We'll need to track substitutions as we go
  const argTypes: Array<{ name: string; type: Term }> = [];
  let returnType = fnType;

  while (returnType.tag === 'Pi' && argTypes.length < clause.patterns.length) {
    argTypes.push({ name: returnType.name, type: returnType.domain });
    returnType = returnType.codomain;
  }

  console.log(`\nExpected arg types (before refinement):`);
  for (let i = 0; i < argTypes.length; i++) {
    console.log(`  ${i + 1}. ${argTypes[i].name} : ${mctx.prettyTerm(argTypes[i].type)}`);
  }
  console.log(`Expected return type: ${mctx.prettyTerm(returnType)}`);

  // Track the term that each pattern position maps to
  // This is the key data structure for refinement!
  // patternTerms[i] is the term that position i elaborates to
  const patternTerms: Term[] = [];

  // Elaborate each pattern
  const pctx = new PatternCtx();
  const allBindings: PatternBinding[] = [];

  for (let i = 0; i < clause.patterns.length; i++) {
    console.log(`\n--- Pattern ${i + 1} (${argTypes[i].name}) ---`);

    // The expected type may reference earlier patterns via De Bruijn indices
    // De Bruijn index 0 in argTypes[i] refers to argTypes[i-1], etc.
    // We need to substitute the patternTerms for those indices
    let expectedType = argTypes[i].type;

    // Apply substitutions for all previous patterns
    // Index j in the type refers to pattern (i - 1 - j)
    for (let j = 0; j < i; j++) {
      const patternIndex = i - 1 - j;
      expectedType = substitute(expectedType, j, patternTerms[patternIndex]);
    }
    expectedType = mctx.zonk(expectedType);

    console.log(`  Expected type (after substitution): ${mctx.prettyTerm(expectedType)}`);

    // Elaborate the pattern and determine what term it represents
    const result = elaboratePatternWithTerm(
      clause.patterns[i],
      expectedType,
      argTypes[i].name,
      pctx,
      mctx,
      env
    );

    patternTerms.push(result.term);
    console.log(`  Pattern elaborates to: ${mctx.prettyTerm(result.term)}`);

    for (const b of result.bindings) {
      allBindings.push(b);
    }
  }

  // Compute refined return type by substituting all pattern terms
  let refinedReturn = returnType;
  for (let j = 0; j < patternTerms.length; j++) {
    const patternIndex = patternTerms.length - 1 - j;
    refinedReturn = substitute(refinedReturn, j, patternTerms[patternIndex]);
  }
  refinedReturn = mctx.zonk(refinedReturn);

  console.log(`\nRefined return type: ${mctx.prettyTerm(refinedReturn)}`);

  // Show pattern context
  console.log(`\nPattern context (bindings for RHS):`);
  for (let i = allBindings.length - 1; i >= 0; i--) {
    const idx = allBindings.length - 1 - i;
    console.log(`  #${idx} ${allBindings[i].name} : ${mctx.prettyTerm(mctx.zonk(allBindings[i].type))}`);
  }

  // Type check RHS (simplified - just show what we'd check)
  console.log(`\nRHS should have type: ${mctx.prettyTerm(refinedReturn)}`);

  mctx.printState();
}

/**
 * Extended version of elaboratePattern that also returns the term
 * that the pattern represents (meta, constructor application, or var)
 */
interface ElabWithTermResult extends ElabResult {
  term: Term;  // The term this pattern elaborates to
}

function elaboratePatternWithTerm(
  pattern: Pattern,
  expectedType: Term,
  defaultName: string,
  pctx: PatternCtx,
  mctx: MetaCtx,
  env: Map<string, ConstructorInfo>
): ElabWithTermResult {
  switch (pattern.tag) {
    case 'PWild': {
      // Wildcard: create a fresh meta
      const meta = mctx.fresh(expectedType, defaultName[0]);
      console.log(`    Wildcard _ -> ${mctx.prettyTerm(meta)}`);
      return { refinement: new Map(), bindings: [], term: meta };
    }

    case 'PVar': {
      // Variable: bind in the pattern context and use a var term
      const idx = pctx.size();
      const varTerm: Term = { tag: 'Var', name: pattern.name, index: idx };
      pctx.bind(pattern.name, expectedType);
      console.log(`    Variable ${pattern.name} : ${mctx.prettyTerm(expectedType)} -> #${idx}`);
      return {
        refinement: new Map(),
        bindings: [{ name: pattern.name, type: expectedType }],
        term: varTerm
      };
    }

    case 'PCtor': {
      // Constructor: this is where refinement happens!
      const ctorInfo = env.get(pattern.name);
      if (!ctorInfo) {
        throw new Error(`Unknown constructor: ${pattern.name}`);
      }

      console.log(`    Constructor ${pattern.name}`);

      // Create fresh metas for each constructor parameter
      const paramMetas: Term[] = [];
      for (const param of ctorInfo.params) {
        // The type may reference earlier params, so substitute
        let paramType = param.type;
        for (let i = 0; i < paramMetas.length; i++) {
          paramType = substitute(paramType, ctorInfo.params.length - 1 - i, paramMetas[i]);
        }
        const meta = mctx.fresh(paramType, param.name[0]);
        paramMetas.push(meta);
        console.log(`      Fresh meta for ${param.name}: ${mctx.prettyTerm(meta)}`);
      }

      // Compute the constructor's return type with metas substituted
      let ctorReturnType = ctorInfo.returnType;
      for (let i = 0; i < paramMetas.length; i++) {
        ctorReturnType = substitute(ctorReturnType, ctorInfo.params.length - 1 - i, paramMetas[i]);
      }
      console.log(`      Constructor return type: ${mctx.prettyTerm(ctorReturnType)}`);

      // THE KEY STEP: Unify constructor return type with expected type
      console.log(`      Unifying with expected type: ${mctx.prettyTerm(expectedType)}`);
      if (!unify(mctx, ctorReturnType, expectedType)) {
        throw new Error(`Constructor ${pattern.name} cannot match type ${mctx.prettyTerm(expectedType)}`);
      }

      // Build the term: constructor applied to args
      let ctorTerm: Term = { tag: 'Const', name: pattern.name };
      for (const meta of paramMetas) {
        ctorTerm = { tag: 'App', fn: ctorTerm, arg: mctx.zonk(meta) };
      }

      // Now recursively elaborate the sub-patterns
      const allBindings: PatternBinding[] = [];
      const refinement = new Map<string, Term>();

      if (pattern.args.length !== ctorInfo.params.length) {
        throw new Error(`Constructor ${pattern.name} expects ${ctorInfo.params.length} args, got ${pattern.args.length}`);
      }

      for (let i = 0; i < pattern.args.length; i++) {
        // The expected type for this arg is the param type with metas substituted
        let argType = ctorInfo.params[i].type;
        for (let j = 0; j < paramMetas.length; j++) {
          argType = substitute(argType, ctorInfo.params.length - 1 - j, paramMetas[j]);
        }
        argType = mctx.zonk(argType);

        const result = elaboratePatternWithTerm(
          pattern.args[i],
          argType,
          ctorInfo.params[i].name,
          pctx,
          mctx,
          env
        );
        for (const [k, v] of result.refinement) {
          refinement.set(k, v);
        }
        for (const b of result.bindings) {
          allBindings.push(b);
        }
      }

      return { refinement, bindings: allBindings, term: mctx.zonk(ctorTerm) };
    }
  }
}

// =============================================================================
// Test: vecConcat
// =============================================================================

function testVecConcat(): void {
  console.log('\n' + '#'.repeat(70));
  console.log('# TESTING vecConcat ELABORATION');
  console.log('#'.repeat(70));

  const env = buildEnvironment();

  // Helper constructors
  const Type: Term = { tag: 'Type' };
  const Nat: Term = { tag: 'Const', name: 'Nat' };
  const Zero: Term = { tag: 'Const', name: 'Zero' };
  const Succ = (n: Term): Term => ({ tag: 'App', fn: { tag: 'Const', name: 'Succ' }, arg: n });
  const Vec = (A: Term, n: Term): Term => ({ tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'Vec' }, arg: A }, arg: n });
  const plus = (a: Term, b: Term): Term => ({ tag: 'App', fn: { tag: 'App', fn: { tag: 'Const', name: 'plus' }, arg: a }, arg: b });
  const mkVar = (name: string, index: number): Term => ({ tag: 'Var', name, index });

  // vecConcat : (A : Type) → (a : Nat) → (b : Nat) → Vec A a → Vec A b → Vec A (plus a b)
  // Build this type with De Bruijn indices:
  // (A : Type) → (a : Nat) → (b : Nat) → Vec #2 #1 → Vec #3 #1 → Vec #4 (plus #3 #2)
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

  const mctx = new MetaCtx();
  console.log('\nvecConcat type:', mctx.prettyTerm(vecConcatType));

  // Clause 1: vecConcat _ Zero _ (VNil _) v = v
  console.log('\n\n' + '*'.repeat(70));
  console.log('* CLAUSE 1: vecConcat _ Zero _ (VNil _) v = v');
  console.log('*'.repeat(70));

  const clause1: Clause = {
    patterns: [
      { tag: 'PWild' },                                    // _ : Type
      { tag: 'PCtor', name: 'Zero', args: [] },           // Zero : Nat (refines a = Zero)
      { tag: 'PWild' },                                    // _ : Nat
      { tag: 'PCtor', name: 'VNil', args: [{ tag: 'PWild' }] },  // VNil _ : Vec ?A Zero
      { tag: 'PVar', name: 'v' }                           // v : Vec ?A ?b
    ],
    rhs: mkVar('v', 0)  // placeholder
  };

  const mctx1 = new MetaCtx();
  elaborateClause(clause1, vecConcatType, mctx1, env);

  // Clause 2: vecConcat _ _ _ (VCons _ _ h tail) v = VCons _ _ h (vecConcat _ _ _ tail v)
  console.log('\n\n' + '*'.repeat(70));
  console.log('* CLAUSE 2: vecConcat _ _ _ (VCons _ _ h tail) v = ...');
  console.log('*'.repeat(70));

  const clause2: Clause = {
    patterns: [
      { tag: 'PWild' },                                    // _ : Type
      { tag: 'PWild' },                                    // _ : Nat (will be refined to Succ n)
      { tag: 'PWild' },                                    // _ : Nat
      { tag: 'PCtor', name: 'VCons', args: [              // VCons _ _ h tail : Vec ?A ?a
        { tag: 'PWild' },                                  // _ : Type (A)
        { tag: 'PWild' },                                  // _ : Nat (n, predecessor)
        { tag: 'PVar', name: 'h' },                        // h : A
        { tag: 'PVar', name: 'tail' }                      // tail : Vec A n
      ]},
      { tag: 'PVar', name: 'v' }                           // v : Vec ?A ?b
    ],
    rhs: mkVar('placeholder', 0)  // placeholder
  };

  const mctx2 = new MetaCtx();
  elaborateClause(clause2, vecConcatType, mctx2, env);
}

// =============================================================================
// Run
// =============================================================================

testVecConcat();

console.log('\n\n' + '='.repeat(70));
console.log('SIMULATION COMPLETE');
console.log('='.repeat(70));
