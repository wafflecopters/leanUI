# Tactics Implementation Plan

## Executive Summary

This document outlines the design and implementation of a tactic-based proof system for LeanUI. The system will be **hyper-focused on the immutable engine**, leveraging LeanUI's existing metavariable and constraint infrastructure.

**Key Principle**: Tactics don't manipulate abstract "goals" — they **build terms with typed holes (metavariables)**.

---

## Research Foundation

### Lean 4 Architecture
- **TacticM Monad**: Extends term elaboration with goal-oriented proof construction
- **Goals as Metavariables**: Each goal is simply a metavariable (`MVarId`)
- **Integration**: Tactics deeply integrated with elaboration system
- Sources: [Lean 4 Tactics Documentation](https://leanprover-community.github.io/lean4-metaprogramming-book/main/09_tactics.html), [Lean 4 System Description](https://lean-lang.org/papers/lean4.pdf)

### Coq Proof Engine
- **Proofview Monad**: Monadic API for proof state manipulation
- **Evars (Existential Variables)**: Typed holes defined by context and return type
- **Goal State**: Ordered list of evars to be filled
- Sources: [Coq Proof Engine Documentation](https://github.com/coq/coq/blob/master/dev/doc/proof-engine.md), [Mtac2: Typed Tactics](https://iris-project.org/pdfs/2018-icfp-mtac2-final.pdf)

### Idris 2 Elaboration
- **TTImp → TT Pipeline**: Elaboration with postponed unification problems
- **Implicit Search**: Only begins when determining arguments don't contain holes
- **Hole Scope**: Each hole has a scope and type
- Sources: [Idris 2 Implementation Overview](https://idris2.readthedocs.io/en/latest/implementation/overview.html), [Elaborator Reflection](https://docs.idris-lang.org/en/latest/elaboratorReflection/elaborator-reflection.html)

### Academic Research
- **Compositional Pre-processing**: Predictable, atomic goal transformations ([CPP 2023](https://dl.acm.org/doi/abs/10.1145/3573105.3575676))
- **Normalization by Evaluation**: For type checking and proof search ([ICFP 2019](https://dl.acm.org/doi/10.1145/3341711))

---

## Architecture Overview

### The Core Insight

```
ProofState = TTKTerm with Metavariables + Constraint Set
```

A proof in progress is simply a term under construction, with metavariables representing unfilled parts.

```typescript
// Conceptual example:
// Proving: modusPonens : {A B : Type} -> A -> (A -> B) -> B

// Initial state:
term = ?goal0
metas = { ?goal0: { type: {A B : Type} -> A -> (A -> B) -> B, ctx: [] } }

// After `intro A`:
term = λ{A:Type} => ?goal1
metas = { ?goal1: { type: {B : Type} -> A -> (A -> B) -> B, ctx: [A:Type] } }

// After `intro B`:
term = λ{A:Type} => λ{B:Type} => ?goal2
metas = { ?goal2: { type: A -> (A -> B) -> B, ctx: [A:Type, B:Type] } }

// After `intro a`:
term = λ{A:Type} => λ{B:Type} => λ(a:A) => ?goal3
metas = { ?goal3: { type: (A -> B) -> B, ctx: [A:Type, B:Type, a:A] } }

// After `intro f`:
term = λ{A:Type} => λ{B:Type} => λ(a:A) => λ(f:A->B) => ?goal4
metas = { ?goal4: { type: B, ctx: [A:Type, B:Type, a:A, f:A->B] } }

// After `apply f`:
term = λ{A:Type} => λ{B:Type} => λ(a:A) => λ(f:A->B) => f ?arg
metas = { ?arg: { type: A, ctx: [A:Type, B:Type, a:A, f:A->B] } }

// After `exact a`:
term = λ{A:Type} => λ{B:Type} => λ(a:A) => λ(f:A->B) => f a
metas = {}  // No unsolved metas — proof complete!
```

---

## Leveraging Existing Infrastructure

LeanUI already has the essential components:

### 1. **Metavariable System** (`src/compiler/term.ts`)

```typescript
type MetaVar = {
  ctx: TTKContext,        // Context where meta was created
  type: TTKTerm,          // Target type (the goal type)
  solution?: TTKTerm,     // Solution (undefined = unsolved)
  isHole?: boolean        // Explicit user hole?
}
```

**Perfect for tactics**: Each unsolved metavariable IS a goal.

### 2. **Type Checking Environment** (`src/compiler/term.ts`)

```typescript
class TCEnv<T> {
  context: TTKContext                    // Local hypotheses
  metaVars: Map<string, MetaVar>         // All metas (goals)
  constraints: Constraint[]              // Pending constraints
  definitions: DefinitionsMap            // Global definitions
  // ... other fields
}
```

**Perfect for proof state**: Immutable, tracks goals and context.

### 3. **Constraint Solving** (`src/compiler/meta.ts`)

```typescript
function solveConstraints(
  metaVars: Map<string, MetaVar>,
  constraints: Constraint[],
  ...
): { constraints: Constraint[], metaVars: Map<string, MetaVar> }
```

**Perfect for tactic validation**: Ensures solutions are well-typed.

### 4. **Unification** (`src/compiler/unify.ts`)

```typescript
function unifyTerms(
  t1: TTKTerm,
  t2: TTKTerm,
  options: UnifyOptions
): UnifyResult
```

**Perfect for tactics**: `apply` and `refine` need unification.

---

## Core Data Structures

### 1. TacticEngine (Immutable)

The **heart** of the system.

```typescript
/**
 * TacticEngine: Immutable proof state manager
 *
 * Responsibilities:
 * - Track open goals (unsolved metas)
 * - Maintain proof term under construction
 * - Apply tactics to transform state
 * - Validate solutions via constraint solving
 */
export class TacticEngine {
  constructor(
    /** The proof term being built (may contain Metas) */
    public readonly term: TTKTerm,

    /** All metavariables (goals + solved) */
    public readonly metaVars: Map<string, MetaVar>,

    /** Active constraint set */
    public readonly constraints: Constraint[],

    /** Global definitions (inductive types, constants) */
    public readonly definitions: DefinitionsMap,

    /** Ordered list of goal IDs (unsolved metas) */
    public readonly goals: string[],

    /** Focus: which goal are we working on? (index into goals) */
    public readonly focusIndex: number
  ) {}

  // --- Query Methods ---

  /** Get the current focused goal */
  getFocusedGoal(): MetaVar | null {
    const goalId = this.goals[this.focusIndex];
    return goalId ? this.metaVars.get(goalId) ?? null : null;
  }

  /** Get all unsolved goals */
  getUnsolvedGoals(): MetaVar[] {
    return this.goals
      .map(id => this.metaVars.get(id))
      .filter((mv): mv is MetaVar => mv !== undefined && mv.solution === undefined);
  }

  /** Check if proof is complete (no unsolved goals) */
  isComplete(): boolean {
    return this.getUnsolvedGoals().length === 0;
  }

  /** Substitute solved metas in term (zonking) */
  zonk(): TTKTerm {
    return zonkTermWithMetas(this.term, this.metaVars);
  }

  // --- State Transformation Methods ---

  /** Apply a tactic to the focused goal */
  applyTactic(tactic: Tactic): TacticResult {
    const goal = this.getFocusedGoal();
    if (!goal) {
      return { success: false, error: 'No focused goal' };
    }
    return tactic.apply(this, goal, this.goals[this.focusIndex]!);
  }

  /** Create a new engine with updated state */
  withUpdates(updates: Partial<{
    term: TTKTerm,
    metaVars: Map<string, MetaVar>,
    constraints: Constraint[],
    goals: string[],
    focusIndex: number
  }>): TacticEngine {
    return new TacticEngine(
      updates.term ?? this.term,
      updates.metaVars ?? this.metaVars,
      updates.constraints ?? this.constraints,
      this.definitions,
      updates.goals ?? this.goals,
      updates.focusIndex ?? this.focusIndex
    );
  }

  /** Solve constraints and update metavar solutions */
  solveConstraints(): TacticEngine {
    const result = solveConstraints(
      this.metaVars,
      this.constraints,
      undefined,
      this.definitions
    );
    return this.withUpdates({
      metaVars: result.metaVars,
      constraints: result.constraints
    });
  }

  /** Move focus to next goal */
  focusNext(): TacticEngine {
    const nextIndex = (this.focusIndex + 1) % Math.max(1, this.goals.length);
    return this.withUpdates({ focusIndex: nextIndex });
  }

  /** Move focus to previous goal */
  focusPrev(): TacticEngine {
    const prevIndex = this.focusIndex === 0
      ? Math.max(0, this.goals.length - 1)
      : this.focusIndex - 1;
    return this.withUpdates({ focusIndex: prevIndex });
  }

  /** Set focus to specific goal by ID */
  focusGoal(goalId: string): TacticEngine {
    const index = this.goals.indexOf(goalId);
    if (index === -1) return this;
    return this.withUpdates({ focusIndex: index });
  }
}
```

### 2. Tactic Interface

```typescript
/**
 * TacticResult: Outcome of applying a tactic
 */
export type TacticResult =
  | { success: true; newEngine: TacticEngine }
  | { success: false; error: string; cause?: Error };

/**
 * Tactic: A proof state transformation
 */
export interface Tactic {
  /** Human-readable name */
  name: string;

  /** Apply this tactic to the given goal */
  apply(
    engine: TacticEngine,
    goal: MetaVar,
    goalId: string
  ): TacticResult;
}

/**
 * TacticSequence: Compose tactics
 */
export class TacticSequence implements Tactic {
  constructor(
    public readonly name: string,
    public readonly tactics: Tactic[]
  ) {}

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    let current = engine;
    for (const tactic of this.tactics) {
      const result = current.applyTactic(tactic);
      if (!result.success) return result;
      current = result.newEngine;
    }
    return { success: true, newEngine: current };
  }
}
```

### 3. Goal Representation

**No new types needed!** Goals are just unsolved metavariables:

```typescript
// A goal is a MetaVar where solution === undefined
type Goal = MetaVar & { solution: undefined };

// Goal type = the type we need to prove
const goalType: TTKTerm = goal.type;

// Local hypotheses = the context where goal was created
const hypotheses: TTKContext = goal.ctx;
```

---

## Core Tactics to Implement

### Phase 1: Basic Tactics (MVP)

#### 1. `exact`

**What it does**: Solve the goal by providing the exact term.

```typescript
export class ExactTactic implements Tactic {
  constructor(public readonly term: TTKTerm) {}
  name = 'exact';

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      // Elaborate term in goal's context
      const env = new TCEnv(
        goal.ctx,
        engine.definitions,
        engine.metaVars,
        engine.constraints,
        /* indexPath */ [],
        /* valueStack */ [],
        this.term,
        new Map(), // levelMetas
        { mode: 'check' }
      );

      // Check term has expected type
      const checkedEnv = checkType(env, goal.type);

      // Zonk the checked term (resolve any new metas)
      const solution = checkedEnv.zonkTerm(checkedEnv.elaboratedTerm ?? this.term);

      // Assign solution to goal
      const newMetaVars = new Map(engine.metaVars);
      newMetaVars.set(goalId, { ...goal, solution });

      // Remove goal from goal list
      const newGoals = engine.goals.filter(id => id !== goalId);

      return {
        success: true,
        newEngine: engine.withUpdates({
          metaVars: newMetaVars,
          constraints: checkedEnv.constraints,
          goals: newGoals
        }).solveConstraints()
      };
    } catch (e) {
      return {
        success: false,
        error: `exact: ${e instanceof Error ? e.message : String(e)}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }
}
```

#### 2. `assumption`

**What it does**: Search local context for a term of the goal type.

```typescript
export class AssumptionTactic implements Tactic {
  name = 'assumption';

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    const goalType = goal.type;

    // Search context backwards (most recent first)
    for (let i = goal.ctx.length - 1; i >= 0; i--) {
      const hyp = goal.ctx[i];

      // Check if hypothesis type matches goal type
      if (areTypesDefEq(hyp.type, goalType, engine.definitions)) {
        // Use variable at de Bruijn index (goal.ctx.length - 1 - i)
        const varIndex = goal.ctx.length - 1 - i;
        const solution: TTKTerm = { tag: 'Var', index: varIndex };

        // Apply exact with the variable
        return new ExactTactic(solution).apply(engine, goal, goalId);
      }
    }

    return {
      success: false,
      error: 'assumption: no matching hypothesis found'
    };
  }
}
```

#### 3. `intro` / `intros`

**What it does**: Introduce a Pi binder into the context.

```typescript
export class IntroTactic implements Tactic {
  constructor(public readonly name_?: string) {}
  name = 'intro';

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    const goalType = goal.type;

    // Reduce goal type to WHNF
    const goalTypeWhnf = whnf(goalType, {
      definitions: engine.definitions,
      unfoldDelta: true
    });

    // Check if goal type is a Pi
    if (goalTypeWhnf.tag !== 'Pi') {
      return {
        success: false,
        error: `intro: goal type is not a function type (got ${goalTypeWhnf.tag})`
      };
    }

    const { binder, domain, body } = goalTypeWhnf;

    // Determine name (user-provided or from binder)
    const paramName = this.name_ ?? binder.name ?? 'x';

    // Extend context with new parameter
    const newCtx = [...goal.ctx, { name: paramName, type: domain }];

    // Create fresh meta for body
    const newGoalId = freshMetaName();
    const newGoal: MetaVar = {
      ctx: newCtx,
      type: body, // Note: body already has correct de Bruijn indices
      solution: undefined
    };

    // Build lambda term: λ(paramName : domain) => ?newGoal
    const lambdaTerm: TTKTerm = {
      tag: 'Lambda',
      binder: { ...binder, name: paramName },
      domain,
      body: { tag: 'Meta', id: newGoalId }
    };

    // Assign lambda to current goal
    const newMetaVars = new Map(engine.metaVars);
    newMetaVars.set(goalId, { ...goal, solution: lambdaTerm });
    newMetaVars.set(newGoalId, newGoal);

    // Replace current goal with new goal
    const newGoals = engine.goals.map(id => id === goalId ? newGoalId : id);

    return {
      success: true,
      newEngine: engine.withUpdates({
        metaVars: newMetaVars,
        goals: newGoals
      })
    };
  }
}

/**
 * intros: Apply intro repeatedly until goal is not a Pi
 *
 * Optionally provide names: intros(["A", "B", "a", "f"])
 */
export class IntrosTactic implements Tactic {
  constructor(public readonly names?: string[]) {}
  name = 'intros';

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    let current = engine;
    let nameIndex = 0;

    while (true) {
      const currentGoal = current.getFocusedGoal();
      if (!currentGoal) break;

      const goalTypeWhnf = whnf(currentGoal.type, {
        definitions: current.definitions,
        unfoldDelta: true
      });

      if (goalTypeWhnf.tag !== 'Pi') break;

      // Determine name
      const name = this.names && nameIndex < this.names.length
        ? this.names[nameIndex]
        : undefined;
      nameIndex++;

      // Apply intro
      const introResult = new IntroTactic(name).apply(
        current,
        currentGoal,
        current.goals[current.focusIndex]!
      );

      if (!introResult.success) {
        // If intro fails for any reason, return what we have so far
        return { success: true, newEngine: current };
      }

      current = introResult.newEngine;
    }

    return { success: true, newEngine: current };
  }
}
```

#### 4. `apply`

**What it does**: Apply a function to solve the goal, creating subgoals for arguments.

```typescript
export class ApplyTactic implements Tactic {
  constructor(public readonly fn: TTKTerm) {}
  name = 'apply';

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      // Infer type of function in goal's context
      const env = new TCEnv(
        goal.ctx,
        engine.definitions,
        engine.metaVars,
        engine.constraints,
        [],
        [],
        this.fn,
        new Map(),
        { mode: 'check' }
      );

      const inferredEnv = inferType(env);
      const fnType = inferredEnv.value; // The inferred type

      // Collect arguments from Pi type
      const argMetas: { id: string; meta: MetaVar }[] = [];
      let currentType = whnf(fnType, {
        definitions: engine.definitions,
        unfoldDelta: true
      });

      while (currentType.tag === 'Pi') {
        // Create meta for this argument
        const argMetaId = freshMetaName();
        const argMeta: MetaVar = {
          ctx: goal.ctx,
          type: currentType.domain,
          solution: undefined
        };
        argMetas.push({ id: argMetaId, meta: argMeta });

        // Substitute meta into body to get next type
        currentType = subst(0, { tag: 'Meta', id: argMetaId }, currentType.body);
        currentType = whnf(currentType, {
          definitions: engine.definitions,
          unfoldDelta: true
        });
      }

      // Unify return type with goal type
      const unifyResult = unifyTerms(currentType, goal.type, {
        mode: 'check',
        definitions: engine.definitions,
        flexibleVars: false
      });

      if (!unifyResult.success) {
        return {
          success: false,
          error: `apply: return type mismatch (${unifyResult.reason})`
        };
      }

      // Build application term: fn ?arg1 ?arg2 ...
      let appTerm: TTKTerm = this.fn;
      for (const { id } of argMetas) {
        appTerm = {
          tag: 'App',
          fn: appTerm,
          arg: { tag: 'Meta', id }
        };
      }

      // Assign application to goal
      const newMetaVars = new Map(engine.metaVars);
      newMetaVars.set(goalId, { ...goal, solution: appTerm });

      // Add arg metas to metaVars
      for (const { id, meta } of argMetas) {
        newMetaVars.set(id, meta);
      }

      // Add substitutions from unification
      for (const [varIdx, replacement] of unifyResult.substitutions) {
        // Apply substitution to all metas (if needed)
        // This is context-dependent - may need helper
      }

      // Add meta constraints from unification
      const newConstraints = [
        ...engine.constraints,
        ...unifyResult.metaConstraints.map(mc => ({
          ctx: goal.ctx,
          meta: mc.meta,
          rhs: mc.rhs
        }))
      ];

      // Replace current goal with arg metas
      const newGoalIds = argMetas.map(({ id }) => id);
      const newGoals = [
        ...engine.goals.slice(0, engine.focusIndex),
        ...newGoalIds,
        ...engine.goals.slice(engine.focusIndex + 1)
      ];

      return {
        success: true,
        newEngine: engine.withUpdates({
          metaVars: newMetaVars,
          constraints: newConstraints,
          goals: newGoals
        }).solveConstraints()
      };
    } catch (e) {
      return {
        success: false,
        error: `apply: ${e instanceof Error ? e.message : String(e)}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }
}
```

### Phase 2: Convenience Tactics

#### 5. `refine`

Like `exact`, but allows holes (`_`) in the term that become new goals.

#### 6. `split` / `constructor`

For inductive types with one constructor (records, sigma, etc.), apply the constructor.

#### 7. `cases`

Pattern match on a hypothesis of inductive type, creating subgoals for each constructor.

#### 8. `revert`

Opposite of `intro`: move a hypothesis back into the goal type.

---

## Syntax Design

### Tactic Blocks

Following Lean/Coq style:

```
modusPonens : {A B : Type} -> A -> (A -> B) -> B := by
  intro A
  intro B
  intro a
  intro f
  apply f
  exact a
```

Alternative (Coq-style, more explicit):

```
modusPonens : {A B : Type} -> A -> (A -> B) -> B := by
  intros [A, B, a, f]
  apply f
  assumption
```

### Parser Changes

Add to `parseTerm` in `src/parser/parser.ts`:

```typescript
// Check for "by" keyword
if (this.match('by')) {
  this.consume('by');
  const tactics = this.parseTacticBlock();
  return { tag: 'TacticBlock', tactics };
}
```

```typescript
parseTacticBlock(): TacticScript {
  const tactics: TacticCommand[] = [];

  // Tactics are indented relative to "by"
  this.consumeNewline();
  this.expectIndentIncrease();

  while (!this.atIndentDecrease() && !this.isAtEnd()) {
    tactics.push(this.parseTacticCommand());
    if (!this.isAtEnd() && !this.atIndentDecrease()) {
      this.consumeNewline();
    }
  }

  this.expectIndentDecrease();
  return { tag: 'TacticScript', tactics };
}

parseTacticCommand(): TacticCommand {
  const name = this.consume('identifier').lexeme;
  const args: TTerm[] = [];

  // Parse tactic arguments (if any)
  while (!this.isAtNewline() && !this.isAtEnd()) {
    args.push(this.parseTerm());
  }

  return { name, args };
}
```

### TT Representation

```typescript
// src/types/tt-core.ts

export type TTerm =
  | ... existing variants
  | { tag: 'TacticBlock'; tactics: TacticScript };

export type TacticScript = {
  tag: 'TacticScript';
  tactics: TacticCommand[];
};

export type TacticCommand = {
  name: string;       // "intro", "exact", "apply", etc.
  args: TTerm[];      // Arguments to the tactic
};
```

---

## Elaboration & Type Checking Integration

### Elaboration of Tactic Blocks

When elaborating `{ tag: 'TacticBlock', tactics }`:

1. **Elaborate to TTK**: Keep tactic structure
2. **During type checking**: Execute tactics to build proof term
3. **Return**: The completed proof term (zonked)

```typescript
// In elabToKernelWithMap
case 'TacticBlock': {
  // Elaborate each tactic arg to TTK
  const elabTactics = term.tactics.tactics.map(cmd => ({
    name: cmd.name,
    args: cmd.args.map(arg => elabToKernelWithMap(arg, ...))
  }));

  return {
    tag: 'TacticBlock',
    tactics: { tag: 'TacticScript', tactics: elabTactics }
  };
}
```

### Type Checking Tactic Blocks

```typescript
// In checkType (src/compiler/checker.ts)

case 'TacticBlock': {
  // Create initial proof state
  const goalId = freshMetaName();
  const initialGoal: MetaVar = {
    ctx: env.context,
    type: expectedType,
    solution: undefined
  };

  let engine = new TacticEngine(
    { tag: 'Meta', id: goalId },
    new Map([[goalId, initialGoal]]),
    env.constraints,
    env.definitions,
    [goalId],
    0
  );

  // Execute tactics
  for (const tacticCmd of term.tactics.tactics) {
    const tactic = buildTactic(tacticCmd, env);
    const result = engine.applyTactic(tactic);

    if (!result.success) {
      throw env.error(`Tactic '${tacticCmd.name}' failed: ${result.error}`);
    }

    engine = result.newEngine;
  }

  // Check proof is complete
  if (!engine.isComplete()) {
    const unsolved = engine.getUnsolvedGoals();
    throw env.error(
      `Proof incomplete: ${unsolved.length} unsolved goal(s)\n` +
      unsolved.map((g, i) => `  ${i + 1}. ${prettyPrintTerm(g.type)}`).join('\n')
    );
  }

  // Zonk to get final proof term
  const proofTerm = engine.zonk();

  return env.withValue(proofTerm).withElaboratedTerm(proofTerm);
}
```

### Building Tactics from Syntax

```typescript
function buildTactic(cmd: TacticCommand, env: TCEnv): Tactic {
  switch (cmd.name) {
    case 'intro':
      const name = cmd.args[0]?.tag === 'Const'
        ? (cmd.args[0] as any).name
        : undefined;
      return new IntroTactic(name);

    case 'intros':
      // Parse names: intros A B C => ["A", "B", "C"]
      const names = cmd.args
        .filter(arg => arg.tag === 'Const')
        .map(arg => (arg as any).name);
      return new IntrosTactic(names.length > 0 ? names : undefined);

    case 'exact':
      if (cmd.args.length !== 1) {
        throw new Error('exact: expected 1 argument');
      }
      return new ExactTactic(cmd.args[0]);

    case 'apply':
      if (cmd.args.length !== 1) {
        throw new Error('apply: expected 1 argument');
      }
      return new ApplyTactic(cmd.args[0]);

    case 'assumption':
      return new AssumptionTactic();

    default:
      throw new Error(`Unknown tactic: ${cmd.name}`);
  }
}
```

---

## Testing Strategy

### Unit Tests for Tactics

File: `src/tactics/tactics.test.ts`

```typescript
describe('TacticEngine', () => {
  test('intro: introduces Pi binder', () => {
    // Goal: A -> B
    const goalType: TTKTerm = {
      tag: 'Pi',
      binder: { kind: 'explicit', name: 'x' },
      domain: { tag: 'Const', name: 'A' },
      body: { tag: 'Const', name: 'B' }
    };

    const engine = createInitialEngine(goalType);
    const result = engine.applyTactic(new IntroTactic('a'));

    expect(result.success).toBe(true);
    if (!result.success) return;

    const newGoal = result.newEngine.getFocusedGoal();
    expect(newGoal?.type).toEqual({ tag: 'Const', name: 'B' });
    expect(newGoal?.ctx).toHaveLength(1);
    expect(newGoal?.ctx[0].name).toBe('a');
  });

  test('exact: solves goal with term', () => {
    // Goal: Nat, context: [n : Nat]
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const context: TTKContext = [{ name: 'n', type: { tag: 'Const', name: 'Nat' } }];

    const engine = createEngineWithContext(goalType, context);
    const result = engine.applyTactic(new ExactTactic({ tag: 'Var', index: 0 }));

    expect(result.success).toBe(true);
    if (!result.success) return;

    expect(result.newEngine.isComplete()).toBe(true);
  });

  test('assumption: finds matching hypothesis', () => {
    const goalType: TTKTerm = { tag: 'Const', name: 'Nat' };
    const context: TTKContext = [
      { name: 'x', type: { tag: 'Const', name: 'Bool' } },
      { name: 'n', type: { tag: 'Const', name: 'Nat' } }
    ];

    const engine = createEngineWithContext(goalType, context);
    const result = engine.applyTactic(new AssumptionTactic());

    expect(result.success).toBe(true);
    if (!result.success) return;

    expect(result.newEngine.isComplete()).toBe(true);
  });

  test('apply: creates subgoals for function arguments', () => {
    // Goal: B
    // Context: [f : A -> B]
    // Apply f => subgoal: A
    const goalType: TTKTerm = { tag: 'Const', name: 'B' };
    const context: TTKContext = [{
      name: 'f',
      type: {
        tag: 'Pi',
        binder: { kind: 'explicit', name: 'x' },
        domain: { tag: 'Const', name: 'A' },
        body: { tag: 'Const', name: 'B' }
      }
    }];

    const engine = createEngineWithContext(goalType, context);
    const result = engine.applyTactic(
      new ApplyTactic({ tag: 'Var', index: 0 })
    );

    expect(result.success).toBe(true);
    if (!result.success) return;

    const unsolved = result.newEngine.getUnsolvedGoals();
    expect(unsolved).toHaveLength(1);
    expect(unsolved[0].type).toEqual({ tag: 'Const', name: 'A' });
  });
});
```

### Integration Tests (.tt files)

File: `src/test-programs/tactics/modus-ponens.tt`

```
-- @test success
-- @name "modusPonens via tactics"

modusPonens : {A B : Type} -> A -> (A -> B) -> B := by
  intro A
  intro B
  intro a
  intro f
  apply f
  exact a
```

File: `src/test-programs/tactics/id-via-tactics.tt`

```
-- @test success
-- @name "id via tactics with intros"

id : {A : Type} -> A -> A := by
  intros [A, x]
  exact x
```

File: `src/test-programs/tactics/const-via-tactics.tt`

```
-- @test success
-- @name "const via tactics with assumption"

const : {A B : Type} -> A -> B -> A := by
  intros [A, B, a, b]
  assumption
```

---

## Implementation Roadmap

### Milestone 1: Core Infrastructure (Week 1)

- [ ] Create `src/tactics/engine.ts` with `TacticEngine` class
- [ ] Create `src/tactics/tactic.ts` with `Tactic` interface
- [ ] Add helper utilities (fresh meta names, zonking with metas, etc.)
- [ ] Write unit tests for `TacticEngine` state management

### Milestone 2: Basic Tactics (Week 1-2)

- [ ] Implement `ExactTactic`
- [ ] Implement `AssumptionTactic`
- [ ] Implement `IntroTactic`
- [ ] Implement `IntrosTactic`
- [ ] Implement `ApplyTactic`
- [ ] Unit tests for each tactic

### Milestone 3: Parser & Syntax (Week 2)

- [ ] Add `TacticBlock` to TT types
- [ ] Implement `parseTacticBlock` in parser
- [ ] Implement `parseTacticCommand` in parser
- [ ] Add syntax tests

### Milestone 4: Elaboration & Type Checking (Week 2-3)

- [ ] Elaborate `TacticBlock` to TTK
- [ ] Implement `buildTactic` from syntax
- [ ] Integrate tactic execution into `checkType`
- [ ] Handle error reporting with proper context

### Milestone 5: End-to-End Testing (Week 3)

- [ ] Write `.tt` test for `modusPonens`
- [ ] Write `.tt` test for `id`
- [ ] Write `.tt` test for `const`
- [ ] Write `.tt` tests for failure cases (incomplete proofs, type mismatches)

### Milestone 6: Documentation & Polish (Week 3-4)

- [ ] Update `language-spec.md` with tactic syntax
- [ ] Update `SYSTEM_OVERVIEW.md` with tactics architecture
- [ ] Add examples to documentation
- [ ] Add IDE support (syntax highlighting, error messages)

### Future Enhancements

- [ ] `refine` tactic (exact with holes)
- [ ] `split` / `constructor` tactics
- [ ] `cases` / `induction` tactics
- [ ] `rewrite` tactic (equality reasoning)
- [ ] Tactic combinators (`<;>`, `try`, `repeat`, `<|>`)
- [ ] Tactic macros (user-defined tactics)
- [ ] Proof term extraction (for inspection/debugging)

---

## Comparison to Existing Systems

| Feature | Lean 4 | Coq | Idris 2 | LeanUI (Planned) |
|---------|--------|-----|---------|------------------|
| Goals as metavariables | ✅ MVarId | ✅ Evars | ✅ Holes | ✅ MetaVar |
| Immutable proof state | ✅ | ✅ (Proofview monad) | ✅ | ✅ TacticEngine |
| Typed tactics | ✅ TacticM | ✅ Ltac2/Mtac2 | ✅ Elab | ✅ Tactic interface |
| Integration with elaborator | ✅ Deep | ✅ Deep | ✅ Deep | ✅ Via checkType |
| Tactic combinators | ✅ Rich | ✅ Rich | ✅ Moderate | ⏳ Future |
| Proof term extraction | ✅ | ✅ | ✅ | ✅ (via zonk) |
| Custom tactics | ✅ Meta DSL | ✅ Ltac2/Gallina | ✅ Elab reflection | ⏳ Future |

---

## Open Questions

### 1. Named Arguments in Intro

Should `intro` support named parameters differently?

```
-- Function with named params:
f : {A : Type} -> {B : Type} -> A -> B

-- Does intro handle implicit binders automatically?
-- Option A: intro only handles explicit binders
f := by
  intro a
  intro b

-- Option B: intro handles all binders (implicit + explicit)
f := by
  intro A  -- implicit
  intro B  -- implicit
  intro a  -- explicit
  intro b  -- explicit
```

**Decision**: Start with Option B (handle all binders). User can skip with `intros` bulk command.

### 2. How to Handle Universe Levels?

Universe level metavariables are separate from term metavariables. Do tactics need to interact with them?

**Decision**: For MVP, tactics don't directly manipulate level metas. The constraint solver handles them automatically.

### 3. Should Tactic Execution be Lazy or Eager?

**Lazy**: Tactics build a tactic tree, executed later.
**Eager**: Tactics execute immediately, building the term as we go.

**Decision**: Eager execution (like Lean 4). Simpler to implement, better error messages.

### 4. Error Recovery

If a tactic fails midway through a sequence, should we:
- A) Fail the entire proof
- B) Return partial state for inspection
- C) Support backtracking (try alternative tactics)

**Decision**: (A) for MVP. (C) as future enhancement (tactic combinators like `<|>`).

---

## References

- [Lean 4 Metaprogramming Book - Tactics](https://leanprover-community.github.io/lean4-metaprogramming-book/main/09_tactics.html)
- [Coq Proof Engine Documentation](https://github.com/coq/coq/blob/master/dev/doc/proof-engine.md)
- [Mtac2: Typed Tactics for Backward Reasoning in Coq](https://iris-project.org/pdfs/2018-icfp-mtac2-final.pdf)
- [Idris 2 Implementation Overview](https://idris2.readthedocs.io/en/latest/implementation/overview.html)
- [Idris Elaborator Reflection](https://docs.idris-lang.org/en/latest/elaboratorReflection/elaborator-reflection.html)
- [Compositional Pre-processing for Automated Reasoning in Dependent Type Theory (CPP 2023)](https://dl.acm.org/doi/abs/10.1145/3573105.3575676)
- [The Lean 4 Theorem Prover and Programming Language](https://lean-lang.org/papers/lean4.pdf)

---

## Next Steps

1. **Review this plan** with stakeholders
2. **Start Milestone 1**: Build `TacticEngine` infrastructure
3. **Iterate**: Get feedback early and often
4. **Keep it simple**: MVP first, enhancements later

**CRITICAL**: Stick to established algorithms from Lean/Coq/Idris. No ad-hoc inventions. When in doubt, research first.
