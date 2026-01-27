# LeanUI System Overview

This document provides a comprehensive overview of the LeanUI type checker, from source code to fully checked terms.

## Table of Contents

1. [Architecture Overview](#architecture-overview)
2. [Term Representation Layers](#term-representation-layers)
3. [Compilation Pipeline](#compilation-pipeline)
4. [Parsing](#parsing)
5. [Elaboration (TT → TTK)](#elaboration-tt--ttk)
6. [Type Checking](#type-checking)
7. [Pattern Matching](#pattern-matching)
8. [Metas and Constraint Solving](#metas-and-constraint-solving)
9. [Unification](#unification)
10. [Substitution and De Bruijn Indices](#substitution-and-de-bruijn-indices)
11. [WHNF Normalization](#whnf-normalization)
12. [Totality Checking](#totality-checking)
13. [Structural Recursion Checking](#structural-recursion-checking)
14. [Key Invariants](#key-invariants)
15. [Ideas for Hardening / Refactoring / Improving](#ideas-for-hardening--refactoring--improving)

---

## Architecture Overview

LeanUI implements a dependently-typed language with:
- **Bidirectional type checking** (inference and checking modes)
- **Pattern matching** with totality and termination checking
- **Implicit arguments** with automatic insertion
- **Universe polymorphism** with level inference
- **Let bindings** with type inference (no generalization)

The system follows a layered architecture:

```
Source Text
    ↓
[PARSING] Parser + Indentation Grouper
    ↓
TT (Surface Syntax) + SourceMap
    ↓
[ELABORATION] elabToKernelWithMap
    ↓
TTK (Kernel Syntax) + ElabMap
    ↓
[TYPE CHECKING] checkType / inferType
    ↓
Checked TTK + Solved Metas
    ↓
[VERIFICATION] Totality + Recursion
    ↓
CompiledDeclaration
```

---

## Term Representation Layers

### TT (Typed Terms - Surface)

**Location**: `src/types/tt-core.ts`

Surface-level representation that may include syntactic sugar:
- Named variable references (before de Bruijn conversion)
- Record extension syntax
- User-written holes (`_` or `?name`)
- Named argument syntax `{name := value}`

**Types**: `TTerm`, `TPattern`, `TClause`, `BinderKind`

### TTK (Typed Terms - Kernel)

**Location**: `src/types/tt-kernel.ts`

Elaborated/desugared form - the "ground truth" for verification:
- De Bruijn indices for variables
- Inlined record extensions
- Holes converted to Metas
- Reordered arguments (named → positional)

**Types**: `TTKTerm`, `TTKClause`, `TTKBinderKind`, `TTKContext`

### Key Rule

**All verification happens on TTK, not TT.** Type checking, unification, termination checking, and all other verification must operate on `TTKTerm`.

---

## Compilation Pipeline

### Entry Point

```typescript
// src/compiler/compile.ts
compileTTFromText(source: string): CompileResult
```

### Pipeline Steps

```
compileTTFromText(source)
  │
  ├─ parseTTSource(source)
  │   ├─ Indentation grouping (blocks)
  │   └─ Parser.parseDeclarationsWithSource()
  │
  └─ For each declaration:
      │
      ├─ Name Resolution
      │   └─ validateDeclarations() → SymbolContext
      │
      ├─ Pattern Resolution
      │   └─ resolvePatternsInDeclarations() → PCtor vs PVar
      │
      ├─ Elaboration (TT → TTK)
      │   └─ elabToKernelWithMap() → TTKTerm + ElabMap
      │
      ├─ Type Checking
      │   ├─ For inductive types: checkInductiveDeclaration()
      │   ├─ For terms: checkType() / inferType()
      │   └─ For pattern matching: checkMatchClause()
      │
      └─ Verification
          ├─ checkTotality() → Coverage analysis
          └─ checkStructuralRecursion() → Termination
```

---

## Parsing

**Location**: `src/parser/parser.ts`

### Parser Features

- **Pratt parser** for operator precedence
- **Indentation-sensitive** block grouping
- **Source mapping** for error locations

### Supported Syntax

| Construct | Syntax |
|-----------|--------|
| Lambda | `\x => body`, `\(x : T) => body` |
| Pi type | `(x : T) -> body`, `T -> U` |
| Let | `let x = v in body`, `let x : T = v in body` |
| Multi-let | `let x = v, y = w in body` |
| Application | `f x y` |
| Implicit args | `{x}`, `{name := value}` |
| Match | `match e with \| p1 => r1 \| p2 => r2` |
| Inductive | `inductive Name : Type where \| Ctor : T` |
| Holes | `_`, `?name` |

### Output

```typescript
interface ParsedDeclaration {
  name?: string;
  kind: 'inductive' | 'term';
  type?: TTerm;          // Surface type annotation
  value?: TTerm;         // Surface value (may contain Match)
  constructors?: Array<{ name: string; type: TTerm }>;
}
```

---

## Elaboration (TT → TTK)

**Location**: `src/compiler/elab.ts`

### Entry Point

```typescript
elabToKernelWithMap(
  term: TTerm,
  elabMap: ElabMap,
  surfacePath: IndexPath,
  kernelPath: IndexPath,
  ...
): TTKTerm
```

### Elaboration Tasks

1. **De Bruijn conversion**: Named vars → indices
2. **Record inlining**: Expand `extends` clauses
3. **Named arg reordering**: `{a := 1}` → positional slot
4. **Implicit filling**: Insert Holes for omitted implicits
5. **Let type holes**: `let x = v` → `let x : Hole = v`
6. **Pattern elaboration**: TPattern → TTKPattern with generated names

### ElabMap

Maps kernel AST paths to surface AST paths for error reporting:

```typescript
type ElabMap = Map<string, string>  // kernelPath → surfacePath
```

---

## Type Checking

**Location**: `src/compiler/checker.ts`

### Bidirectional Type Checking

```typescript
// Checking mode: verify term has expected type
checkType(env: TCEnv<TTKTerm>, expected: TTKTerm): TCEnv<TTKTerm>

// Inference mode: synthesize type of term
inferType(env: TCEnv<TTKTerm>): TCEnv<TTKTerm>
```

### Type Checking Rules

#### VAR - Variable Lookup
```
(x : T) ∈ Γ
─────────────
Γ ⊢ x ⇒ T
```

The type is looked up from the context and shifted to the current scope.

#### CONST - Definition Lookup
```
(c : T) ∈ Σ
─────────────
Γ ⊢ c ⇒ T
```

#### SORT - Universe Hierarchy
```
─────────────────────────
Γ ⊢ Type_i ⇒ Type_(i+1)
```

#### PI - Dependent Function Type
```
Γ ⊢ A ⇐ Type_i
Γ, x : A ⊢ B ⇐ Type_j
─────────────────────────
Γ ⊢ Π(x : A). B ⇒ Type_max(i,j)
```

#### LAM - Lambda Abstraction
```
Γ ⊢ A ⇐ Type
Γ, x : A ⊢ t ⇒ B
─────────────────────────
Γ ⊢ λ(x : A). t ⇒ Π(x : A). B
```

- Domain can be a Hole (becomes Meta, inferred from usage)
- Body type inferred with context extended by **elaborated domain**

#### APP - Function Application
```
Γ ⊢ f ⇒ Π(x : A). B
Γ ⊢ e ⇐ A
─────────────────────────
Γ ⊢ f e ⇒ B[x := e]
```

- Argument checked in **original context** (not extended)
- Implicit arguments inserted automatically for named parameters

#### LET - Let Binding with Type Inference
```
Γ ⊢ A ⇐ Type_i            (or Hole → Meta for inference)
Γ ⊢ v ⇐ A
Γ, x : A ⊢ body ⇒ B'
B = [x := v]B'            (substitute if B' references x, else shift)
─────────────────────────────────────────────────────────────────
Γ ⊢ let x : A := v in body ⇒ B
```

**Key behaviors**:
1. When type annotation is a Hole, it becomes a Meta
2. Checking the value against the Meta generates constraints
3. Constraints are solved **before** entering the body
4. Body type is **strengthened** when exiting scope:
   - If body type references the let variable: substitute value
   - Otherwise: shift de Bruijn indices by -1

#### CONV - Conversion Rule
```
Γ ⊢ t ⇒ T'
T ≃ T'
─────────────────────
Γ ⊢ t ⇐ T
```

Definitional equality checked via WHNF reduction and unification.

### TCEnv - Type Checking Environment

**Location**: `src/compiler/term.ts`

```typescript
class TCEnv<T> {
  context: TTKContext           // De Bruijn stack: index 0 = most recent
  definitions: DefinitionsMap   // Global term & inductive definitions
  metaVars: Map<string, MetaVar>  // Unsolved metavariables
  constraints: Constraint[]     // Pending constraints
  indexPath: IndexPath          // Current AST location
  valueStack: unknown[]         // Term navigation stack
  value: T                      // Current term being checked
  levelMetas: Map<string, LevelMeta>  // Universe level variables
  options: TCEnvOptions         // Mode: 'pattern' | 'check'
  elaboratedTerm?: TTKTerm      // Elaborated term (Holes → Metas)
}
```

### Key Methods

| Method | Purpose |
|--------|---------|
| `withValue(v)` | Replace current term |
| `extendTTKContext(name, type)` | Add variable binding |
| `solveMetasAndConstraints()` | Resolve constraints |
| `zonkTerm(term)` | Substitute solved metas |
| `createMetaForHole(type)` | Create fresh meta |

---

## Pattern Matching

**Location**: `src/compiler/patterns.ts`

### Entry Point

```typescript
checkMatchClause(
  termName: string,
  env: TCEnv<TTKClause>,
  type: TTKTerm,
  namedArgMap?: NamedArgMap,
  totalArity?: number
): TCEnv<TTKClause>
```

### Pattern Types

```typescript
type TTKPattern =
  | { tag: 'PVar'; name: string }      // User-named variable
  | { tag: 'PWild'; name: string }     // Wildcard (generated name)
  | { tag: 'PCtor'; name: string; args: TTKPattern[] }  // Constructor
```

### LHS Processing Flow

```
Surface patterns
    │
    ├─ Named pattern reordering
    ├─ Implicit slot filling (wildcards)
    └─ Pattern resolution (PVar vs PCtor)
    │
    ↓
Kernel patterns
    │
    ├─ unifyMatchClauseLhs()
    │   ├─ Process each pattern against type
    │   ├─ For PVar: bind variable in context
    │   ├─ For PWild: create meta + constraint
    │   ├─ For PCtor: unify with constructor type
    │   └─ Build elaboration stack
    │
    └─ Apply unification result
        ├─ Extend context with bindings
        ├─ Apply substitutions to RHS
        └─ Convert RHS from levels → de Bruijn
```

### RHS Checking

The RHS is checked in the extended context with pattern bindings. The expected type is the **return type** after processing all patterns.

**Important**: The RHS is converted from "level" representation (for pattern unification) back to de Bruijn indices using `levelsToDeBruijn(rhs, contextLength)`.

---

## Metas and Constraint Solving

**Location**: `src/compiler/meta.ts`

### MetaVar Structure

```typescript
type MetaVar = {
  ctx: TTKContext      // Context where meta was created
  type: TTKTerm        // Expected type of solution
  solution?: TTKTerm   // Solved value (once unified)
}
```

### Constraint Structure

```typescript
type Constraint = {
  ctx: TTKContext      // Context where constraint created
  meta: string         // Meta name: "?m0", "?m1", etc.
  rhs: TTKTerm         // Proposed solution
  rhsType?: TTKTerm    // Optional: type of rhs
}
```

### Meta Creation Points

1. **Elaboration**: Holes in source → Metas
2. **Type checking**: Fresh metas for unannotated lambda domains
3. **Let inference**: Fresh metas for omitted let type annotations
4. **Universe levels**: Level metas for implicit universe parameters

### Constraint Solving

```typescript
solveConstraints(
  metaVars: Map<string, MetaVar>,
  constraints: Constraint[],
  liftContext?: TTKContext
): { constraints: Constraint[], metaVars: Map<string, MetaVar> }
```

**Algorithm**:
1. For each constraint `?m = rhs`:
   - **Occurs check**: Prevent `?m` in `rhs` (no cycles)
   - **Scope check**: All free vars of `rhs` must be in context
   - **Conflict check**: If already solved, verify compatibility
   - **Set solution**: `metaVars[?m].solution = rhs`
2. Return remaining unsolved constraints

### Zonking

"Zonking" (GHC terminology) substitutes solved metas with their solutions:

```typescript
zonkTerm(term: TTKTerm): TTKTerm
```

Recursively traverses the term, replacing any `Meta` that has a solution.

---

## Unification

**Location**: `src/compiler/unify.ts`

### Entry Point

```typescript
unifyTerms(t1: TTKTerm, t2: TTKTerm, options: UnifyOptions): UnifyResult
```

### Options

```typescript
type UnifyOptions = {
  flexibleVars?: boolean      // Can vars be substituted? (pattern mode)
  rigidVarsAtOrAbove?: number // Vars >= this index are rigid
  mode: 'pattern' | 'check'   // Matching or general unification
  definitions?: DefinitionsMap // For delta-reduction
  fuel?: number               // Reduction limit (default 1000)
}
```

### Algorithm

1. **WHNF reduce** both terms
2. **Compare heads**:
   - `Const` vs different `Const` → conflict
   - `Meta` → generate constraint
   - Flexible `Var` → generate substitution
   - Rigid `Var` vs different `Var` → conflict
3. **Recurse** into structure (domain, body, args)

### Result

```typescript
type UnifyResult =
  | { success: true;
      substitutions: [varIndex, replacement][];
      metaConstraints: { meta: string; rhs: TTKTerm }[];
      levelConstraints: { lmvar: string; rhs: TTKTerm }[];
    }
  | { success: false; reason: 'conflict' | 'cycle' }
```

---

## Substitution and De Bruijn Indices

**Location**: `src/compiler/subst.ts`

### De Bruijn Convention

Variables are identified by binding distance:
- Index 0 = most recently bound variable
- Index increases going outward

Context representation:
```typescript
type TTKContext = Array<{ name: string; type: TTKTerm }>
// Stored oldest-first, so context[length-1-index] gives entry for de Bruijn index
```

### Substitution

```typescript
subst(index: number, replacement: TTKTerm, term: TTKTerm): TTKTerm
```

Replace variable at `index` with `replacement`:
- `Var i` where `i == index + depth` → replace (shifted by depth)
- `Var i` where `i > index + depth` → decrement (removing a binder)
- Recurse into binders with `depth + 1`

### Shifting

```typescript
shiftTerm(term: TTKTerm, delta: number, cutoff: number): TTKTerm
```

Adjust de Bruijn indices when changing context size:
- `delta > 0`: Context grew (entering scope)
- `delta < 0`: Context shrunk (exiting scope)
- Only shift variables with index >= cutoff

### Helper Functions

| Function | Purpose |
|----------|---------|
| `minFreeVarIndex(term)` | Lowest de Bruijn index with free var |
| `containsVarIndex(term, i)` | Does term contain free var i? |
| `freeVarIndices(term)` | All free variable indices |

---

## WHNF Normalization

**Location**: `src/compiler/whnf.ts`

### Weak Head Normal Form

```typescript
whnf(term: TTKTerm, ctx?: WhnfContext): TTKTerm
```

Reduce until head is irreducible:
- **β-reduction**: `(λx. t) e → t[x := e]`
- **ζ-reduction**: `let x := v in t → t[x := v]`
- **δ-reduction**: Unfold definitions (controlled by options)
- **ι-reduction**: Pattern match when scrutinee matches clause

**Does NOT reduce**:
- Under binders (λ, Π, let bodies)
- Function arguments
- Match arms (only scrutinee)

### Full Normalization

```typescript
normalize(term: TTKTerm): TTKTerm
```

Recursively reduces all redexes everywhere (for pretty printing).

### Definitional Equality

```typescript
areTypesDefEq(t1: TTKTerm, t2: TTKTerm, env: TCEnv): boolean
```

1. Reduce both to WHNF
2. Compare heads structurally
3. Recurse through structure

---

## Totality Checking

**Location**: `src/compiler/totality.ts`

### Entry Point

```typescript
checkTotality(
  clauses: TTKClause[],
  checkAbsurdity: AbsurdityChecker,
  definitions: DefinitionsMap
): TotalityResult
```

### Case Tree

```typescript
type CaseTree =
  | { tag: 'Leaf'; clauseIndex: number }
  | { tag: 'Split'; typeName: string; branches: Map<string, CaseTree>; ... }
  | { tag: 'Uncovered' }
  | { tag: 'Absurd' }
```

### Algorithm

1. **Build trie** by walking patterns left-to-right, depth-first
2. **Split branches** for each constructor
3. **Detect uncovered** leaves (no matching clause)
4. **Check absurdity** (can contradictory patterns exist?)
5. **Detect unreachable** clauses

### Result

```typescript
interface TotalityResult {
  caseTree: CaseTree | null;
  unreachableClauses: { clauseIndex: number; patterns: TTKPattern[] }[];
  isExhaustive: boolean;
  missingValidClauses: { patterns: TTKPattern[] }[];
  missingAbsurdClauses: { patterns: TTKPattern[] }[];
}
```

---

## Structural Recursion Checking

**Location**: `src/compiler/recursion.ts`

### Entry Point

```typescript
checkStructuralRecursion(
  name: string,
  clauses: TTKClause[],
  definitions: DefinitionsMap
): StructuralRecursionResult
```

### Algorithm

1. For each clause, build **structurally smaller map**:
   - Variables bound inside `PCtor` are smaller than the pattern position
2. Find **recursive call sites** in RHS
3. Verify at least one argument is **structurally smaller**

### Structural Ordering

In pattern `f (Succ n) = ...`:
- `n` is structurally smaller than argument position 0
- Recursive call `f n` is valid (n < Succ n)

---

## Key Invariants

1. **All checking on TTK**: Type checking, unification, totality operate on kernel terms only

2. **De Bruijn scoping**: Variables identified by distance, context is stack with index 0 = most recent

3. **Substitution order**: Apply substitutions in descending index order to avoid shifting issues

4. **Context extension**:
   - Lambda/let bodies: extended by elaborated domain
   - Pattern RHS: extended by pattern bindings
   - Argument checking: **original context** (not extended)

5. **Meta solving**:
   - Occurs check prevents cycles
   - Free vars must be in meta's context
   - Zonking substitutes solutions

6. **Unification modes**:
   - Pattern mode: vars are flexible
   - Check mode: vars are rigid skolems

7. **Let type strengthening**: When exiting let scope, body type must be adjusted:
   - If references let var: substitute value
   - Otherwise: shift by -1

8. **Map correspondence**:
   - `ElabMap`: kernel paths → surface paths
   - `SourceMap`: surface paths → file positions

---

## Ideas for Hardening / Refactoring / Improving

### High Priority

#### 1. Constraint De Bruijn Shifting Bug (Potential)

**Location**: `src/compiler/meta.ts:195`

When `liftMetasToFullContext: true`, the constraint RHS is stored without shifting:

```typescript
newMetaVars.set(constraint.meta, { ...meta, solution: constraint.rhs, ctx: effectiveContext });
```

If `constraint.rhs` contains de Bruijn indices relative to `constraint.ctx` (length N), but `effectiveContext` has length M > N, those indices may refer to wrong variables. The RHS should potentially be shifted by `M - N`.

**Recommendation**: Review all uses of `liftMetasToFullContext: true` and add shifting if needed.

#### 2. Remove `mkMeta` Direct Creation

**Location**: Various files still use `mkMeta()` directly

All meta creation should go through `TCEnv.createMetaForHole()` or similar to ensure metas are properly registered. Direct `mkMeta()` can create "orphan" metas not in the metaVars map.

**Recommendation**: Audit and remove direct `mkMeta()` calls, route through TCEnv methods.

#### 3. Error Message Context Loss

When errors are thrown deep in the call stack, context information (like current term, expected type) can be lost. The `wrappedBy()` pattern helps but isn't consistently applied.

**Recommendation**: Create a consistent error context protocol, perhaps using a context stack.

### Medium Priority

#### 4. TCEnv Immutability Overhead

`TCEnv` is immutable with many `with*` methods creating new instances. This is clean but may have performance overhead for deep type checking.

**Recommendation**: Profile hot paths; consider mutable builder pattern for performance-critical sections.

#### 5. Unify Fuel Exhaustion Handling

When WHNF reduction hits fuel limit (default 1000), unification fails silently. This could mask real issues.

**Recommendation**: Add warning/logging when fuel is exhausted; consider exponential backoff or user-configurable limits.

#### 6. Pattern Matching Elaboration Complexity

`checkMatchClause` does many things: padding, reordering, LHS unification, RHS checking, level conversion. This is difficult to follow and test.

**Recommendation**: Extract sub-phases into separate functions with clear interfaces.

#### 7. Level Representation Duplication

Levels are sometimes `TTKTerm` (general terms) and sometimes special-cased. The `ULit`, `ULevel`, `UOmega` tags create complexity.

**Recommendation**: Consider a cleaner level algebra with dedicated types.

### Low Priority / Future Enhancements

#### 8. Incremental Type Checking

Currently, changing one declaration re-checks everything after it. For large codebases, incremental checking would improve IDE responsiveness.

**Recommendation**: Track dependencies between declarations; invalidate only affected declarations.

#### 9. Better Totality Diagnostics

The case tree is built but not fully exploited for user feedback. Could show:
- Specific uncovered patterns with examples
- Why a clause is unreachable
- Suggested fixes

**Recommendation**: Enhance `TotalityResult` with richer diagnostic information.

#### 10. Proof Term Generation

The system checks types but doesn't generate proof terms (elaborated terms with all implicits filled). This would enable:
- Proof export to other systems
- Runtime interpretation
- Proof replay

**Recommendation**: Thread elaboration through all phases; output fully explicit terms.

#### 11. Universe Inference Improvements

Level inference works but can be fragile with complex constraints. Consider:
- Better error messages for level conflicts
- Visualization of level constraints
- Optional explicit universe polymorphism syntax

#### 12. Test Coverage for Edge Cases

The test suite is good but could use more tests for:
- Nested let with dependent types
- Complex pattern matching with refinement
- Level constraint edge cases
- Error recovery scenarios

**Recommendation**: Add property-based testing with generated terms.

### Code Quality

#### 13. Reduce File Sizes

Some files are very large:
- `compile.ts`: ~2600 lines
- `patterns.ts`: ~1250 lines
- `elab.ts`: ~2500 lines

**Recommendation**: Split into focused modules (e.g., `compile-inductive.ts`, `compile-term.ts`).

#### 14. Documentation Comments

Many internal functions lack documentation. The type system helps, but intent and invariants should be documented.

**Recommendation**: Add JSDoc comments to key functions, especially invariants.

#### 15. Logging Consistency

Logging is controlled by various `setXLoggingEnabled()` functions. This is scattered and hard to manage.

**Recommendation**: Centralize logging configuration; consider structured logging for debugging.
