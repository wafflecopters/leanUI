# Type Checking with Meta-Variables

Based on Norell & Coquand's "Type checking in the presence of meta-variables"

## Terms (using de Bruijn indices)

```typescript
type Term =
  | { tag: 'Var'; index: number }
  | { tag: 'Sort'; level: number }                         // Type_i, Prop = Type_0
  | { tag: 'Binder'; name: string; binderKind: BinderKind; domain: Term; body: Term }
  | { tag: 'App'; fn: Term; arg: Term }
  | { tag: 'Const'; name: string; type: Term }             // Named constant (constructors, etc.)
  | { tag: 'Hole'; id: string; type: Term; context: Context }
  | { tag: 'Annot'; term: Term; type: Term }
  | { tag: 'Match'; scrutinee: Term; clauses: Clause[] }

type Pattern =
  | { tag: 'PVar'; name: string }
  | { tag: 'PCtor'; name: string; args: Pattern[] }

type Clause = { patterns: Pattern[]; rhs: Term }

type BinderKind =
  | { tag: 'BPi' }                      // Π-binder (dependent function type)
  | { tag: 'BLam' }                     // λ-binder (function abstraction)
  | { tag: 'BLet'; defVal: Term }       // let-binder (local definition)
```

Note: In this system, there is no term/type distinction — types are terms. A Pi type is just a `Binder` with `binderKind: {tag: 'BPi'}`.

We use de Bruijn **levels** internally during elaboration for stability as context grows. Level `l` in context of length `n` converts to index `n - l - 1`.

## State

```typescript
type State = {
  Γ: Array<{name: string, type: Term}>,  // context: name + type, position = level
  Σ: Map<string, MetaEntry>,              // meta-variable solutions (keyed by Hole id)
  C: Constraint[],                        // unsolved constraints
  P: Array<Pattern | DONE>,               // patterns to process
  T: Array<Term>,                         // types to check against (must be Pi-shaped or final)
  E: Array<Term>,                         // elaborated terms (using levels)
  nextMeta: number                        // fresh meta counter
}

type MetaEntry = {
  telLen: number,           // telescope length (context size when created)
  ty: Term,                 // type of the meta
  sol: Term | null          // solution (if solved)
}

type Constraint = {
  ctx: Array<{name: string, type: Term}>,  // context where constraint lives
  meta: string,                             // which meta (Hole id)
  rhs: Term                                 // what meta should equal
}

type DONE = { tag: 'DONE', pattern: Pattern, arity: number }
```

## Operations

### Bind variable of type A with name x

```typescript
Γ.push({name: x, type: A})
// new variable has level Γ.length - 1
```

### Fresh meta of type A

```typescript
const id = `?m${nextMeta++}`
Σ.set(id, {telLen: Γ.length, ty: A, sol: null})
// elaborated term is Hole with id, applied to context vars
// or built as nested App(Hole(...), #0), App(..., #1), ...
```

### Current variable as term (using levels)

```typescript
// just bound a variable, it has level Γ.length - 1
// as a term with level: Var(Γ.length - 1)
// will convert to index 0 when done
```

### Apply substitution Var(l) = t

```typescript
// remove level l from Γ
// in all of Γ's types, T, C's rhs, E: 
//   replace Var(l) with t
//   decrement all levels > l
```

## Main Loop

```typescript
while (P.length > 0) {
  const top = P[P.length - 1]
  if (top.tag === 'DONE') {
    constructorDone(top.pattern, top.arity)
  } else {
    processPattern(P.pop()!)
  }
}

// When P is empty and T = [expectedType]:
//   process RHS
```

## Process Pattern

```typescript
const pat = P.pop()!
const piType = T.pop()!  // must be Binder with BPi

// Extract domain A and body B from Pi type
// piType = {tag: 'Binder', binderKind: {tag: 'BPi'}, domain: A, body: B, ...}

switch (pat.tag) {
  case 'PVar': {
    // 1. Bind: 
    Γ.push({name: pat.name, type: A})
    // 2. Record:
    E.push(Var(Γ.length - 1))  // using levels
    // 3. Push codomain:
    T.push(B)  // B may reference the new binding
    break
  }
  
  case 'PCtor': {
    // pat = {tag: 'PCtor', name, args: [p1, ..., pn]}
    
    // 1. Look up constructor type:
    //    Con : (C1) -> ... -> (Cn) -> ReturnType
    
    // 2. Push marker:
    P.push({tag: 'DONE', pattern: pat, arity: pat.args.length})
    
    // 3. Push sub-patterns (reversed):
    for (let i = pat.args.length - 1; i >= 0; i--) {
      P.push(pat.args[i])
    }
    
    // 4. Push constructor type:
    T.push(constructorType)
    break
  }
}
```

**Note on holes in patterns:** A hole like `_w5` is treated as a `PVar` that also creates a meta. When we see a hole pattern:

```typescript
// For hole pattern with name h:
// 1. Create meta:
const id = `?m${nextMeta++}`
Σ.set(id, {telLen: Γ.length, ty: A, sol: null})

// 2. Bind:
Γ.push({name: h, type: A})

// 3. Add constraint:
C.push({ctx: [...Γ], meta: id, rhs: Var(Γ.length - 1)})

// 4. Record:
E.push(Var(Γ.length - 1))

// 5. Push codomain:
T.push(B)
```

## Constructor Done

```typescript
const done = P.pop()!  // {tag: 'DONE', pattern: pat, arity: n}
// pat = {tag: 'PCtor', name, args: [p1, ..., pn]}

const returnType = T.pop()!  // must be non-Pi (e.g., Vec A n)
const piType = T[T.length - 1]  // peek: must be Pi (parent's remaining type)
// piType.domain is what we unify against

// 1. Shift both sides to current context before unifying
const shiftedReturnType = shiftTerm(returnType, Γ.length - returnTypeCtxLen, 0)
const shiftedDomain = shiftTerm(piType.domain, Γ.length - piTypeCtxLen, 0)

// 2. Unify
const unifyResult = unify(shiftedReturnType, shiftedDomain)
//   - yields equations [(varIndex, term), ...] and meta constraints

// 3. Apply each substitution to ALL state, one by one
//    Order matters: each substitution affects indices in subsequent ones
for (const {varIndex, value} of enumerateAppliedSubstitutions(unifyResult.equations)) {
  const mainSigLength = Γ.length
  
  // Update context (removes variable, adjusts types)
  Γ = applySubstitutionToContext(Γ, varIndex, value)
  
  // Update check stack (T)
  T = applySubstitutionToCheckStack(T, mainSigLength, varIndex, value)
  
  // Update elab stack (E) - note: E uses levels, not indices
  E = applySubstitutionToElabStack(E, mainSigLength, varIndex, value)
  
  // Update constraints
  C = applySubstitutionToConstraints(C, mainSigLength, varIndex, value)
  
  // Update meta-variables
  Σ = applySubstitutionToMetaVars(Σ, mainSigLength, varIndex, value)
}

// 4. Add new meta constraints from unification
for (const [metaId, rhs] of unifyResult.metaConstraints) {
  C.push({ctx: [...Γ], meta: metaId, rhs})
}

// 5. Build elaborated term:
//    Pop n terms from E, convert from levels to indices
const args: Term[] = []
for (let i = 0; i < n; i++) {
  args.unshift(E.pop()!)  // pop n terms, reverse order
}
const argsWithIndices = args.map(t => levelToIndex(t, Γ.length))
const elaborated = buildConst(pat.name, argsWithIndices)
E.push(elaborated)

// 6. Continue:
T.pop()  // remove the Pi
T.push(substitute(piType.body, elaborated))  // push codomain with subst

// 7. Try solve constraints (now that all state is updated)
solveConstraints()
```

## Solve Constraints

```typescript
function solveConstraints() {
  C = C.filter(constraint => {
    const {meta, rhs} = constraint
    const entry = Σ.get(meta)!
    const k = entry.telLen
    
    // Check: are all free variable levels in rhs < k?
    if (allLevelsBelow(rhs, k)) {
      entry.sol = rhs
      return false  // remove from C
    }
    return true  // keep in C (stuck)
  })
}

function allLevelsBelow(term: Term, k: number): boolean {
  // Returns true if all Var levels in term are < k
  // i.e., the term only references variables in the meta's telescope
}
```

## Re-lift Stuck Constraints

At the end, for stuck constraints:

```typescript
function reliftConstraints() {
  for (const constraint of C) {
    const entry = Σ.get(constraint.meta)!
    entry.telLen = Γ.length  // extend telescope to full context
    entry.sol = constraint.rhs  // now solvable
  }
  C = []  // all resolved
}
```

## RHS Processing

When P is empty, T should be `[expectedType]`.

For RHS application `App(App(...App(f, a1), a2)..., an)`:

```typescript
// Flatten to get function and args: f, [a1, ..., an]
// Push args (reversed):
for (let i = args.length - 1; i >= 0; i--) {
  P.push(termToPattern(args[i]))  // convert term to pattern-like
}
// Look up f's type and push:
T.push(typeOf(f))
```

### Variable on RHS

```typescript
// Find variable's level l and type A_l in Γ
const {level: l, type: A_l} = lookupVar(varName)

// Pop T -> must be Pi
const piType = T.pop()!

// Unify: A_l with piType.domain
const result = unify(A_l, piType.domain)
// Process equations and meta constraints...

// Record:
E.push(Var(l))

// Push codomain:
T.push(piType.body)
```

### Hole on RHS

```typescript
// Pop T -> must be Pi
const piType = T.pop()!
const A = piType.domain

// Create meta:
const id = `?m${nextMeta++}`
Σ.set(id, {telLen: Γ.length, ty: A, sol: null})

// Build applied meta (Hole applied to all context vars):
const spine = buildSpine(Γ.length)  // [#0, #1, ..., Var(n-1)]
const appliedMeta = applyToSpine(Hole(id, A, Γ), spine)

// Record:
E.push(appliedMeta)

// Push codomain (with meta application substituted):
T.push(substitute(piType.body, appliedMeta))

// No constraint yet; constraints come from unification later
```

### Application Done on RHS

Same as Constructor Done, but we're building `App(f, args)` instead of `Const`.

### RHS Finished

When P empty again:

```typescript
const inferredType = T.pop()!
const expectedType = T.pop()!
unify(inferredType, expectedType)
// Process any resulting equations/constraints
```

## Unify

```typescript
type UnifyResult = {
  equations: Array<[number, Term]>,      // [(level, term), ...] - substitutions
  metaConstraints: Array<[string, Term]> // [(metaId, rhs), ...] - meta constraints
}

type UnifyError = 'Conflict' | 'Cycle'

function unify(a: Term, b: Term): UnifyResult | UnifyError
```

### Unification Rules (from "Pattern Matching without K")

| Rule | LHS | RHS | Result |
|------|-----|-----|--------|
| Deletion | `t` | `t` | success (no equations) |
| Substitution | `Var(l)` | `t` | `[(l, t)]` if `l ∉ FV(t)` |
| Cycle | `Var(l)` | `t` | fail if `l ∈ FV(t)` and `t ≠ Var(l)` |
| Conflict | `Const(c, _)` | `Const(d, _)` | fail if `c ≠ d` |
| Injectivity | `Const(c, as)` | `Const(c, bs)` | unify `as` with `bs` pairwise |
| Meta | `App(...Hole(α)..., spine)` | `t` | meta constraint `(α, t)` |

The unification must handle the nested `App` structure for both constructors and meta applications.

---

# Example: `nth` Function

## Signature

```
Vec   : Type -> Nat -> Type
Fin   : Nat -> Type
VCons : (A:Type) -> (n:Nat) -> A -> Vec A n -> Vec A (Succ n)
FSucc : (n:Nat) -> Fin n -> Fin (Succ n)
Succ  : Nat -> Nat
nth   : (A:Type) -> (n:Nat) -> Vec A n -> Fin n -> A
```

## Clause

```
nth A _w5 (VCons _w6 (Succ _w7) h tail) (FSucc _w8 f) = nth _w9 _w10 tail f
```

Where `_w5`, `_w6`, etc. are holes (implicit arguments to infer).

---

## Trace

### Initial

```
Γ = []
Σ = {}
C = []
P = [(FSucc _w8 f), (VCons _w6 (Succ _w7) h tail), _w5, A]
T = [(A:Type) -> (n:Nat) -> Vec A n -> Fin n -> A]
E = []
nextMeta = 0
```

---

### STEP: `A` against `(A:Type) -> ...`

Variable pattern. Bind.

```
Γ = [(A, Type)]
Σ = {}
C = []
P = [(FSucc _w8 f), (VCons _w6 (Succ _w7) h tail), _w5]
T = [(n:Nat) -> Vec A n -> Fin n -> A]
E = [#0]
```

---

### STEP: `_w5` against `(n:Nat) -> ...`

Hole pattern. Create meta, bind, add constraint.

```
Γ = [(A, Type), (_w5, Nat)]
Σ = {?m0: {ctx: [A], ty: Nat, sol: null}}
C = [{ctx: [A, _w5], meta: ?m0, rhs: #1}]
P = [(FSucc _w8 f), (VCons _w6 (Succ _w7) h tail)]
T = [Vec A _w5 -> Fin _w5 -> A]
E = [#0, #1]
```

Note: ?m0's ctx is `[A]` (before `_w5` was bound), but the constraint's ctx is `[A, _w5]` (after binding).

---

### STEP: `(VCons _w6 (Succ _w7) h tail)` against `(_:Vec A _w5) -> ...`

Constructor pattern. Push DONE, sub-patterns, constructor type.

```
Γ = [(A, Type), (_w5, Nat)]
Σ = {?m0: ...}
C = [{ctx: ..., meta: ?m0, rhs: #1}]
P = [(FSucc _w8 f), DONE(VCons..., 4), tail, h, (Succ _w7), _w6]
T = [Vec A _w5 -> Fin _w5 -> A,
     (A':Type) -> (n':Nat) -> A' -> Vec A' n' -> Vec A' (Succ n')]
E = [#0, #1]
```

---

### STEP: `_w6` against `(A':Type) -> ...`

Hole pattern.

```
Γ = [(A, Type), (_w5, Nat), (_w6, Type)]
Σ = {?m0: {ctx: [A], ty: Nat, sol: null},
     ?m1: {ctx: [A, _w5], ty: Type, sol: null}}
C = [{ctx: [A, _w5], meta: ?m0, rhs: #1},
     {ctx: [A, _w5, _w6], meta: ?m1, rhs: #2}]
P = [(FSucc _w8 f), DONE(VCons..., 4), tail, h, (Succ _w7)]
T = [Vec A _w5 -> Fin _w5 -> A,
     (n':Nat) -> _w6 -> Vec _w6 n' -> Vec _w6 (Succ n')]
E = [#0, #1, #2]
```

Note: ?m1's ctx is `[A, _w5]` (before `_w6` was bound).

---

### STEP: `(Succ _w7)` against `(n':Nat) -> ...`

Constructor pattern.

```
Γ = [(A, Type), (_w5, Nat), (_w6, Type)]
P = [(FSucc _w8 f), DONE(VCons..., 4), tail, h, DONE(Succ _w7, 1), _w7]
T = [Vec A _w5 -> Fin _w5 -> A,
     (n':Nat) -> _w6 -> Vec _w6 n' -> Vec _w6 (Succ n'),
     (m:Nat) -> Nat]
E = [#0, #1, #2]
```

---

### STEP: `_w7` against `(m:Nat) -> Nat`

Hole pattern.

```
Γ = [(A, Type), (_w5, Nat), (_w6, Type), (_w7, Nat)]
Σ = {?m0: {ctx: [A], ty: Nat, sol: null},
     ?m1: {ctx: [A, _w5], ty: Type, sol: null},
     ?m2: {ctx: [A, _w5, _w6], ty: Nat, sol: null}}
C = [{ctx: [A, _w5], meta: ?m0, rhs: #1},
     {ctx: [A, _w5, _w6], meta: ?m1, rhs: #2},
     {ctx: [A, _w5, _w6, _w7], meta: ?m2, rhs: #3}]
P = [(FSucc _w8 f), DONE(VCons..., 4), tail, h, DONE(Succ _w7, 1)]
T = [Vec A _w5 -> Fin _w5 -> A,
     (n':Nat) -> _w6 -> Vec _w6 n' -> Vec _w6 (Succ n'),
     Nat]
E = [#0, #1, #2, #3]
```

Note: ?m2's ctx is `[A, _w5, _w6]` (before `_w7` was bound).

---

### STEP: `DONE(Succ _w7, 1)`

Pop T -> `Nat` (Succ's return type)
Peek T -> `(n':Nat) -> _w6 -> Vec _w6 n' -> Vec _w6 (Succ n')`

Unify: `Nat = Nat` ✓

Build: Pop 1 from E -> `#3`. Build `Con(Succ, [#3])`. Push.

Pop T, push codomain `[n' := Succ _w7]`.

```
Γ = [(A, Type), (_w5, Nat), (_w6, Type), (_w7, Nat)]
P = [(FSucc _w8 f), DONE(VCons..., 4), tail, h]
T = [Vec A _w5 -> Fin _w5 -> A,
     _w6 -> Vec _w6 (Succ _w7) -> Vec _w6 (Succ (Succ _w7))]
E = [#0, #1, #2, Con(Succ, [#3])]
```

---

### STEP: `h` against `_w6`

Variable pattern. Bind.

```
Γ = [(A, Type), (_w5, Nat), (_w6, Type), (_w7, Nat), (h, _w6)]
P = [(FSucc _w8 f), DONE(VCons..., 4), tail]
T = [Vec A _w5 -> Fin _w5 -> A,
     Vec _w6 (Succ _w7) -> Vec _w6 (Succ (Succ _w7))]
E = [#0, #1, #2, Con(Succ, [#3]), #4]
```

---

### STEP: `tail` against `Vec _w6 (Succ _w7)`

Variable pattern. Bind.

```
Γ = [(A, Type), (_w5, Nat), (_w6, Type), (_w7, Nat), (h, _w6), (tail, Vec _w6 (Succ _w7))]
P = [(FSucc _w8 f), DONE(VCons..., 4)]
T = [Vec A _w5 -> Fin _w5 -> A,
     Vec _w6 (Succ (Succ _w7))]
E = [#0, #1, #2, Con(Succ, [#3]), #4, #5]
```

---

### STEP: `DONE(VCons _w6 (Succ _w7) h tail, 4)`

Pop T → `Vec _w6 (Succ (Succ _w7))` (VCons's return type, ctxLen=4)
Peek T → `Vec A _w5 -> Fin _w5 -> A` (ctxLen=2)

**Shift both to current context (len=6):**
- Left: `Vec #3 (Succ (Succ #2))` (shifted by 2)
- Right domain: `Vec #5 #4` (shifted by 4)

**Unify:** `Vec #3 (Succ (Succ #2)) = Vec #5 #4`
- Injectivity: `#3 = #5` → equation `(3, #5)` i.e. `_w6 = A`
- Injectivity: `Succ (Succ #2) = #4` → equation `(4, Succ(Succ #2))` i.e. `_w5 = Succ(Succ _w7)`

**Apply `#3 = #5` (first substitution, _w6 = A):**

Before (mainSigLength=6):
```
Γ = [(A, Type), (_w5, Nat), (_w6, Type), (_w7, Nat), (h, _w6), (tail, Vec _w6 (Succ _w7))]
Σ = {?m0: {ctx: [A], ty: Nat, sol: null},
     ?m1: {ctx: [A, _w5], ty: Type, sol: null},
     ?m2: {ctx: [A, _w5, _w6], ty: Nat, sol: null}}
T = [Vec A _w5 -> Fin _w5 -> A (ctxLen=2),
     Vec _w6 (Succ (Succ _w7)) (ctxLen=4)]
E = [#0, #1, #2, Con(Succ, [#3]), #4, #5]
C = [{ctx: [A, _w5], meta: ?m0, rhs: #1},
     {ctx: [A, _w5, _w6], meta: ?m1, rhs: #2},
     {ctx: [A, _w5, _w6, _w7], meta: ?m2, rhs: #3}]
```

Substitution `#3 = #5`: removing `_w6` (index 3 from tail).
- ?m0 ctx `[A]`: `_w6` not in scope, unchanged
- ?m1 ctx `[A, _w5]`: `_w6` not in scope, unchanged
- ?m2 ctx `[A, _w5, _w6]`: `_w6` is in scope (local index 0), remove it → `[A, _w5]`
- C[0] ctx `[A, _w5]`: `_w6` not in scope, unchanged
- C[1] ctx `[A, _w5, _w6]`: `_w6` is in scope (local index 0), remove it, rhs `#2` → `#0` (was _w6, now A)
- C[2] ctx `[A, _w5, _w6, _w7]`: `_w6` is in scope (local index 1), remove it → `[A, _w5, _w7]`, rhs `#3` → `#2`

After applying `#3 = #5` to all state:
```
Γ = [(A, Type), (_w5, Nat), (_w7, Nat), (h, A), (tail, Vec A (Succ _w7))]
Σ = {?m0: {ctx: [A], ty: Nat, sol: null},
     ?m1: {ctx: [A, _w5], ty: Type, sol: null},
     ?m2: {ctx: [A, _w5], ty: Nat, sol: null}}
T = [Vec A _w5 -> Fin _w5 -> A (ctxLen=2),
     Vec A (Succ (Succ _w7)) (ctxLen=3)]
E = [#0, #1, #0, Con(Succ, [#2]), #3, #4]
C = [{ctx: [A, _w5], meta: ?m0, rhs: #1},
     {ctx: [A, _w5], meta: ?m1, rhs: #0},
     {ctx: [A, _w5, _w7], meta: ?m2, rhs: #2}]
```

**Apply `#3 = Succ(Succ #2)` (second substitution, _w5 = Succ(Succ _w7)):**

In the updated context (mainSigLength=5), this is now `#3 = Succ(Succ #1)` (indices adjusted).
Removing `_w5` (index 3 from tail in the 5-length context).

- ?m0 ctx `[A]`: `_w5` not in scope, unchanged
- ?m1 ctx `[A, _w5]`: `_w5` is in scope (local index 0), remove it → `[A]`
- ?m2 ctx `[A, _w5]`: `_w5` is in scope (local index 0), remove it → `[A]`
- C[0] ctx `[A, _w5]`: `_w5` is in scope (local index 0), remove it → `[A]`, rhs `#1` → `Succ(Succ _w7)` but _w7 escapes!
- C[1] ctx `[A, _w5]`: `_w5` is in scope (local index 0), remove it → `[A]`, rhs `#0` unchanged (still A)
- C[2] ctx `[A, _w5, _w7]`: `_w5` is in scope (local index 1), remove it → `[A, _w7]`, rhs `#2` → `#1`

After applying to all state (mainSigLength=4):
```
Γ = [(A, Type), (_w7, Nat), (h, A), (tail, Vec A (Succ _w7))]
Σ = {?m0: {ctx: [A], ty: Nat, sol: null},
     ?m1: {ctx: [A], ty: Type, sol: null},
     ?m2: {ctx: [A], ty: Nat, sol: null}}
T = [Fin (Succ (Succ _w7)) -> A (ctxLen=1)]
E = [#0, Succ(Succ #1), #0, Succ #1, #2, #3]
C = [{ctx: [A], meta: ?m0, rhs: <escaping: Succ(Succ _w7)>},
     {ctx: [A], meta: ?m1, rhs: #0},
     {ctx: [A, _w7], meta: ?m2, rhs: #1}]
```

Note on E (using levels):
- #0 = A
- #1 = _w7
- #2 = h
- #3 = tail
So E = [#0, Succ(Succ #1), #0, Succ #1, #2, #3] represents: [A, Succ(Succ _w7), A, Succ _w7, h, tail]

**Build:** Pop 4 from E (the VCons args: A', n', head, tail):
- Pop #3 (tail)
- Pop #2 (h)  
- Pop Succ #1 (Succ _w7)
- Pop #0 (A)

Args in order: [#0, Succ #1, #2, #3] = [A, Succ _w7, h, tail]

Convert levels to indices (ctxLen=4): 
- #0 (level 0 = A) → index 3
- Succ #1 (level 1 = _w7) → Succ #2
- #2 (level 2 = h) → index 1
- #3 (level 3 = tail) → index 0

Build `Con(VCons, [#3, Succ #2, #1, #0])`. Push to E.

E after build: `[#0, Succ(Succ #1), Con(VCons, [#3, Succ #2, #1, #0])]`
Which is: [A, Succ(Succ _w7), VCons A (Succ _w7) h tail]

**Pop T, push codomain with substitution applied.**

**Solve constraints:**
- ?m1: ctx=[A], rhs=#0, FV={0} < 1. ✓ **Solve: ?m1 := #0** (i.e., `A`)
- ?m2: ctx=[A, _w7], rhs=#1, FV={1} < 2. ✓ **Solve: ?m2 := #1** (i.e., `_w7`)
- ?m0: ctx=[A], rhs references `_w7` which is not in scope. **Stuck (needs re-lift).**

```
Γ = [(A, Type), (_w7, Nat), (h, A), (tail, Vec A (Succ _w7))]
Σ = {?m0: {ctx: [A], ty: Nat, sol: null},
     ?m1: {ctx: [A], ty: Type, sol: #0},
     ?m2: {ctx: [A], ty: Nat, sol: #1}}
C = [{ctx: [A], meta: ?m0, rhs: <needs re-lift to include _w7>}]
P = [(FSucc _w8 f)]
T = [Fin (Succ (Succ _w7)) -> A]
E = [#0, Succ(Succ #1), Con(VCons, [#3, Succ #2, #1, #0])]
```

---

### STEP: `(FSucc _w8 f)` against `(_:Fin (Succ (Succ _w7))) -> A`

Constructor pattern.

```
P = [DONE(FSucc _w8 f, 2), f, _w8]
T = [Fin (Succ (Succ _w7)) -> A,
     (n:Nat) -> Fin n -> Fin (Succ n)]
E = [Con(VCons, [...])]
```

---

### STEP: `_w8` against `(n:Nat) -> ...`

Hole pattern.

```
Γ = [(A, Type), (_w7, Nat), (h, A), (tail, Vec A (Succ _w7)), (_w8, Nat)]
Σ = {?m0: {ctx: [A], ty: Nat, sol: null},
     ?m1: {ctx: [A], ty: Type, sol: #0},
     ?m2: {ctx: [A], ty: Nat, sol: #1},
     ?m3: {ctx: [A, _w7, h, tail], ty: Nat, sol: null}}
C = [{ctx: [A], meta: ?m0, rhs: <escaping>},
     {ctx: [A, _w7, h, tail, _w8], meta: ?m3, rhs: #4}]
P = [DONE(FSucc _w8 f, 2), f]
T = [Fin (Succ (Succ _w7)) -> A,
     Fin _w8 -> Fin (Succ _w8)]
E = [Con(VCons, [...]), #4]
```

Note: ?m3's ctx is `[A, _w7, h, tail]` (before `_w8` was bound).

---

### STEP: `f` against `Fin _w8`

Variable pattern.

```
Γ = [(A, Type), (_w7, Nat), (h, A), (tail, Vec A (Succ _w7)), (_w8, Nat), (f, Fin _w8)]
P = [DONE(FSucc _w8 f, 2)]
T = [Fin (Succ (Succ _w7)) -> A,
     Fin (Succ _w8)]
E = [Con(VCons, [...]), #4, #5]
```

---

### STEP: `DONE(FSucc _w8 f, 2)`

Pop T -> `Fin (Succ _w8)`
Peek T -> `Fin (Succ (Succ _w7)) -> A`

Unify: `Fin (Succ _w8) = Fin (Succ (Succ _w7))`
- Injectivity: `Succ _w8 = Succ (Succ _w7)`
- Injectivity: `_w8 = Succ _w7` -> equation `(4, Succ(#1))`

**Apply `#4 = Succ(#1)`:**

```
Γ = [(A, Type), (_w7, Nat), (h, A), (tail, Vec A (Succ _w7)), (f, Fin (Succ _w7))]
     level:  0          1       2                3                    4
```

**Update constraint for ?m3:**
```
C = [..., {ctx: [(A,Type),(_w7,Nat),(h,A),(tail,Vec A (Succ _w7))], meta: ?m3, rhs: Succ(#1)}]
```

**Solve:**
- ?m3: telLen=4, rhs=Succ(#1), FV={1} < 4. ✓ **Solve: ?m3 := Succ(#1)**
- ?m0: Still stuck.

**Build:** Pop 2 from E -> `Succ(#1), #4`. Build `Con(FSucc, [Succ(#1), #4])`. Push.

```
Γ = [(A, Type), (_w7, Nat), (h, A), (tail, Vec A (Succ _w7)), (f, Fin (Succ _w7))]
Σ = {?m0: {telLen: 1, sol: null},
     ?m1: {telLen: 2, sol: #0},
     ?m2: {telLen: 3, sol: #1},
     ?m3: {telLen: 4, sol: Succ(#1)}}
C = [{ctx: [(A,Type)], meta: ?m0, rhs: Succ(Succ(#1))}]
P = []
T = [A]
E = [Con(VCons, [...]), Con(FSucc, [Succ(#1), #4])]
```

---

### LHS Done. Process RHS: `nth _w9 _w10 tail f`

Push args, push nth type.

```
P = [f, tail, _w10, _w9]
T = [A,
     (A':Type) -> (n':Nat) -> Vec A' n' -> Fin n' -> A']
E = [Con(VCons, [...]), Con(FSucc, [...])]
```

---

### STEP: `_w9` against `(A':Type) -> ...`

Hole on RHS. Create meta, no binding.

```
Σ = {..., ?m4: {telLen: 5, ty: Type, sol: null}}
P = [f, tail, _w10]
T = [A,
     (n':Nat) -> Vec ?m4 n' -> Fin n' -> ?m4]
E = [..., App(Meta(4), [#0,#1,#2,#3,#4])]
```

---

### STEP: `_w10` against `(n':Nat) -> ...`

Hole on RHS.

```
Σ = {..., ?m5: {telLen: 5, ty: Nat, sol: null}}
P = [f, tail]
T = [A,
     Vec ?m4 ?m5 -> Fin ?m5 -> ?m4]
E = [..., App(Meta(5), [#0,#1,#2,#3,#4])]
```

---

### STEP: `tail` against `Vec ?m4 ?m5`

Variable on RHS. Look up: `tail` at level 3 with type `Vec A (Succ _w7)`.

Unify: `Vec A (Succ _w7) = Vec ?m4 ?m5`
- Meta constraint: `?m4 = #0` (which is A)
- Meta constraint: `?m5 = Succ(#1)` (which is Succ _w7)

**Add constraints and solve:**
- ?m4: telLen=5, rhs=#0, FV={0} < 5. ✓ **Solve: ?m4 := #0**
- ?m5: telLen=5, rhs=Succ(#1), FV={1} < 5. ✓ **Solve: ?m5 := Succ(#1)**

```
Σ = {..., ?m4: {sol: #0}, ?m5: {sol: Succ(#1)}}
P = [f]
T = [A,
     Fin (Succ _w7) -> A]
E = [..., #3]
```

---

### STEP: `f` against `Fin (Succ _w7)`

Variable on RHS. Look up: `f` at level 4 with type `Fin (Succ _w7)`.

Unify: `Fin (Succ _w7) = Fin (Succ _w7)` ✓

```
P = []
T = [A, A]
E = [..., #4]
```

---

### RHS Done

Pop T -> `A` (inferred)
Pop T -> `A` (expected)

Unify: `A = A` ✓

```
T = []
```

---

### Re-lift Stuck Constraints

```
C = [{ctx: [(A,Type)], meta: ?m0, rhs: Succ(Succ(#1))}]
```

**Re-lift ?m0:**
- Old telLen: 1
- New telLen: 5 (full Γ)
- rhs = Succ(Succ(#1)), FV={1} < 5. ✓

**Solve: ?m0 := Succ(Succ(#1))**

---

### Final State

```
Γ = [(A, Type), (_w7, Nat), (h, A), (tail, Vec A (Succ _w7)), (f, Fin (Succ _w7))]

Σ = {
  ?m0: {telLen: 5, sol: Succ(Succ(#1))},   -- _w5 = Succ (Succ _w7)
  ?m1: {telLen: 2, sol: #0},                -- _w6 = A
  ?m2: {telLen: 3, sol: #1},                -- (inner Succ arg) = _w7
  ?m3: {telLen: 4, sol: Succ(#1)},          -- _w8 = Succ _w7
  ?m4: {telLen: 5, sol: #0},                -- _w9 = A
  ?m5: {telLen: 5, sol: Succ(#1)}           -- _w10 = Succ _w7
}

C = []
```

---

### Elaborated Clause

**LHS:** `nth A (Succ (Succ _w7)) (VCons A (Succ _w7) h tail) (FSucc (Succ _w7) f)`

**RHS:** `nth A (Succ _w7) tail f`

---

## Summary Table

| Hole | Meta | Solution | Meaning |
|------|------|----------|---------|
| `_w5` | ?m0 | `Succ(Succ(#1))` | `Succ (Succ _w7)` |
| `_w6` | ?m1 | `#0` | `A` |
| `_w7` | ?m2 | `#1` | `_w7` (identity) |
| `_w8` | ?m3 | `Succ(#1)` | `Succ _w7` |
| `_w9` | ?m4 | `#0` | `A` |
| `_w10` | ?m5 | `Succ(#1)` | `Succ _w7` |

---

## Constraint Solving Algorithm

### Data Structures

```typescript
interface MetaVar {
  ctx: Signature;           // Telescope: the context when this meta was created
  type: TTKTerm;            // The type of the meta
  solution: TTKTerm | null; // The solution, once found
}

interface Constraint {
  ctx: Signature;           // Context where constraint was created (after binding)
  meta: string;             // Meta-variable id (e.g., "?m0")
  rhs: TTKTerm;             // The term the meta should equal
}
```

**Key distinction:** `meta.ctx` is the telescope (context *before* the hole was bound). `constraint.ctx` is the context *after* binding (used for index calculations during substitution).

### Solvability Condition

A constraint `?m = t` is **solvable** when all free variables in `t` are within the meta's telescope:

```typescript
function canSolve(meta: MetaVar, rhs: TTKTerm): boolean {
  const telLen = meta.ctx.length;
  return maxFreeVarIndex(rhs) < telLen;
}
```

If `t` references index `i` where `i >= telLen`, the constraint is **stuck**.

### Two-Phase Solving

**Phase 1: During Elaboration**

After `constructorDone` applies substitutions, try to solve:

```typescript
function solveConstraints(env: WorkEnv): WorkEnv {
  const stillStuck: Constraint[] = [];
  
  for (const constraint of env.constraints) {
    const meta = env.metaVars.get(constraint.meta)!;
    
    if (meta.solution !== null) continue;
    
    if (canSolve(meta, constraint.rhs)) {
      meta.solution = constraint.rhs;
    } else {
      stillStuck.push(constraint);
    }
  }
  
  return { ...env, constraints: stillStuck };
}
```

**Phase 2: After All Patterns (Re-lift)**

Stuck constraints get their telescope extended to the full final context:

```typescript
function reliftAndSolve(env: WorkEnv): WorkEnv {
  const fullCtx = env.signature;
  const stillStuck: Constraint[] = [];
  
  for (const constraint of env.constraints) {
    const meta = env.metaVars.get(constraint.meta)!;
    
    if (meta.solution !== null) continue;
    
    // Extend telescope to full context
    meta.ctx = fullCtx;
    
    if (canSolve(meta, constraint.rhs)) {
      meta.solution = constraint.rhs;
    } else {
      // Still stuck after re-lift = type error
      stillStuck.push(constraint);
    }
  }
  
  return { ...env, constraints: stillStuck };
}
```

### Why Constraints Get Stuck

When a substitution like `_w5 = Succ(Succ _w7)` is applied:

1. The constraint's `ctx` shrinks (removing `_w5`)
2. The `rhs` changes from `#1` (pointing to `_w5`) to `Succ(Succ _w7)`
3. But `_w7` might not be in the meta's telescope → **escaping variable** → stuck

### Example

```
?m0 created with ctx = [A]  (telescope length 1)

After substitution _w5 = Succ(Succ _w7):
  constraint.rhs = Succ(Succ #1)  where #1 = _w7
  maxFreeVarIndex = 1
  telLen = 1
  1 < 1? NO → STUCK

After re-lift to full ctx = [A, _w7, h, tail, f]:
  meta.ctx extended to length 5
  maxFreeVarIndex = 1
  telLen = 5
  1 < 5? YES → SOLVE: ?m0 := Succ(Succ #1)
```

### Main Loop Integration

```typescript
// Main elaboration loop
while (patternStack.length > 0) {
  const pattern = patternStack.pop()!;
  const checkType = checkStack.pop()!;
  
  if (pattern.tag === 'done') {
    workEnv = constructorDone(...);  // calls solveConstraints internally
  } else {
    workEnv = processPattern(...);
  }
}

// Final re-lift for stuck constraints
workEnv = reliftAndSolve(workEnv);

// If constraints remain, it's a type error
if (workEnv.constraints.length > 0) {
  throw new Error('Unsolved constraints');
}
```