# LeanUI Engine Development Plan

## Completed

- **Universe Levels Core** - `kernel.ts`: Level type (LZero/LSucc/LMax/LIMax/LParam/LMVar), helpers, simplification, equality, pretty printing
- **Level Unification** - `unify.ts`: Full level unification with metavariables, occurs check
- **Term Unification** - `unify.ts`: First-order unification for all term forms, metavariable constraints
- **Bidirectional Type Checker** - `checker.ts`: inferType/checkType with documented typing rules
- **Sort Uses Levels** - Sort.level is Level type, mkProp/mkType/mkSort work correctly

---

## Roadmap

```
1. Level Syntax  →  2. Let Expressions  →  3. Named/Implicit Args  →  4. Multi-var Binders  →  5. Records
```

---

## 1. Level Syntax in Parser

**Goal**: Parse universe level parameters. Type inference can produce Type ω (omega) and successors internally, but there's no surface syntax for omega.

### 1.1: Parse Level Parameters
- `Type u` → `Sort (succ (param u))`
- `Sort u` → `Sort (param u)`
- `Type` (no param) → `Sort 1` (as today)

### 1.2: Parse Concrete Levels
- `Type 0` or `Type_0` → `Sort 1`
- `Type 3` or `Type_3` → `Sort 4`

### 1.3: Level Parameter Declarations
- Function signatures: `def id (u : Level) (A : Type u) (x : A) : A := x`
- Or implicit: `def id {u} {A : Type u} (x : A) : A := x`

### 1.4: Integration
- Track level params in elaboration context
- Infer level args at call sites
- Test: `id : {A : Type u} -> A -> A` works end-to-end

---

## 2. Let Expressions

**Goal**: Parse and check `let x : T := e in body` expressions.

### 2.1: Parser
- `let x := e in body` (type inferred)
- `let x : T := e in body` (type annotated)
- Support in term position

### 2.2: Elaboration
- Elaborate to kernel `BLet` binder
- Check definition value against annotated type (if present)
- Or infer type from definition value

### 2.3: Type Checking
- Already supported in kernel (`BLet` binder kind)
- Ensure WHNF unfolds let bindings

---

## 3. Named and Implicit Arguments

**Source**: `NAMED_ARGS_PLAN.md`

### 3.1: Extend Surface Syntax Types
- Add `BinderInfo = 'explicit' | 'implicit'` to binders
- Add `TArg = Positional | Named` for call-site arguments
- Add `Call` node: `{ tag: 'Call'; fn: TTerm; args: TArg[] }`

### 3.2: Parser - Implicit Binders
- `{x : A} -> B` as implicit Pi
- `\{x : A} => e` as implicit lambda

### 3.3: Parser - Named Arguments
- `f {x = e}` as named argument
- `f {x}` as shorthand for `f {x = x}`

### 3.4: Elaboration
- Resolve named args to positions
- Fill implicit args with fresh metavars
- Convert `Call` to chain of kernel `App` nodes

### 3.5: Pattern Syntax for Implicits
- `{n}` and `{n = pat}` in pattern position

### 3.6: Type Query Updates
- Handle `Call` nodes in hover/type queries

---

## 4. Multi-Variable Binders

**Source**: `MULTI_ARGS_PLAN.md`

### 4.1: Add MultiVarBinder to Surface Syntax
- `{ tag: 'MultiVarBinder'; names: string[]; binderKind: BinderKind; domain: TTerm; body: TTerm }`

### 4.2: Parser
- `(x y z : Nat) -> ...`
- `{A B : Type} -> ...`
- `\(x y : Nat) => ...`

### 4.3: Elaboration
- Transform `MultiVarBinder(['x','y'], T, body)` → nested single binders
- Adjust De Bruijn indices in body

### 4.4: Type Queries
- Track source range for each name
- Hover on `y` in `(x y : Nat)` shows `Nat`

---

## 5. Records (Structures)

**Source**: `STRUCTURES_PLAN.md`

### 5.1: Parser
```
structure Point where
  x : Nat
  y : Nat

structure Pair (A B : Type) where
  fst : A
  snd : B

structure ColorPoint extends Point where
  color : Color
```

### 5.2: Field Dependency Checking
- Check each field type in context of params + earlier fields
- Error on forward references

### 5.3: Projection Generation
- `Point.x : Point -> Nat`
- `Pair.fst : {A B : Type} -> Pair A B -> A`
- Handle dependent projections: `Sigma.snd : (s : Sigma A B) -> B (Sigma.fst s)`

### 5.4: Constructor Generation
- `Point.mk : Nat -> Nat -> Point`
- `Pair.mk : {A B : Type} -> A -> B -> Pair A B`

### 5.5: Extension Handling
- Inline parent fields during elaboration
- Detect cycles, field name clashes

### 5.6: Block Checker Integration
- Wire up: parse → elaborate → type-check → register projections/constructor

---

## Source Documents

- `NAMED_ARGS_PLAN.md` - Implicit/named argument design
- `LEVELS_PLAN.md` - Universe level polymorphism
- `MULTI_ARGS_PLAN.md` - Multi-variable binder syntax
- `STRUCTURES_PLAN.md` - Record/structure implementation
