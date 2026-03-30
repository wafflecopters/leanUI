# LeanUI Language Specification

This document describes the surface syntax of the LeanUI language.

## Terms

### Variables and Constants

```
x               -- Variable (resolved to De Bruijn index)
Nat             -- Constant (looked up in environment)
Point.x         -- Qualified identifier (e.g., record projection)
Foo.Bar.baz     -- Multi-level qualified identifier
```

Qualified identifiers use dot notation to access namespaced definitions.
Currently used for record projections (e.g., `Point.x` to project field `x` from record `Point`).

### Universes (Sorts)

```
Type            -- Type_0 (alias for Type 0)
Type 0          -- Type at level 0
Type 1          -- Type at level 1
Type_3          -- Type at level 3 (underscore notation)
Type u          -- Type at level u (where u is a level variable)
Prop            -- Propositions (Type 0)
```

### Universe Levels

```
ULevel          -- The type of universe levels
UZero           -- The zero level (equivalent to 0)
0, 1, 2, ...    -- Numeric level literals
USucc u         -- Successor of level u
UMax u v        -- Maximum of levels u and v
UIMax u v       -- Impredicative max (0 if v=0, else max(u,v))
```

Universe level variables are bound with `{u : ULevel}` binders:

```
id : {u : ULevel} -> {A : Type u} -> A -> A
id x = x
```

### Pi Types (Function Types)

```
A -> B                    -- Non-dependent function type
(x : A) -> B              -- Dependent Pi type, single parameter
(a b : A) -> B            -- Multi-parameter Pi, same type (space-separated)
(a b c d : A) -> B        -- Any number of parameters
(x : A) -> (y : B) -> C   -- Chained Pi types
```

### Lambda Expressions

```
\x => body                -- Untyped lambda (type inferred as hole)
\ x => body               -- Same, with space
\x y => body              -- Multiple untyped parameters
\(x : A) => body          -- Typed lambda, single parameter
\(x y : A) => body        -- Multi-parameter lambda, same type (space-separated)
\(x : A) y => body        -- Mixed typed and untyped
\(x : A) (y : B) => body  -- Multiple typed binders
```

**Note:** Type annotations require parentheses. `\x : A => body` is NOT allowed.

### Let Expressions

```
let x = val in body             -- No type annotation
let x : T = val in body         -- With type annotation
let (x : T) = val in body       -- Parenthesized type annotation
```

**Note:** Arrow types in annotations need parentheses to avoid ambiguity with `=`:
```
let f : (A -> B) = val in body    -- Correct: parens around arrow type
let f : A -> B = val in body      -- Incorrect: parser sees A -> (B = val ...)
```

### Multi-Let Expressions

Multiple bindings can be specified in a single `let` using commas:

```
let a = X, b = Y in body           -- Two bindings
let a = X, b = Y, c = Z in body    -- Three bindings
let a : T = X, b = Y in body       -- First binding typed, second untyped
```

Each binding can reference previous bindings:

```
let a = Zero, b = Succ a, c = Succ b in c   -- b uses a, c uses b
```

Multi-let is expanded to nested single-let expressions during elaboration:

```
let a = X, b = Y in body
-- Elaborates to:
let a = X in let b = Y in body
```

### Applications

```
f x                       -- Simple application
f x y z                   -- Multiple arguments (left-associative)
(f x) y                   -- Explicit grouping
```

### Type Annotations

```
(x : T)                   -- Annotate term x with type T
(f x : T)                 -- Annotate application (f x) with type T
```

### Holes

```
_                         -- Unnamed hole (to be inferred)
?name                     -- Named hole
```

### Match Expressions

```
match x with
| Zero => ...
| Succ n => ...
```

## Definitions

### Function Definitions

```
def name : Type := body

def id : (A : Type) -> A -> A := \(A : Type) (x : A) => x
```

### Inductive Types

```
inductive Nat : Type where
| Zero : Nat
| Succ : Nat -> Nat
```

### Record Types (Structures)

Records are single-constructor inductive types with named fields and automatic projection functions.

**Basic syntax:**
```
record Point where
  x : Nat
  y : Nat
```

**With parameters:**
```
record Pair (A : Type) (B : Type) where
  fst : A
  snd : B
```

**With implicit parameters:**
```
record Container {A : Type} where
  value : A
```

**With multi-variable binders (multiple names sharing one type):**
```
record Pair (A B : Type) where
  fst : A
  snd : B

record Foo (A B : Type) {C D : Type} where
  x : A
  y : C
```

**With custom constructor name:**
```
record Point where
  constructor MkPoint
  x : Nat
  y : Nat
```

**With inheritance (extends):**
```
record ColoredPoint extends Point where
  color : Color

record Combined extends A, B, C where
  extra : Nat
```

**With implicit fields:**
```
record ImplicitField where
  {hidden : Type}
  visible : hidden
```

**Dependent fields** (fields can reference previous fields):
```
record Sigma (A : Type) (B : A -> Type) where
  fst : A
  snd : B fst
```

**Default constructor name:** If not specified, the constructor is named `Mk#RecordName`.

**Record η-conversion:** Records support eta expansion/contraction for definitional equality. A record value constructed from all of its projections is definitionally equal to the original value:

```
-- For any record R with fields f1, f2, ..., fN:
MkR (R.f1 r) (R.f2 r) ... (R.fN r) ≃ r

-- Example: Point with fields x and y
MkPoint (Point.x p) (Point.y p) ≃ p
```

This allows functions that reconstruct a record from its projections to type check correctly:

```
-- This type checks because the RHS is definitionally equal to p
idPoint : Point -> Point
idPoint p = MkPoint (Point.x p) (Point.y p)
```

### Postulates (Axioms)

Postulates declare a name with a type but no definition. They are opaque to reduction — the type checker accepts them on faith.

```
postulate myAxiom : (A : Type) -> A -> A
```

Postulates are useful for:
- Axiomatizing structures that exist but whose construction is not relevant (e.g., the real numbers)
- Declaring operations whose implementation requires features not yet available (e.g., case analysis on order)

```
-- Postulate the reals as a complete ordered field
postulate RealPkg : DPair (Type) CompleteOrderedField

-- Postulate absolute value (requires case analysis on order)
postulate rabs : Real -> Real
```

### Pattern Matching in Definitions

```
def plus : Nat -> Nat -> Nat
| Zero, n => n
| Succ m, n => Succ (plus m n)
```

### With Clauses

With clauses provide Agda-style pattern matching on an expression within a function definition. They desugar to auxiliary functions.

**Basic with** — match on a function argument:

```
isZero : Nat -> Bool
isZero n with n
  | Zero => True
  | Succ _ => False
```

**With on a computed expression** — match on the result of a function call:

```
isZeroSafe : Nat -> Bool
isZeroSafe n with isZero n
  | True => True
  | False => False
```

**Multiple scrutinees** — match on several expressions at once:

```
compare : Nat -> Nat -> Ordering
compare m n with m, n
  | Zero, Zero => EQ
  | Zero, Succ _ => LT
  | Succ _, Zero => GT
  | Succ a, Succ b => compare a b
```

**Mixed clauses** — combine regular pattern matching with `with`:

```
isOne : Nat -> Bool
isOne Zero = False
isOne n with n
  | Succ Zero => True
  | Succ (Succ _) => False
```

**Multiple with clauses** — different clauses of the same function can each use `with`:

```
classify : Nat -> Nat -> Nat
classify Zero n with n
  | Zero => Zero
  | Succ _ => Succ Zero
classify (Succ m) n with n
  | Zero => Succ (Succ Zero)
  | Succ _ => Succ (Succ (Succ Zero))
```

**With on generic types** — works with implicit type parameters:

```
headOr : {A : Type} -> A -> List A -> A
headOr def xs with xs
  | Nil => def
  | Cons x _ => x
```

**Desugaring**: Each `with` clause compiles to an auxiliary function. For example, `isZero n with n | Zero => True | Succ _ => False` becomes:

```
isZero n = isZero-with-1 n n
isZero-with-1 : Nat -> Nat -> Bool
isZero-with-1 n Zero = True
isZero-with-1 n (Succ _) = False
```

**Nested with** — use `with` inside a with-branch to match on another expression:

```
classify : Nat -> Nat -> Bool
classify m n with m
  | Zero with n
    | Zero => True
    | Succ _ => False
  | Succ _ => True
```

Nested withs can appear in any branch and can be nested to arbitrary depth:

```
deep : Nat -> Nat -> Nat -> Bool
deep a b c with a
  | Zero with b
    | Zero with c
      | Zero => True
      | Succ _ => False
    | Succ _ => False
  | Succ _ => False
```

Each level of nesting generates an additional auxiliary function. The inner `|` pipes are distinguished from outer ones by indentation (inner pipes must be indented further than outer pipes).

**Ellipsis syntax** — `...` can optionally precede `|` in with-branches, following Agda convention. It means "repeat the parent function patterns unchanged":

```
filter p Nil = Nil
filter p (Cons x rest) with p x
  ... | True => Cons x (filter p rest)
  ... | False => filter p rest
```

The `...` is purely syntactic sugar — our with-branches already inherit the parent function patterns implicitly. It works in both top-level and nested with-branches.

**`#absurd` in with branches** — mark impossible cases:

```
absurdEqual : Equal Zero (Succ Zero) -> Void
absurdEqual eq with eq
  | refl => #absurd
```

With branches must be exhaustive (all constructor cases covered).

## Comments

```
-- Single line comment

/- Block comment
   can span multiple lines -/

/- Nested /- comments -/ are supported -/
```

## Directives

Directives are special annotations that control compiler behavior. They start with `@` and appear at the top of a file or before definitions.

### @assumeK

Controls whether axiom K (the deletion rule) is enabled for pattern matching:

```
@assumeK=true    -- Enable axiom K (allows UIP, Streicher's K)
@assumeK=false   -- Disable axiom K (requires --without-K proofs)
```

**Default:** Axiom K is **enabled** by default (matches Lean's behavior).

**What it affects:**
- **With K enabled:** Pattern matches that force reflexive equations (`x = x`) are allowed
- **Without K:** Only proofs using the J eliminator are allowed

**Example:**
```
@assumeK=true

inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a

-- UIP requires axiom K
uip : {A : Type} -> {x y : A} -> (p q : Equal x y) -> Equal p q
uip refl refl = refl  -- ✓ Allowed with @assumeK=true
```

**See also:** [AXIOM_K.md](AXIOM_K.md) for detailed explanation of axiom K.

## Operators

```
a + b                     -- Infix operators (defined in environment)
a * b
a = b                     -- Equality
```

## Notation Declarations

Custom infix, prefix, and binding operators can be defined:

```
infixl <precedence> <symbol> := <function>    -- Left-associative infix
infixr <precedence> <symbol> := <function>    -- Right-associative infix
infix  <precedence> <symbol> := <function>    -- Non-associative infix
prefix <precedence> <symbol> := <function>    -- Prefix operator
```

### Examples

```
infixl 65 + := radd       -- a + b  desugars to  radd a b
infixl 70 * := rmul       -- a * b  desugars to  rmul a b
prefix 90 - := rneg       -- -a     desugars to  rneg a
```

### Binding Notation (Sigma Types)

Right-associative operators with the `binding` keyword create dependent binding forms:

```
infixr 40 ** := DPair binding

-- (x : A ** P x)  desugars to  DPair A (\x => P x)
myType : Type
myType = (n : Nat ** Equal n Zero)
```

When `**` follows a typed binder `(x : A)`, the RHS is wrapped in a lambda binding `x`.

### Precedence

Higher numbers bind tighter. Standard precedences:
- `->` (Pi type): 25
- `||` , `∨` : 30
- `&&` , `∧` : 35
- `**` (DPair): 40
- `=` , `<` , `>` , `≤` , `≥` : 50
- `+` , `-` : 65
- `*` , `/` : 70
- `^` : 80
- prefix `-` : 90
- function application: 100

## Syntactic Sugar

### Multi-Parameter Binders

When multiple parameters share the same type, they can be grouped:

```
-- Instead of:
(a : Nat) -> (b : Nat) -> (c : Nat) -> T

-- Write:
(a b c : Nat) -> T
```

This applies to both Pi types and lambda expressions.

## Named Arguments

Named arguments allow parameters to be specified by name rather than position. This is useful for functions with multiple type parameters where the caller wants to be explicit about which type is being provided.

### Named Binders in Pi Types

Use curly braces `{}` to declare named parameters:

```
{ A : Type } -> A -> A                    -- Single named parameter
{ A : Type } -> { B : Type } -> A -> B    -- Multiple named parameters
{ A B : Type } -> A -> B -> A             -- Multi-parameter named binder
```

Named binders differ from positional binders `(x : T)` in that they can be matched by name at call sites and in pattern definitions.

### Named Patterns in Function Definitions

When defining a function with named parameters, patterns can be specified by name using curly braces:

```
-- Named pattern at standard position
id : { A : Type } -> A -> A
id {A} x = x

-- Named patterns can be written in any order
fst : { A : Type } -> { B : Type } -> A -> B -> A
fst {B} {A} a b = a                       -- B and A are reordered to match positions

-- Mixed named and positional patterns, reordered
first : { A : Type } -> { B : Type } -> A -> B -> A
first x y {B} {A} = x                     -- All patterns reordered correctly
```

Named patterns are matched to their positions in the type signature by name, then reordered to the canonical order for type checking.

### Named Wildcard Patterns

Use `{_}` to indicate a named parameter position without binding its value:

```
isZero : { A : Type } -> Nat -> Bool
isZero {_} Zero = True
isZero {_} (Succ n) = False
```

### Named Arguments in Applications

When calling a function with named parameters, arguments can be specified by name using the `:=` syntax:

```
id : { A : Type } -> A -> A
id {A} x = x

test : Type -> Type
test T = id { A := T } T                  -- Explicitly provide A

-- Named arguments can be given in any order
const : { A : Type } -> { B : Type } -> A -> B -> A
const {A} {B} a b = a

test2 : Type
test2 = const { B := Type } { A := Type } Type Type
```

**Note:** Named argument application reordering is a work in progress.

### Comparison: Named vs Positional

| Syntax | In Type | In Pattern | In Application |
|--------|---------|------------|----------------|
| Positional | `(A : Type) ->` | `A` | `f Type` |
| Named | `{ A : Type } ->` | `{A}` or `{_}` | `f { A := Type }` |

Named parameters:
- Must be matched by exact name (or wildcard `{_}`)
- Can be provided in any order (reordered automatically)
- Useful for polymorphic functions with multiple type parameters

## Precedence and Associativity

- Application is left-associative: `f x y` = `(f x) y`
- Arrow is right-associative: `A -> B -> C` = `A -> (B -> C)`
- Lambda body extends as far right as possible: `\x => f x` = `\x => (f x)`

## Reserved Keywords

```
def, inductive, where, match, with, let, in, Type, Prop, fun, postulate
```

## Lexical Conventions

- Identifiers: Start with letter or underscore, followed by letters, digits, underscores
- Greek letters and mathematical symbols are allowed in identifiers
- Whitespace is generally insignificant except for indentation-sensitive constructs
