# LeanUI Language Specification

This document describes the surface syntax of the LeanUI language.

## Terms

### Variables and Constants

```
x               -- Variable (resolved to De Bruijn index)
Nat             -- Constant (looked up in environment)
```

### Universes (Sorts)

```
Type            -- Type_0 (alias for Type 0)
Type 0          -- Type at level 0
Type 1          -- Type at level 1
Type_3          -- Type at level 3 (underscore notation)
Prop            -- Propositions (Type 0)
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

### Pattern Matching in Definitions

```
def plus : Nat -> Nat -> Nat
| Zero, n => n
| Succ m, n => Succ (plus m n)
```

## Comments

```
-- Single line comment

/- Block comment
   can span multiple lines -/

/- Nested /- comments -/ are supported -/
```

## Operators

```
a + b                     -- Infix operators (defined in environment)
a * b
a = b                     -- Equality
```

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

## Precedence and Associativity

- Application is left-associative: `f x y` = `(f x) y`
- Arrow is right-associative: `A -> B -> C` = `A -> (B -> C)`
- Lambda body extends as far right as possible: `\x => f x` = `\x => (f x)`

## Reserved Keywords

```
def, inductive, where, match, with, let, in, Type, Prop, fun
```

## Lexical Conventions

- Identifiers: Start with letter or underscore, followed by letters, digits, underscores
- Greek letters and mathematical symbols are allowed in identifiers
- Whitespace is generally insignificant except for indentation-sensitive constructs
