# Tactics Examples & Grammar

This document shows example tactic proofs and extracts the grammar for tactics syntax.

---

## Example Proofs

### Example 1: Modus Ponens (Basic)

```
modusPonens : {A B : Type} -> A -> (A -> B) -> B := by
  intros A B a f
  apply f
  exact a
```

**Tactics used:**
- `intros` with identifier arguments
- `apply` with identifier argument (references hypothesis)
- `exact` with identifier argument

---

### Example 2: Modus Ponens (Explicit Steps)

```
modusPonens : {A B : Type} -> A -> (A -> B) -> B := by
  intro A
  intro B
  intro a
  intro f
  apply f
  assumption
```

**Tactics used:**
- `intro` with single identifier (repeated)
- `apply` with identifier
- `assumption` with no arguments

---

### Example 3: Identity Function

```
id : {A : Type} -> A -> A := by
  intros A x
  exact x
```

**Tactics used:**
- `intros` with multiple identifiers
- `exact` with identifier

---

### Example 4: Function Composition

```
compose : {A B C : Type} -> (B -> C) -> (A -> B) -> A -> C := by
  intros A B C g f a
  apply g
  apply f
  exact a
```

**Tactics used:**
- `intros` with many identifiers
- Multiple `apply` invocations creating subgoals
- `exact` to solve final goal

---

### Example 5: Using Complex Terms

```
applyTwice : {A : Type} -> (A -> A) -> A -> A := by
  intros A f x
  exact (f (f x))
```

**Tactics used:**
- `intros` with identifiers
- `exact` with **complex term** (application expression)

---

### Example 6: Explicit Type Application

```
selfApply : {A : Type} -> ((A -> A) -> A -> A) -> A -> A := by
  intros A f x
  apply f
  exact (\y => y)
```

**Tactics used:**
- `apply` with identifier
- `exact` with **lambda term** (anonymous function)

---

### Example 7: Pattern Matching Result

```
isZeroToBool : Nat -> Bool := by
  intro n
  exact (match n with
    | Zero => True
    | Succ _ => False)
```

**Tactics used:**
- `intro` with identifier
- `exact` with **match expression** (full pattern matching term)

---

### Example 8: Using Let Bindings

```
double : Nat -> Nat := by
  intro n
  exact (let twice = Succ (Succ n) in twice)
```

**Tactics used:**
- `exact` with **let expression**

---

### Example 9: Future - Have (introducing hypotheses)

```
contrapositive : {A B : Type} -> (A -> B) -> (Not B -> Not A) := by
  intros A B f nb a
  apply nb
  exact (f a)
```

Or with explicit `have`:

```
proof : {A : Type} -> A -> A := by
  intros A x
  have h : A := x
  exact h
```

**Future tactics:**
- `have <name> : <type> := <term>` - introducing intermediate lemmas

---

## Grammar Analysis

### Top-Level Structure

```ebnf
definition ::= identifier ':' term ':=' 'by' tacticBlock

tacticBlock ::= NEWLINE INDENT tacticLine+ DEDENT

tacticLine ::= tactic NEWLINE
```

### Tactic Grammar

```ebnf
tactic ::= tacticName tacticArgs?

tacticName ::= 'intro' | 'intros' | 'exact' | 'apply' | 'assumption'
             | 'refine' | 'cases' | 'induction' | 'rewrite' | 'constructor'
             | 'reflexivity' | 'have' | ...

tacticArgs ::= identifier+                  -- For intro, intros, cases, etc.
             | term                         -- For exact, apply, refine, etc.
             | identifier ':' term ':=' term -- For have
```

### Key Observation: Context-Dependent Parsing

The challenge: **we need to know which tactic to determine how to parse arguments**.

**Strategy 1: Tactic-specific parsing** (like Lean 4)
```
intro <identifier>+         -- Parse identifiers only
exact <term>                -- Parse full term
apply <term>                -- Parse full term
cases <identifier>          -- Parse identifier only
```

**Strategy 2: Uniform parsing** (simpler but less efficient)
```
tactic ::= tacticName term*

-- Where 'term' includes identifiers, applications, lambdas, etc.
-- Each tactic validates/interprets its arguments
```

---

## Proposed Grammar (Detailed)

### Full Grammar

```ebnf
(* Top level *)
definition ::= identifier ':' term ':=' tacticProof

tacticProof ::= 'by' NEWLINE INDENT tacticScript DEDENT

tacticScript ::= tacticCommand+

tacticCommand ::= tactic NEWLINE

(* Tactics *)
tactic ::=
  | 'intro' identifier
  | 'intros' identifier*
  | 'exact' term
  | 'apply' term
  | 'refine' term
  | 'assumption'
  | 'cases' identifier
  | 'induction' identifier
  | 'rewrite' term
  | 'constructor'
  | 'reflexivity'
  | 'have' identifier ':' term ':=' term

(* Terms - reuse existing term grammar *)
term ::= ... (existing LeanUI term grammar)
```

---

## Parsing Strategy

### Recommended Approach: Hybrid

1. **Parse tactic name** first (always an identifier)
2. **Dispatch to tactic-specific argument parser** based on name:
   - `intro`, `intros`, `cases`, `induction` → parse identifier list
   - `exact`, `apply`, `refine`, `rewrite` → parse full term
   - `assumption`, `constructor`, `reflexivity` → no arguments
   - `have` → parse identifier, `:`, term, `:=`, term

### Parser Pseudocode

```typescript
parseTactic(): TacticCommand {
  const name = this.consume('identifier').lexeme;

  switch (name) {
    case 'intro':
      const id = this.consume('identifier').lexeme;
      return { name: 'intro', args: [{ tag: 'Const', name: id }] };

    case 'intros':
      const ids: string[] = [];
      while (this.check('identifier') && !this.isAtNewline()) {
        ids.push(this.consume('identifier').lexeme);
      }
      return { name: 'intros', args: ids.map(id => ({ tag: 'Const', name: id })) };

    case 'exact':
    case 'apply':
    case 'refine':
    case 'rewrite':
      const term = this.parseTerm();
      return { name, args: [term] };

    case 'assumption':
    case 'constructor':
    case 'reflexivity':
      return { name, args: [] };

    case 'have':
      const hypName = this.consume('identifier').lexeme;
      this.consume(':');
      const hypType = this.parseTerm();
      this.consume(':=');
      const hypProof = this.parseTerm();
      return {
        name: 'have',
        args: [
          { tag: 'Const', name: hypName },
          hypType,
          hypProof
        ]
      };

    default:
      throw this.error(`Unknown tactic: ${name}`);
  }
}
```

---

## Argument Interpretation

When building tactics from parsed syntax:

```typescript
function buildTactic(cmd: TacticCommand, env: TCEnv): Tactic {
  switch (cmd.name) {
    case 'intro':
      // args[0] is a Const node with the name
      const name = (cmd.args[0] as TConst).name;
      return new IntroTactic(name);

    case 'intros':
      // args is array of Const nodes
      const names = cmd.args.map(arg => (arg as TConst).name);
      return new IntrosTactic(names);

    case 'exact':
    case 'apply':
      // args[0] is the full elaborated term
      const term = cmd.args[0];
      return cmd.name === 'exact'
        ? new ExactTactic(term)
        : new ApplyTactic(term);

    case 'assumption':
      return new AssumptionTactic();

    // ... etc
  }
}
```

---

## Key Design Decisions

### 1. **Identifiers vs. Terms**

**Question**: Should `exact x` parse `x` as an identifier or a term?

**Answer**: **Always as a term**. An identifier is just a term (`Const` or `Var` after elaboration).

This means:
- `exact x` → parses `x` as term `{ tag: 'Const', name: 'x' }`
- `exact (f x)` → parses as term `{ tag: 'App', fn: ..., arg: ... }`
- `intro x` → parses `x` as identifier only (special case)

### 2. **Whitespace-Separated vs. Parenthesized**

**Question**: Should arguments require parentheses or be whitespace-separated?

**Answer**: **Whitespace-separated** (like Lean/Coq):
```
exact f x y        ✓ (parses as term application)
exact (f x y)      ✓ (explicitly parenthesized)
apply f            ✓
intros a b c       ✓
```

**Not**:
```
exact(f, x, y)     ✗ (comma-separated arguments)
```

### 3. **One Tactic Per Line**

**Question**: Can multiple tactics be on one line?

**Answer**: **One per line** (for now, for simplicity):
```
by
  intro x
  exact x
```

**Not**:
```
by intro x; exact x     ✗ (no semicolons for now)
```

Future: could add `;` for single-line sequencing.

---

## Examples with Full AST

### Example: `exact (f x)`

**Source:**
```
proof : A := by
  exact (f x)
```

**Parsed TacticCommand:**
```typescript
{
  name: 'exact',
  args: [
    {
      tag: 'App',
      fn: { tag: 'Const', name: 'f' },
      arg: { tag: 'Const', name: 'x' }
    }
  ]
}
```

**Elaborated to TTK:**
```typescript
{
  name: 'exact',
  args: [
    {
      tag: 'App',
      fn: { tag: 'Var', index: 1 },  // f resolved to de Bruijn index
      arg: { tag: 'Var', index: 0 }  // x resolved to de Bruijn index
    }
  ]
}
```

---

## Next Steps

1. ✅ Define TT types for tactics (TacticBlock, TacticCommand)
2. ✅ Implement parser for `by` keyword and tactic blocks
3. ✅ Implement tactic-specific argument parsing
4. ✅ Integrate with elaboration (TT → TTK for tactic arguments)
5. ✅ Integrate with type checker (execute tactics)
6. ✅ Test with `modusPonens` example

---

## Summary

**Key Points:**
- Tactics can take **identifiers**, **full terms**, or **no arguments**
- Parse strategy: **dispatch based on tactic name**
- Arguments are **whitespace-separated**
- Terms in tactic arguments follow **existing term grammar**
- Elaboration converts tactic arguments from TT → TTK just like normal terms
