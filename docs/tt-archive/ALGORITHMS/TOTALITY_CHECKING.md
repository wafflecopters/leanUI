# Totality Checking via Pattern Trie Construction

## Overview

Totality checking verifies that a function handles all possible inputs. We build a **pattern trie** from the clauses by walking patterns left-to-right in depth-first order, then check for:

1. **Missing patterns** — inputs that no clause handles (marked as `Uncovered`)
2. **Unreachable clauses** — clauses that can never match (already covered by earlier clauses)
3. **Absurd cases** — patterns that are type-theoretically impossible (via LHS unification)

---

## Data Structures

### Patterns (TTKPattern)

```typescript
type TTKPattern =
  | { tag: 'PVar'; name: string }
  | { tag: 'PWild'; name: string }
  | { tag: 'PCtor'; name: string; args: TTKPattern[] }
```

### Mutable Pattern Trie

During construction, we use a mutable trie with shared references:

```typescript
interface MutableNode {
  content: NodeContent;
}

type NodeContent =
  | { tag: 'Wildcard'; child: MutableNode }
  | { tag: 'Split'; typeName: string; branches: Map<string, MutableNode> }
  | { tag: 'Leaf'; clauseIndex: number }
  | { tag: 'Uncovered' }
  | { tag: 'Absurd' }
```

### Immutable Case Tree (for visualization)

```typescript
type CaseTree =
  | { tag: 'Leaf'; clauseIndex: number }
  | { tag: 'Split'; typeName: string; branches: Map<string, CaseTree> }
  | { tag: 'Uncovered' }
  | { tag: 'Absurd' }
```

---

## Algorithm

### Step 1: Flatten Patterns (DFS Order)

Before adding a clause to the trie, we flatten its patterns by inlining constructor arguments depth-first:

```typescript
function flattenPatterns(patterns: TTKPattern[]): TTKPattern[] {
  const result: TTKPattern[] = [];
  for (const p of patterns) {
    flattenPattern(p, result);
  }
  return result;
}

function flattenPattern(pattern: TTKPattern, result: TTKPattern[]): void {
  result.push(pattern);
  if (pattern.tag === 'PCtor') {
    for (const arg of pattern.args) {
      flattenPattern(arg, result);
    }
  }
}
```

**Example:**
```
Clause: head A n (cons _ _ x _) = x
Patterns: [PVar(A), PVar(n), PCtor(cons, [PWild, PWild, PVar(x), PWild])]
Flattened: [PVar(A), PVar(n), PCtor(cons), PWild, PWild, PVar(x), PWild]
```

### Step 2: Add Clauses to Trie

For each clause, we walk the flattened patterns and build the trie:

```typescript
function addClauseToTree(
  node: MutableNode,
  patterns: TTKPattern[],
  patternIndex: number,
  clauseIndex: number,
  typeInfo: TypeInfoMap,
  ctorToType: ConstructorToTypeMap
): boolean {
  // End of patterns - mark this position
  if (patternIndex >= patterns.length) {
    if (node.content.tag === 'Uncovered') {
      node.content = { tag: 'Leaf', clauseIndex };
      return true;  // Clause is reachable
    }
    return false;   // Already covered
  }

  const pattern = patterns[patternIndex];

  switch (node.content.tag) {
    case 'Uncovered':
      if (pattern is Wildcard/Var) {
        // Create wildcard node and continue
        node.content = { tag: 'Wildcard', child: makeNode('Uncovered') };
        return addClauseToTree(child, patterns, patternIndex + 1, ...);
      } else {
        // Constructor - create Split for ALL constructors of this type
        const allCtors = getConstructorsForType(pattern.name);
        const branches = new Map();
        for (const ctor of allCtors) {
          const arity = getArity(ctor);
          // Each branch gets its own wildcard chain for constructor args
          branches.set(ctor, createWildcardChain(arity, makeNode('Uncovered')));
        }
        node.content = { tag: 'Split', typeName, branches };
        // Continue into the matching branch
        return addClauseToTree(branches.get(pattern.name), patterns, patternIndex + 1, ...);
      }

    case 'Wildcard':
      // Continue to child
      return addClauseToTree(node.content.child, patterns, patternIndex + 1, ...);

    case 'Split':
      if (pattern is Wildcard/Var) {
        // Clause has wildcard but tree has split - recurse into ALL branches
        for (const [ctorName, branch] of branches) {
          // Synthesize wildcard patterns for constructor args
          addClauseToTree(branch, synthesizedPatterns, patternIndex + 1, ...);
        }
      } else {
        // Constructor - go into matching branch only
        return addClauseToTree(branches.get(pattern.name), patterns, patternIndex + 1, ...);
      }

    case 'Leaf':
      return false;  // Already covered by earlier clause
  }
}
```

### Step 3: Mark Absurd Cases

After building the trie, we walk it to find `Uncovered` nodes and check if they're absurd:

```typescript
function markAbsurdInMutableTree(
  node: MutableNode,
  currentPath: TTKPattern[],
  checker: AbsurdityChecker
): void {
  switch (node.content.tag) {
    case 'Uncovered':
      if (checker(currentPath)) {
        node.content = { tag: 'Absurd' };
      }
      break;

    case 'Wildcard':
      currentPath.push({ tag: 'PWild', name: '_' });
      markAbsurdInMutableTree(child, currentPath, checker);
      currentPath.pop();
      break;

    case 'Split':
      for (const [ctorName, branch] of branches) {
        const arity = countWildcardsAtStart(branch);
        const args = Array(arity).fill({ tag: 'PWild' });
        currentPath.push({ tag: 'PCtor', name: ctorName, args });
        markAbsurdInMutableTree(skipWildcards(branch, arity), currentPath, checker);
        currentPath.pop();
      }
      break;
  }
}
```

The `AbsurdityChecker` uses LHS pattern unification - if unifying the patterns with the expected type fails, the case is absurd.

### Step 3b: Agda-Style Recursive Splitting

Basic absurdity checking only catches cases where the explicit patterns conflict. But some cases are absurd due to **remaining arguments** that have no valid constructors.

Consider `nth : (A : Type) -> (n : Nat) -> Vec A n -> Fin n -> A`:
- When the Vec argument is `VNil`, we have `n = Zero` (from `VNil : Vec A Zero`)
- The Fin argument must then be `Fin Zero`
- But `Fin Zero` is uninhabited! Both constructors require `Fin (Succ m)`:
  - `FZero : (m : Nat) -> Fin (Succ m)` — requires `Succ m = Zero` → conflict
  - `FSucc : (m : Nat) -> Fin m -> Fin (Succ m)` — requires `Succ m = Zero` → conflict

The enhanced absurdity checker handles this by **splitting on remaining arguments**:

```typescript
function absurdityChecker(patterns: TTKPattern[]): boolean {
  // Pad patterns with wildcards to match function arity
  const paddedPatterns = padToArity(patterns, functionType);

  // Basic check: do the explicit patterns conflict?
  if (arePatternsAbsurd(paddedPatterns, functionType)) {
    return true;
  }

  // Agda-style: try splitting on each padded wildcard position
  for (let pos = patterns.length; pos < expectedArgCount; pos++) {
    const argType = getTypeAtPosition(functionType, pos);
    const inductiveType = extractInductiveTypeName(argType);

    if (inductiveType) {
      let allConstructorsFail = true;

      for (const ctor of constructorsOf(inductiveType)) {
        // Replace wildcard at pos with this constructor
        const newPatterns = [...patterns, constructorPattern(ctor)];

        // If this constructor works, the case isn't absurd
        if (!arePatternsAbsurd(newPatterns, functionType)) {
          allConstructorsFail = false;
          break;
        }
      }

      // If ALL constructors fail at this position → case is absurd
      if (allConstructorsFail) {
        return true;
      }
    }
  }

  return false;
}
```

**Key insight from Agda**: We only split **once** per position. We don't recursively expand constructor arguments. This guarantees termination while still catching common absurdity patterns like `Fin Zero`.

### Step 4: Convert to Immutable CaseTree

Finally, convert the mutable trie to an immutable CaseTree, collapsing Wildcard nodes:

```typescript
function mutableToCaseTree(node: MutableNode): CaseTree {
  switch (node.content.tag) {
    case 'Leaf':     return { tag: 'Leaf', clauseIndex };
    case 'Uncovered': return { tag: 'Uncovered' };
    case 'Absurd':   return { tag: 'Absurd' };
    case 'Wildcard': return mutableToCaseTree(child);  // Collapse
    case 'Split':    return { tag: 'Split', branches: ... };
  }
}
```

---

## Trace: `head` Function

### Input

```tt
inductive Vec : Type -> Nat -> Type where
  | nil : (A : Type) -> Vec A Zero
  | cons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

head : (A : Type) -> (n : Nat) -> Vec A (Succ n) -> A
head A n (cons _ _ x _) = x
```

### Flattened Patterns

```
Clause 0: [PVar(A), PVar(n), PCtor(cons), PWild, PWild, PVar(x), PWild]
```

### Building the Trie

1. **Start:** root = `Uncovered`

2. **Pattern 0: PVar(A)** at `Uncovered`
   - Create `Wildcard(child1)`, continue to child1

3. **Pattern 1: PVar(n)** at `Uncovered`
   - Create `Wildcard(child2)`, continue to child2

4. **Pattern 2: PCtor(cons)** at `Uncovered`
   - Vec has constructors: `nil` (arity 1), `cons` (arity 4)
   - Create `Split(Vec, { nil: W→Uncovered, cons: W→W→W→W→Uncovered })`
   - Continue into `cons` branch

5. **Patterns 3-6: PWild, PWild, PVar(x), PWild** through wildcards
   - Walk through the 4 wildcards in cons branch
   - Mark end as `Leaf(0)`

### Trie After Building

```
Wildcard → Wildcard → Split(Vec)
                        nil:  Wildcard → Uncovered
                        cons: Wildcard → Wildcard → Wildcard → Wildcard → Leaf(0)
```

### Absurdity Checking

Walk the trie to find uncovered patterns:
- Path to `nil` branch: `[PWild, PWild, PCtor(nil, [PWild])]`

Check absurdity:
- Type is `(A : Type) -> (n : Nat) -> Vec A (Succ n) -> A`
- Pattern `nil` gives type `Vec A Zero`
- Expected: `Vec A (Succ n)`
- Unify `Zero` with `Succ n` → **FAILS**
- Mark as `Absurd`

### Final Case Tree

```
Split(Vec)
  nil:  → absurd
  cons: → clause 0
```

**Result:** Exhaustive (nil is absurd, cons is covered)

---

## Trace: `plus` Function

### Input

```tt
plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)
```

### Flattened Patterns

```
Clause 0: [PCtor(Zero), PVar(b)]
Clause 1: [PCtor(Succ), PVar(a), PVar(b)]
```

### Building the Trie

1. **Add Clause 0:**
   - Pattern 0: `Zero` at `Uncovered`
   - Create `Split(Nat, { Zero: Uncovered, Succ: W→Uncovered })`
   - Continue into `Zero` branch
   - Pattern 1: `PVar(b)` at `Uncovered`
   - Create `Wildcard(child)`, mark child as `Leaf(0)`

2. **Add Clause 1:**
   - Pattern 0: `Succ` at `Split`
   - Go into `Succ` branch (which is `Wildcard(Uncovered)`)
   - Pattern 1: `PVar(a)` at `Wildcard`
   - Continue to child (`Uncovered`)
   - Pattern 2: `PVar(b)` at `Uncovered`
   - Create `Wildcard(child)`, mark child as `Leaf(1)`

### Final Case Tree

```
Split(Nat)
  Zero: → clause 0
  Succ: → clause 1
```

**Result:** Exhaustive, no unreachable clauses

---

## Trace: `nth` Function (Recursive Splitting)

This example demonstrates the Agda-style recursive splitting for detecting absurdity.

### Input

```tt
inductive Vec : Type -> Nat -> Type where
  | VNil : (A : Type) -> Vec A Zero
  | VCons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n)

inductive Fin : Nat -> Type where
  | FZero : (n : Nat) -> Fin (Succ n)
  | FSucc : (n : Nat) -> Fin n -> Fin (Succ n)

nth : (A : Type) -> (n : Nat) -> Vec A n -> Fin n -> A
nth A _ (VCons _ _ h _) (FZero _) = h
nth A _ (VCons _ _ _ tail) (FSucc _ f) = nth A _ tail f
```

### Case Tree After Building

```
Wildcard → Wildcard → Split(Vec)
  VNil:  Wildcard → Uncovered      [4th arg (Fin) is missing!]
  VCons: Wildcard → ... → Split(Fin)
    FZero: → clause 0
    FSucc: → clause 1
```

### Absurdity Checking for VNil

Path to VNil's Uncovered: `[PWild, PWild, PCtor(VNil, [PWild])]`

**Basic check**: The path only has 3 patterns, but `nth` has 4 arguments. Pad with wildcard:
- Padded: `[PWild, PWild, PCtor(VNil, [PWild]), PWild]`
- This succeeds (wildcards match anything) → NOT absurd by basic check

**Recursive splitting on position 3** (the padded Fin argument):

The type at position 3 is `Fin n`. After VNil constrains `n = Zero`, it becomes `Fin Zero`.

Try each Fin constructor:

1. **Try FZero**: `[PWild, PWild, PCtor(VNil, [PWild]), PCtor(FZero, [PWild])]`
   - FZero : `(m : Nat) -> Fin (Succ m)`
   - VNil constrains `n = Zero`
   - FZero requires `Fin (Succ m)`, unify with `Fin n = Fin Zero`
   - `Succ m = Zero` → **CONFLICT!** → absurd

2. **Try FSucc**: `[PWild, PWild, PCtor(VNil, [PWild]), PCtor(FSucc, [PWild, PWild])]`
   - FSucc : `(m : Nat) -> Fin m -> Fin (Succ m)`
   - Same conflict: `Succ m = Zero` → **CONFLICT!** → absurd

**All constructors of Fin fail** → VNil case is absurd!

### Final Case Tree

```
Split(Vec)
  VNil:  → absurd
  VCons: Split(Fin)
    FZero: → clause 0
    FSucc: → clause 1
```

**Result:** Exhaustive (VNil is absurd because Fin Zero is uninhabited)

---

## Key Design Decisions

### Why DFS Flattening?

Flattening patterns depth-first means constructor arguments are processed immediately after the constructor. This allows the trie to naturally represent nested patterns:

```
Pattern: Succ(Succ(n))
Flattened: [Succ, Succ, n]
Trie path: Split(Nat) → Succ → Split(Nat) → Succ → Wildcard → ...
```

### Why No Sharing Between Constructors?

Initially we tried sharing a "rest" node between all constructor branches. This fails because constructors have different arities:

```
nil : Vec A Zero           (arity 1)
cons : A -> Vec A n -> ... (arity 4)
```

After `nil`, we have 1 pattern consumed. After `cons`, we have 4 patterns consumed. Sharing would conflate positions in the flattened pattern list.

### Why Mark Absurdity on Mutable Tree?

The absurdity checker needs the full pattern path including constructor arities. When converting to CaseTree, we collapse Wildcard nodes, losing arity information. By marking absurdity before conversion, we preserve the correct patterns.

---

## Summary

1. **Flatten patterns** — inline constructor args depth-first
2. **Build trie incrementally** — add each clause by walking flattened patterns
3. **On constructor at Uncovered** — create Split with ALL constructors, each with wildcard chain
4. **On wildcard at Split** — recurse into ALL branches
5. **Mark absurd cases** — use LHS unification to detect impossible patterns:
   - First try basic unification with the current patterns
   - If that succeeds, try Agda-style recursive splitting on remaining arguments
   - If ALL constructors of any remaining argument fail unification → absurd
6. **Convert to CaseTree** — collapse wildcards for visualization
7. **Check exhaustiveness** — tree is exhaustive if all leaves are Leaf or Absurd
