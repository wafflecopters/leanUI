# Totality Checking via Case-Split Trees

## Overview

Totality checking verifies that a function handles all possible inputs. We build a **case-split tree** from the clauses, then check for:

1. **Missing patterns** — inputs that no clause handles
2. **Useless clauses** — clauses that can never match (already covered by earlier clauses)

---

## Data Structures

### Pattern

```typescript
type Pattern =
  | { tag: 'Var', name: string }
  | { tag: 'Con', name: string, args: Pattern[] }
```

### Clause

```typescript
type Clause = {
  index: number;
  patterns: Pattern[];
}
```

### Case-Split Tree

```typescript
type CaseSplitTree =
  | { tag: 'Leaf', clauseIndex: number }
  | { tag: 'Split', column: number, cases: Map<string, CaseSplitTree> }
  | { tag: 'Uncovered' }
```

---

## Algorithm

### Main Entry Point

```typescript
function buildCoverageTree(
  clauses: Clause[],
  typeInfo: TypeInfo
): { tree: CaseSplitTree, uselessClauses: number[], missingPatterns: Pattern[][] } {
  
  const tree = buildTree(clauses, typeInfo);
  
  const usedClauses = new Set<number>();
  collectUsedClauses(tree, usedClauses);
  const uselessClauses = clauses
    .map((_, i) => i)
    .filter(i => !usedClauses.has(i));
  
  const missingPatterns = collectUncoveredPaths(tree, [], typeInfo);
  
  return { tree, uselessClauses, missingPatterns };
}
```

### Building the Tree

```typescript
function buildTree(clauses: Clause[], typeInfo: TypeInfo): CaseSplitTree {
  // Base case: no clauses → uncovered
  if (clauses.length === 0) {
    return { tag: 'Uncovered' };
  }
  
  // Base case: no patterns left → first clause wins
  if (clauses[0].patterns.length === 0) {
    return { tag: 'Leaf', clauseIndex: clauses[0].index };
  }
  
  // Find first column with a constructor pattern
  const splitCol = findSplitColumn(clauses);
  
  if (splitCol === null) {
    // All columns are variables → first clause wins
    return { tag: 'Leaf', clauseIndex: clauses[0].index };
  }
  
  // Get all constructors for this column's type
  const allConstructors = typeInfo.getConstructors(splitCol);
  
  // Build a case for each constructor
  const cases = new Map<string, CaseSplitTree>();
  
  for (const conName of allConstructors) {
    const arity = typeInfo.getConstructorArity(conName);
    const specialized = specializeClauses(clauses, splitCol, conName, arity);
    cases.set(conName, buildTree(specialized, typeInfo));
  }
  
  return { tag: 'Split', column: splitCol, cases };
}
```

### Finding a Split Column

```typescript
function findSplitColumn(clauses: Clause[]): number | null {
  const numCols = clauses[0].patterns.length;
  
  for (let col = 0; col < numCols; col++) {
    for (const clause of clauses) {
      if (clause.patterns[col].tag === 'Con') {
        return col;
      }
    }
  }
  
  return null;
}
```

### Specializing Clauses

When splitting on column `col` with constructor `C` of arity `k`:
- Clauses with `C` in that column: replace `C(args...)` with `args...`
- Clauses with `Var` in that column: replace `Var` with `k` fresh variables
- Clauses with different constructor: discard

```typescript
function specializeClauses(
  clauses: Clause[],
  col: number,
  conName: string,
  arity: number
): Clause[] {
  const result: Clause[] = [];
  
  for (const clause of clauses) {
    const pattern = clause.patterns[col];
    
    if (pattern.tag === 'Con' && pattern.name === conName) {
      // Matching constructor: inline its arguments
      const newPatterns = [
        ...clause.patterns.slice(0, col),
        ...pattern.args,
        ...clause.patterns.slice(col + 1)
      ];
      result.push({ index: clause.index, patterns: newPatterns });
    } else if (pattern.tag === 'Var') {
      // Variable: expand to fresh variables
      const freshVars: Pattern[] = Array.from({ length: arity }, (_, i) =>
        ({ tag: 'Var', name: `_${i}` }));
      const newPatterns = [
        ...clause.patterns.slice(0, col),
        ...freshVars,
        ...clause.patterns.slice(col + 1)
      ];
      result.push({ index: clause.index, patterns: newPatterns });
    }
    // Otherwise: different constructor, clause is discarded
  }
  
  return result;
}
```

### Collecting Used Clauses

```typescript
function collectUsedClauses(tree: CaseSplitTree, used: Set<number>): void {
  if (tree.tag === 'Leaf') {
    used.add(tree.clauseIndex);
  } else if (tree.tag === 'Split') {
    for (const subtree of tree.cases.values()) {
      collectUsedClauses(subtree, used);
    }
  }
}
```

### Collecting Uncovered Paths

```typescript
function collectUncoveredPaths(
  tree: CaseSplitTree,
  pathSoFar: Pattern[],
  typeInfo: TypeInfo
): Pattern[][] {
  if (tree.tag === 'Uncovered') {
    return [pathSoFar];
  }
  
  if (tree.tag === 'Leaf') {
    return [];
  }
  
  const results: Pattern[][] = [];
  
  for (const [conName, subtree] of tree.cases) {
    const arity = typeInfo.getConstructorArity(conName);
    const freshVars: Pattern[] = Array.from({ length: arity }, (_, i) =>
      ({ tag: 'Var', name: `_${i}` }));
    const conPattern: Pattern = { tag: 'Con', name: conName, args: freshVars };
    
    results.push(...collectUncoveredPaths(subtree, [...pathSoFar, conPattern], typeInfo));
  }
  
  return results;
}
```

---

## Trace: `nth` Function

### Input

```tt
nth : (A : Type) -> (n : Nat) -> Vec A n -> Fin n -> A
nth A (Succ n) (VCons A n h tail) (FZero n) = h
nth A (Succ (Succ n)) (VCons A (Succ n) h tail) (FSucc (Succ n) f) = nth A (Succ n) tail f
```

### Initial Clauses

| Clause | Col 0 | Col 1 | Col 2 | Col 3 |
|--------|-------|-------|-------|-------|
| 0 | `Var A` | `Succ(Var n)` | `VCons(A,n,h,tail)` | `FZero(Var n)` |
| 1 | `Var A` | `Succ(Succ(Var n))` | `VCons(A,Succ(n),h,tail)` | `FSucc(Succ(n),Var f)` |

### Step 1: Find split column

- Col 0: all `Var` → skip
- Col 1: has `Con Succ` → **split on Col 1**

### Step 2: Split on Col 1

Constructors for Nat: `{Zero, Succ}`

**Specialize for `Zero` (arity 0):**

- Clause 0: `Succ(...)` ≠ `Zero` → discard
- Clause 1: `Succ(...)` ≠ `Zero` → discard

Result: no clauses → **Uncovered**

**Specialize for `Succ` (arity 1):**

- Clause 0: `Succ(Var n)` → inline → `[Var A, Var n, VCons(...), FZero(...)]`
- Clause 1: `Succ(Succ(Var n))` → inline → `[Var A, Succ(Var n), VCons(...), FSucc(...)]`

| Clause | Col 0 | Col 1 | Col 2 | Col 3 |
|--------|-------|-------|-------|-------|
| 0 | `Var A` | `Var n` | `VCons(A,n,h,tail)` | `FZero(Var n)` |
| 1 | `Var A` | `Succ(Var n)` | `VCons(A,Succ(n),h,tail)` | `FSucc(Succ(n),Var f)` |

### Step 3: Recurse into Succ case

Find split column:
- Col 0: all `Var` → skip
- Col 1: Clause 1 has `Con Succ` → **split on Col 1**

**Specialize for `Zero` (arity 0):**

- Clause 0: `Var n` matches → expand with 0 fresh vars → `[Var A, VCons(...), FZero(...)]`
- Clause 1: `Succ(...)` ≠ `Zero` → discard

| Clause | Col 0 | Col 1 | Col 2 |
|--------|-------|-------|-------|
| 0 | `Var A` | `VCons(A,n,h,tail)` | `FZero(Var n)` |

**Specialize for `Succ` (arity 1):**

- Clause 0: `Var n` matches → expand with 1 fresh var → `[Var A, Var _, VCons(...), FZero(...)]`
- Clause 1: `Succ(Var n)` → inline → `[Var A, Var n, VCons(...), FSucc(...)]`

| Clause | Col 0 | Col 1 | Col 2 | Col 3 |
|--------|-------|-------|-------|-------|
| 0 | `Var A` | `Var _` | `VCons(A,n,h,tail)` | `FZero(Var n)` |
| 1 | `Var A` | `Var n` | `VCons(A,Succ(n),h,tail)` | `FSucc(Succ(n),Var f)` |

### Step 4: Recurse into Succ→Zero case

One clause remains. Find split column:
- Col 0: `Var` → skip
- Col 1: `Con VCons` → **split on Col 1**

**Specialize for `VNil` (arity 0):**

- Clause 0: `VCons(...)` ≠ `VNil` → discard

Result: no clauses → **Uncovered**

**Specialize for `VCons` (arity 4):**

- Clause 0: `VCons(A,n,h,tail)` → inline → `[Var A, Var A, Var n, Var h, Var tail, FZero(Var n)]`

| Clause | Col 0 | Col 1 | Col 2 | Col 3 | Col 4 | Col 5 |
|--------|-------|-------|-------|-------|-------|-------|
| 0 | `Var A` | `Var A` | `Var n` | `Var h` | `Var tail` | `FZero(Var n)` |

Continue splitting on Col 5 (first Con is FZero).

**Specialize for `FZero` (arity 1):**

- Clause 0: `FZero(Var n)` → inline → all `Var`

All columns are Var → **Leaf(0)**

**Specialize for `FSucc` (arity 2):**

- Clause 0: `FZero(...)` ≠ `FSucc` → discard

Result: no clauses → **Uncovered**

### Step 5: Recurse into Succ→Succ case

| Clause | Col 0 | Col 1 | Col 2 | Col 3 |
|--------|-------|-------|-------|-------|
| 0 | `Var A` | `Var _` | `VCons(A,n,h,tail)` | `FZero(Var n)` |
| 1 | `Var A` | `Var n` | `VCons(A,Succ(n),h,tail)` | `FSucc(Succ(n),Var f)` |

Split on Col 2 (both have VCons).

**Specialize for `VNil` (arity 0):**

Both clauses have `VCons` → discard both

Result: no clauses → **Uncovered**

**Specialize for `VCons` (arity 4):**

- Clause 0: inline → `[Var A, Var _, Var A, Var n, Var h, Var tail, FZero(Var n)]`
- Clause 1: inline → `[Var A, Var n, Var A, Succ(Var n), Var h, Var tail, FSucc(Succ(n), Var f)]`

| Clause | Col 0 | Col 1 | Col 2 | Col 3 | Col 4 | Col 5 | Col 6 |
|--------|-------|-------|-------|-------|-------|-------|-------|
| 0 | `Var A` | `Var _` | `Var A` | `Var n` | `Var h` | `Var tail` | `FZero(Var n)` |
| 1 | `Var A` | `Var n` | `Var A` | `Succ(Var n)` | `Var h` | `Var tail` | `FSucc(...)` |

Split on Col 3 (Clause 1 has Succ).

**Specialize for `Zero` (arity 0):**

- Clause 0: `Var n` → expand → keeps clause
- Clause 1: `Succ(...)` ≠ `Zero` → discard

Remaining: just Clause 0. Continue to split on Col 6 (FZero).

FZero case: **Leaf(0)**
FSucc case: **Uncovered**

**Specialize for `Succ` (arity 1):**

- Clause 0: `Var n` → expand with 1 fresh var
- Clause 1: `Succ(Var n)` → inline

| Clause | Col 0 | Col 1 | Col 2 | Col 3 | Col 4 | Col 5 | Col 6 |
|--------|-------|-------|-------|-------|-------|-------|-------|
| 0 | `Var A` | `Var _` | `Var A` | `Var _` | `Var h` | `Var tail` | `FZero(Var n)` |
| 1 | `Var A` | `Var n` | `Var A` | `Var n` | `Var h` | `Var tail` | `FSucc(...)` |

Split on Col 6 (FZero vs FSucc).

FZero case: Clause 0 matches, Clause 1 discarded → **Leaf(0)**
FSucc case: Clause 0 discarded, Clause 1 matches → continue → **Leaf(1)**

### Final Tree

```
Split(col 1: Nat, {
  Zero → Uncovered,
  Succ → Split(col 1: Nat, {
    Zero → Split(col 1: Vec, {
      VNil → Uncovered,
      VCons → Split(col 5: Fin, {
        FZero → Leaf(0),
        FSucc → Uncovered
      })
    }),
    Succ → Split(col 2: Vec, {
      VNil → Uncovered,
      VCons → Split(col 3: Nat, {
        Zero → Split(col 6: Fin, {
          FZero → Leaf(0),
          FSucc → Uncovered
        }),
        Succ → Split(col 6: Fin, {
          FZero → Leaf(0),
          FSucc → Leaf(1)
        })
      })
    })
  })
})
```

### Results

**Useless clauses:** none (both 0 and 1 appear in leaves)

**Uncovered paths:**
- `Zero` (n = 0)
- `Succ(Zero), VNil` (n = 1, empty vector)
- `Succ(Zero), VCons(...), FSucc(...)` (n = 1, index too large)
- `Succ(Succ(_)), VNil` (n ≥ 2, empty vector)
- `Succ(Succ(Zero)), VCons(...), FSucc(...)` (inner n = 0, index too large)

These are all **impossible patterns** due to dependent type constraints (e.g., `Vec A Zero` must be `VNil`, `Fin Zero` is uninhabited). A dependent coverage checker would rule these out using unification.

---

## Summary

1. **Start with clauses** — each clause has a list of patterns (one per argument)
2. **Find split column** — first column with any constructor pattern
3. **Specialize clauses** for each constructor of that column's type:
   - Matching constructor: inline its arguments
   - Variable: expand to fresh variables
   - Different constructor: discard clause
4. **Recurse** until no clauses (Uncovered) or all patterns are variables (Leaf)
5. **Collect results:**
   - Useless clauses: clause indices not in any Leaf
   - Missing patterns: paths to Uncovered nodes