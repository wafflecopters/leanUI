# Nested Case Patterns Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Support nested destructuring in `cases` tactic patterns, e.g., `| MkDPair δF (MkPair pos bound) =>` to destructure a DPair whose second component is a Pair — in one step, with proper variable binding.

**Architecture:** Extend the parser's case branch pattern to accept nested constructor patterns (parenthesized sub-patterns). At the tactic engine level, desugar nested patterns into sequential `cases` applications. The proof tree stores nested patterns; the prose view shows the full flat pattern in the case label.

**Tech Stack:** TypeScript, Vitest

---

## Design

### Syntax

Current (flat):
```
cases x with
| MkDPair a b => ...
```

New (nested):
```
cases x with
| MkDPair a (MkPair pos bound) => ...
```

Each branch param can be either:
- An identifier (simple binding): `a`, `b`, `δF`
- A parenthesized constructor pattern: `(MkPair pos bound)`, `(MkDPair x (MkPair y z))`

### Data Model

Replace `CaseBranch.params: string[]` with a richer structure:

```typescript
export type CasePattern =
  | { tag: 'var'; name: string }
  | { tag: 'ctor'; constructor: string; params: CasePattern[] };

export interface CaseBranch {
  constructor: string;       // Top-level constructor name
  params: CasePattern[];     // Each param is either a var or a nested pattern
  tactics: TacticCommand[];
}
```

For backwards compatibility, a flat pattern like `| MkDPair a b =>` becomes `params: [{tag:'var',name:'a'}, {tag:'var',name:'b'}]`.

### Desugaring

At the tactic engine level, a nested pattern gets desugared to sequential `cases`. For example:

```
cases p with
| MkDPair a (MkPair pos bound) => tactics
```

Desugars to:

```
cases p with
| MkDPair a tmp_snd =>
  cases tmp_snd with
  | MkPair pos bound => tactics
```

The `tmp_snd` is a fresh name introduced by the desugarer for each nested pattern. After desugaring, the existing `cases` tactic machinery handles everything.

### Scope

**In scope:**
- Parser support for nested patterns in case branches
- Desugaring to sequential cases at tactic-to-tree conversion time
- Updates to `CaseBranch` type and all consumers
- Tests for parsing, desugaring, and end-to-end proof compilation

**Out of scope:**
- Wildcard patterns (`_`)
- Literal patterns (`0`, `Zero`)
- Or-patterns (`a | b => ...`)
- Nested patterns in `let` or `have` (only `cases`)

---

## File Map

| File | Change | Purpose |
|------|--------|---------|
| `src/compiler/surface.ts` | Modify | Add `CasePattern` type, update `CaseBranch` interface |
| `src/parser/parser.ts` | Modify | Parse nested patterns in case branches (parseCasePattern helper) |
| `src/parser/parser.test.ts` | Modify | Tests for nested pattern parsing |
| `src/proof-tree/tactic-to-tree.ts` | Modify | Desugar nested patterns to sequential cases |
| `src/proof-tree/proof-tree.ts` | Modify | `mkCase` accepts nested params if needed |
| `src/proof-tree/proof-prose.ts` | Modify | Render nested case labels correctly |
| `src/components/ProofTreeEditor.tsx` | Modify | Display nested case params in tree view |
| `src/compiler/elab.ts` | Review | Ensure case branch elaboration handles new types (may need no changes if desugared upstream) |
| `src/tactics/elaborate-tactic-arg.ts` | Review | Same |
| `src/test-programs/notation/nested-patterns.tt` | Create | End-to-end .tt test |
| `src/presets/real-analysis.ts` | Modify | Update limitAdd to use nested patterns |

---

### Task 1: Add `CasePattern` type

**Files:**
- Modify: `src/compiler/surface.ts` (add CasePattern type, update CaseBranch)

- [ ] **Step 1: Add CasePattern type to surface.ts**

In `src/compiler/surface.ts`, find the `CaseBranch` interface (around line 275) and add the `CasePattern` type before it:

```typescript
/**
 * A pattern in a case branch: either a variable binding or a nested constructor pattern.
 *
 * Examples:
 *   a               → { tag: 'var', name: 'a' }
 *   (MkPair x y)    → { tag: 'ctor', constructor: 'MkPair', params: [var x, var y] }
 *   (MkDPair x (MkPair y z)) → nested
 */
export type CasePattern =
  | { tag: 'var'; name: string }
  | { tag: 'ctor'; constructor: string; params: CasePattern[] };
```

Then update `CaseBranch`:

```typescript
export interface CaseBranch {
  constructor: string;
  params: CasePattern[];  // Was: string[]
  tactics: TacticCommand[];
}
```

- [ ] **Step 2: Run TypeScript check to find all consumers**

Run: `npx tsc --noEmit 2>&1 | head -30`
Expected: Errors from all files that use `CaseBranch.params` as `string[]`.

Record the list of errors — these are the files that need updating in subsequent tasks.

- [ ] **Step 3: Commit the type change**

```bash
git add src/compiler/surface.ts
git commit -m "feat: add CasePattern type for nested case patterns"
```

Note: Build will be broken until subsequent tasks update consumers. This is expected.

---

### Task 2: Helper function to convert flat patterns

Add a helper to convert old-style `string[]` params to `CasePattern[]` so existing code can be updated minimally.

**Files:**
- Modify: `src/compiler/surface.ts`

- [ ] **Step 1: Add the helper function**

In `src/compiler/surface.ts`, after the `CasePattern` type:

```typescript
/** Convert a flat string[] of param names to CasePattern[] (all variable bindings). */
export function flatParamsToCasePatterns(names: readonly string[]): CasePattern[] {
  return names.map(name => ({ tag: 'var' as const, name }));
}

/** Extract all variable names bound by a case pattern (recursive). */
export function patternVarNames(pattern: CasePattern): string[] {
  if (pattern.tag === 'var') return [pattern.name];
  const names: string[] = [];
  for (const sub of pattern.params) {
    names.push(...patternVarNames(sub));
  }
  return names;
}

/** Extract all variable names from a list of case patterns. */
export function allPatternVarNames(patterns: readonly CasePattern[]): string[] {
  const names: string[] = [];
  for (const p of patterns) names.push(...patternVarNames(p));
  return names;
}
```

- [ ] **Step 2: Commit**

```bash
git add src/compiler/surface.ts
git commit -m "feat: helpers for CasePattern (flatParamsToCasePatterns, patternVarNames)"
```

---

### Task 3: Update existing consumers to compile

Fix all existing consumers to work with `CasePattern[]` by using the flat conversion helper.

**Files:**
- Modify: files that use `CaseBranch.params` (find via tsc errors from Task 1)

- [ ] **Step 1: Find all consumers**

Run: `npx tsc --noEmit 2>&1 | grep "CaseBranch\|params" | head -40`

- [ ] **Step 2: For each consumer, update the usage**

For places that CREATE a CaseBranch with `params: ['a', 'b']`:
```typescript
// Old:
{ constructor: 'MkDPair', params: ['a', 'b'], tactics: [...] }

// New:
{ constructor: 'MkDPair', params: flatParamsToCasePatterns(['a', 'b']), tactics: [...] }
```

Import `flatParamsToCasePatterns` from `'../compiler/surface'`.

For places that READ `branch.params` expecting `string[]`:
```typescript
// Old:
const paramNames = branch.params;

// New:
const paramNames = allPatternVarNames(branch.params);
```

Import `allPatternVarNames` from `'../compiler/surface'`.

**Specific files to check:**
- `src/parser/parser.ts` — around line 4106 (case pattern parsing)
- `src/proof-tree/tactic-to-tree.ts` — `buildInductionNode`
- `src/compiler/elab.ts` — case branch elaboration (if any)
- `src/tactics/tactic-session.ts` — `applyCaseBranches`

For each file, apply the minimal change to make it compile. The parser will still only produce flat patterns — nested parsing comes in Task 4.

- [ ] **Step 3: Verify build is clean**

Run: `npx tsc --noEmit 2>&1 | head -10`
Expected: No errors.

- [ ] **Step 4: Run full test suite**

Run: `npm test 2>&1 | tail -5`
Expected: All tests pass (no new failures).

- [ ] **Step 5: Commit**

```bash
git add -A
git commit -m "refactor: update CaseBranch consumers for CasePattern type (flat only)"
```

---

### Task 4: Parser support for nested patterns

**Files:**
- Modify: `src/parser/parser.ts` (case branch parsing)
- Test: `src/parser/parser.test.ts`

- [ ] **Step 1: Write failing test**

In `src/parser/parser.test.ts`, add:

```typescript
describe('nested case patterns', () => {
  test('simple nested pattern: | MkDPair a (MkPair x y) =>', () => {
    const parser = new Parser();
    const decls = parser.parseDeclarations(`
test : Nat := by
  cases p with
  | MkDPair a (MkPair x y) =>
    exact a
`);
    const def = decls.find(d => d.name === 'test');
    const tactics = (def?.value as any).tactics;
    const casesCmd = tactics.find((t: any) => t.name === 'cases');
    expect(casesCmd.caseBranches).toHaveLength(1);
    const branch = casesCmd.caseBranches[0];
    expect(branch.constructor).toBe('MkDPair');
    expect(branch.params).toHaveLength(2);
    expect(branch.params[0]).toEqual({ tag: 'var', name: 'a' });
    expect(branch.params[1]).toEqual({
      tag: 'ctor',
      constructor: 'MkPair',
      params: [
        { tag: 'var', name: 'x' },
        { tag: 'var', name: 'y' },
      ],
    });
  });

  test('deeply nested pattern: | A (B (C x)) =>', () => {
    const parser = new Parser();
    const decls = parser.parseDeclarations(`
test : Nat := by
  cases p with
  | A (B (C x)) =>
    exact x
`);
    const def = decls.find(d => d.name === 'test');
    const tactics = (def?.value as any).tactics;
    const casesCmd = tactics.find((t: any) => t.name === 'cases');
    const branch = casesCmd.caseBranches[0];
    expect(branch.constructor).toBe('A');
    expect(branch.params[0]).toEqual({
      tag: 'ctor',
      constructor: 'B',
      params: [{
        tag: 'ctor',
        constructor: 'C',
        params: [{ tag: 'var', name: 'x' }],
      }],
    });
  });

  test('flat pattern still works: | MkPair a b =>', () => {
    const parser = new Parser();
    const decls = parser.parseDeclarations(`
test : Nat := by
  cases p with
  | MkPair a b =>
    exact a
`);
    const def = decls.find(d => d.name === 'test');
    const tactics = (def?.value as any).tactics;
    const casesCmd = tactics.find((t: any) => t.name === 'cases');
    const branch = casesCmd.caseBranches[0];
    expect(branch.params).toEqual([
      { tag: 'var', name: 'a' },
      { tag: 'var', name: 'b' },
    ]);
  });
});
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run src/parser/parser.test.ts -t "nested case patterns"`
Expected: FAIL (parser produces flat `{tag:'var',name:'(MkPair'}` or throws on the paren).

- [ ] **Step 3: Add parseCasePattern helper**

In `src/parser/parser.ts`, add a new private method on the `Parser` class. Find a good spot near the case parsing code (around line 4100):

```typescript
/**
 * Parse a case pattern: either an identifier or a parenthesized constructor application.
 *
 * Grammar:
 *   casePattern := IDENT                          // variable binding
 *                | '(' IDENT casePattern* ')'     // nested constructor
 */
private parseCasePattern(): CasePattern {
  if (this.current().type === 'LPAREN') {
    this.advance(); // consume '('
    // Expect constructor name
    if (this.current().type !== 'IDENT') {
      throw new ParseError(
        'Expected constructor name after (',
        this.current().line,
        this.current().col
      );
    }
    const ctorName = this.current().value;
    this.advance();
    // Parse nested params until ')'
    const nestedParams: CasePattern[] = [];
    while (this.current().type !== 'RPAREN' && this.current().type !== 'EOF') {
      nestedParams.push(this.parseCasePattern());
    }
    if (this.current().type !== 'RPAREN') {
      throw new ParseError(
        'Expected ) to close nested pattern',
        this.current().line,
        this.current().col
      );
    }
    this.advance(); // consume ')'
    return { tag: 'ctor', constructor: ctorName, params: nestedParams };
  }
  if (this.current().type === 'IDENT') {
    const name = this.current().value;
    this.advance();
    return { tag: 'var', name };
  }
  throw new ParseError(
    `Expected case pattern (identifier or parenthesized constructor), got ${this.current().type}`,
    this.current().line,
    this.current().col
  );
}
```

Import `CasePattern` at the top of parser.ts:

```typescript
import { ..., CasePattern } from '../compiler/surface';
```

- [ ] **Step 4: Replace flat pattern parsing with parseCasePattern calls**

In `src/parser/parser.ts`, find the cases branch parsing (around line 4104-4111) and replace the flat param loop:

```typescript
// OLD (lines ~4104-4111):
const params: string[] = [];
while (this.current().type === 'IDENT' && this.current().col > tacticToken.col) {
  const paramToken = this.current();
  params.push(this.current().value);
  this.recordRange([...caseBranchPath, { kind: 'field' as const, name: 'params' }, { kind: 'array' as const, index: params.length - 1 }], paramToken, paramToken);
  this.advance();
}

// NEW:
const params: CasePattern[] = [];
while ((this.current().type === 'IDENT' || this.current().type === 'LPAREN')
       && this.current().col > tacticToken.col) {
  params.push(this.parseCasePattern());
}
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `npx vitest run src/parser/parser.test.ts -t "nested case patterns"`
Expected: PASS (all 3 tests)

- [ ] **Step 6: Run full suite**

Run: `npx tsc --noEmit && npm test 2>&1 | tail -5`
Expected: All tests pass.

- [ ] **Step 7: Commit**

```bash
git add src/parser/parser.ts src/parser/parser.test.ts
git commit -m "feat: parse nested case patterns | Ctor a (SubCtor x y) =>"
```

---

### Task 5: Desugar nested patterns in tactic-to-tree

When converting parsed tactic commands to a proof tree, nested patterns get desugared into sequential `cases` applications.

**Files:**
- Modify: `src/proof-tree/tactic-to-tree.ts` (buildInductionNode)

- [ ] **Step 1: Write failing test**

Create `src/proof-tree/tactic-to-tree.test.ts` if it doesn't exist, or add to it:

```typescript
import { describe, test, expect } from 'vitest';
import { tacticCommandsToProofTree } from './tactic-to-tree';
import type { TacticCommand } from '../compiler/surface';

describe('nested case pattern desugaring', () => {
  test('| MkDPair a (MkPair x y) => desugars to nested cases', () => {
    // Simulating: cases p with | MkDPair a (MkPair x y) => exact a
    const cmd: TacticCommand = {
      name: 'cases',
      args: [{ tag: 'Const', name: 'p' }],
      caseBranches: [{
        constructor: 'MkDPair',
        params: [
          { tag: 'var', name: 'a' },
          { tag: 'ctor', constructor: 'MkPair', params: [
            { tag: 'var', name: 'x' },
            { tag: 'var', name: 'y' },
          ]},
        ],
        tactics: [{
          name: 'exact',
          args: [{ tag: 'Const', name: 'a' }],
        }],
      }],
    };

    const tree = tacticCommandsToProofTree([cmd]);

    // Outer node: cases p with | MkDPair a <freshvar> => (nested cases)
    expect(tree.tag).toBe('induction');
    if (tree.tag !== 'induction') return;
    expect(tree.isCases).toBe(true);
    expect(tree.cases).toHaveLength(1);
    const outerCase = tree.cases[0];
    expect(outerCase.constructorName).toBe('MkDPair');
    // Outer params: [a, <fresh>]
    expect(outerCase.constructorParamNames).toHaveLength(2);
    expect(outerCase.constructorParamNames?.[0]).toBe('a');
    const freshName = outerCase.constructorParamNames?.[1];
    expect(freshName).toMatch(/^_nested\d+$/);

    // Body should start with inner `cases` on the fresh name
    const innerBody = outerCase.body;
    expect(innerBody.tag).toBe('induction');
    if (innerBody.tag !== 'induction') return;
    expect(innerBody.scrutinee).toBe(freshName);
    expect(innerBody.cases).toHaveLength(1);
    expect(innerBody.cases[0].constructorName).toBe('MkPair');
    expect(innerBody.cases[0].constructorParamNames).toEqual(['x', 'y']);
  });
});
```

- [ ] **Step 2: Run test to verify it fails**

Run: `npx vitest run src/proof-tree/tactic-to-tree.test.ts`
Expected: FAIL (desugaring not implemented).

- [ ] **Step 3: Implement desugaring**

In `src/proof-tree/tactic-to-tree.ts`, find `buildInductionNode` and update it to handle nested patterns. Add a helper:

```typescript
import { CasePattern, CaseBranch, TacticCommand, mkConstTT } from '../compiler/surface';

let nestedFreshCounter = 0;
function freshNestedName(): string {
  return `_nested${nestedFreshCounter++}`;
}

/**
 * Desugar a case branch with nested patterns into a flat top-level pattern
 * plus nested `cases` tactic commands.
 *
 * Example:
 *   | MkDPair a (MkPair x y) => exact a
 * becomes:
 *   | MkDPair a _fresh1 =>
 *     cases _fresh1 with
 *     | MkPair x y => exact a
 */
function desugarNestedCaseBranch(branch: CaseBranch): CaseBranch {
  const flatParams: string[] = [];
  // Collect nested sub-patterns with the synthetic names we assigned
  const nestedSubs: Array<{ freshName: string; pattern: CasePattern & { tag: 'ctor' } }> = [];

  for (const param of branch.params) {
    if (param.tag === 'var') {
      flatParams.push(param.name);
    } else {
      // ctor: generate a fresh name and queue the sub-pattern for inner cases
      const freshName = freshNestedName();
      flatParams.push(freshName);
      nestedSubs.push({ freshName, pattern: param });
    }
  }

  if (nestedSubs.length === 0) {
    // No nesting — return branch unchanged (params already flat)
    return branch;
  }

  // Build inner tactics: for each nested sub, emit a `cases freshName with | Ctor ... => ...`
  // Chain them so each inner cases wraps the next. Innermost level has the original tactics.
  let innerTactics = branch.tactics;

  // Process in reverse so the outermost wrapping is applied last
  for (let i = nestedSubs.length - 1; i >= 0; i--) {
    const { freshName, pattern } = nestedSubs[i];
    // Recursively desugar the nested pattern into a CaseBranch
    const innerBranch: CaseBranch = desugarNestedCaseBranch({
      constructor: pattern.constructor,
      params: pattern.params,
      tactics: innerTactics,
    });
    const innerCases: TacticCommand = {
      name: 'cases',
      args: [mkConstTT(freshName)],
      caseBranches: [innerBranch],
    };
    innerTactics = [innerCases];
  }

  return {
    constructor: branch.constructor,
    params: flatParams.map(name => ({ tag: 'var' as const, name })),
    tactics: innerTactics,
  };
}
```

Then in `buildInductionNode`, apply desugaring to each branch before building the tree:

```typescript
// Find the existing code that maps branches:
// const cases = cmd.caseBranches.map(branch => {
//   const body = tacticCommandsToProofTree(branch.tactics);
//   return mkCase(branch.constructor, body, branch.constructor, branch.params);
// });

// Update to desugar first:
const cases = cmd.caseBranches.map(rawBranch => {
  const branch = desugarNestedCaseBranch(rawBranch);
  const body = tacticCommandsToProofTree(branch.tactics);
  // branch.params is now guaranteed flat (all tag:'var')
  const paramNames = branch.params.map(p => p.tag === 'var' ? p.name : '_err');
  return mkCase(branch.constructor, body, branch.constructor, paramNames);
});
```

- [ ] **Step 4: Run tests**

Run: `npx vitest run src/proof-tree/tactic-to-tree.test.ts`
Expected: PASS

- [ ] **Step 5: Run full suite**

Run: `npx tsc --noEmit && npm test 2>&1 | tail -5`
Expected: All tests pass.

- [ ] **Step 6: Commit**

```bash
git add src/proof-tree/tactic-to-tree.ts src/proof-tree/tactic-to-tree.test.ts
git commit -m "feat: desugar nested case patterns to sequential cases"
```

---

### Task 6: Desugar nested patterns in the tactic session too

The `TacticSession.applyCaseBranches` in `src/tactics/tactic-session.ts` also processes case branches — it runs at compile time to validate the proof. It needs the same desugaring so that nested patterns work during compilation, not just during UI replay.

**Files:**
- Modify: `src/tactics/tactic-session.ts`

- [ ] **Step 1: Write test**

Add to `src/tactics/tactic-session.test.ts`:

```typescript
test('nested case patterns compile successfully', () => {
  const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

add : Nat -> Nat -> Nat
add Zero m = m
add (Succ n) m = Succ (add n m)

record DPair {u v : ULevel} (A : Type u) (B : A -> Type v) : Type (UMax u v) where
  constructor MkDPair
  fst : A
  snd : B fst

record Pair (A B : Type) where
  constructor MkPair
  fst : A
  snd : B

test : DPair Nat (\\n => Pair Nat Nat) -> Nat := by
  intro p
  cases p with
  | MkDPair n (MkPair a b) =>
    exact (add n (add a b))
`;
  const result = compileTTFromText(source);
  const decl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'test');
  expect(decl?.checkSuccess).toBe(true);
});
```

- [ ] **Step 2: Run test — likely fails because the session doesn't desugar**

Run: `npx vitest run src/tactics/tactic-session.test.ts -t "nested case patterns compile"`
Expected: FAIL (likely because either the desugaring isn't in the session path, or the session uses a different pattern representation).

- [ ] **Step 3: Apply desugaring in session**

The session calls `applyCaseBranches` with `CaseBranch[]` from the parsed command. It needs to desugar nested patterns the same way `tactic-to-tree.ts` does. Extract the `desugarNestedCaseBranch` function to a shared location.

Create `src/compiler/case-pattern-desugar.ts`:

```typescript
import { CaseBranch, CasePattern, TacticCommand, mkConstTT } from './surface';

let nestedFreshCounter = 0;
function freshNestedName(): string {
  return `_nested${nestedFreshCounter++}`;
}

/**
 * Desugar nested case patterns into sequential `cases` tactic calls.
 * See tactic-to-tree.ts for example.
 */
export function desugarNestedCaseBranch(branch: CaseBranch): CaseBranch {
  const flatParams: CasePattern[] = [];
  const nestedSubs: Array<{ freshName: string; pattern: CasePattern & { tag: 'ctor' } }> = [];

  for (const param of branch.params) {
    if (param.tag === 'var') {
      flatParams.push(param);
    } else {
      const freshName = freshNestedName();
      flatParams.push({ tag: 'var', name: freshName });
      nestedSubs.push({ freshName, pattern: param });
    }
  }

  if (nestedSubs.length === 0) return branch;

  let innerTactics = branch.tactics;
  for (let i = nestedSubs.length - 1; i >= 0; i--) {
    const { freshName, pattern } = nestedSubs[i];
    const innerBranch = desugarNestedCaseBranch({
      constructor: pattern.constructor,
      params: pattern.params,
      tactics: innerTactics,
    });
    const innerCases: TacticCommand = {
      name: 'cases',
      args: [mkConstTT(freshName)],
      caseBranches: [innerBranch],
    };
    innerTactics = [innerCases];
  }

  return {
    constructor: branch.constructor,
    params: flatParams,
    tactics: innerTactics,
  };
}
```

Update `src/proof-tree/tactic-to-tree.ts` to import from the shared location:

```typescript
import { desugarNestedCaseBranch } from '../compiler/case-pattern-desugar';
```

And remove the local copy.

Update `src/tactics/tactic-session.ts` — find where `applyCaseBranches` processes branches and desugar each one first:

```typescript
import { desugarNestedCaseBranch } from '../compiler/case-pattern-desugar';

// In applyCaseBranches, change:
//   for (const branch of branches) {
// to:
//   for (const rawBranch of branches) {
//     const branch = desugarNestedCaseBranch(rawBranch);
```

Also handle the inner tactics correctly — if desugared, the branch's tactics now include a `cases` command that the session will execute.

- [ ] **Step 4: Run test**

Run: `npx vitest run src/tactics/tactic-session.test.ts -t "nested case patterns compile"`
Expected: PASS

- [ ] **Step 5: Run full suite**

Run: `npx tsc --noEmit && npm test 2>&1 | tail -5`
Expected: All tests pass.

- [ ] **Step 6: Commit**

```bash
git add -A
git commit -m "feat: desugar nested case patterns in tactic session (shared helper)"
```

---

### Task 7: End-to-end .tt test

**Files:**
- Create: `src/test-programs/notation/nested-case-patterns.tt`

- [ ] **Step 1: Create the test file**

```
@test success
@name "nested case patterns: DPair of Pair destructured in one step"
@import preambles/nat.tt

add : Nat -> Nat -> Nat
add Zero m = m
add (Succ n) m = Succ (add n m)

record DPair {u v : ULevel} (A : Type u) (B : A -> Type v) : Type (UMax u v) where
  constructor MkDPair
  fst : A
  snd : B fst

record Pair (A B : Type) where
  constructor MkPair
  fst : A
  snd : B

-- Single step destructuring: | MkDPair n (MkPair a b) =>
test : DPair Nat (\n => Pair Nat Nat) -> Nat := by
  intro p
  cases p with
  | MkDPair n (MkPair a b) =>
    exact (add n (add a b))

-- Deeply nested: | A (B (C x)) =>
record Wrap3 (A : Type) where
  constructor MkWrap3
  inner : DPair A (\a => Pair A A)

test2 : Wrap3 Nat -> Nat := by
  intro w
  cases w with
  | MkWrap3 (MkDPair x (MkPair y z)) =>
    exact (add x (add y z))
```

- [ ] **Step 2: Run the test**

Run: `npx vitest run src/test-programs/tt-runner.test.ts -t "nested case patterns"`
Expected: PASS

- [ ] **Step 3: Run full suite**

Run: `npx tsc --noEmit && npm test 2>&1 | tail -5`
Expected: All tests pass.

- [ ] **Step 4: Commit**

```bash
git add src/test-programs/notation/nested-case-patterns.tt
git commit -m "test: end-to-end nested case patterns"
```

---

### Task 8: Update limitAdd to use nested patterns

**Files:**
- Modify: `src/presets/real-analysis.ts`

- [ ] **Step 1: Update limitAdd proof**

Find `limitAdd` in `src/presets/real-analysis.ts`. Currently:

```
limitAdd : ... := by
  intros R f g x0 L M limF limG
  constructor
  intros ε hε
  cases (Limit.eps_delta limF (rdiv ε (rtwo R)) (divTwoPos ε hε)) with
  | MkDPair δF witnessF =>
    cases (Limit.eps_delta limG (rdiv ε (rtwo R)) (divTwoPos ε hε)) with
    | MkDPair δG witnessG =>
      cases (CompleteOrderedField.leTotal (field R) δF δG) with
      | Left hle =>
        exact (MkDPair δF (MkPair (Pair.fst witnessF) (\x hx0 hxd => convertEps ε ... (Pair.snd witnessF x hx0 hxd) ...)))
      ...
```

Update to destructure `witnessF` and `witnessG` as pairs inline. The `EpsDeltaWitness f x0 L ε δ` unfolds to `Pair (rlt (rzero R) δ) ((x : Carrier R) -> ...)` — so the witness is a Pair with `pos : 0 < δ` and `bound : ∀x, ...`.

New version:

```
limitAdd : ... := by
  intros R f g x0 L M limF limG
  constructor
  intros ε hε
  cases (Limit.eps_delta limF (rdiv ε (rtwo R)) (divTwoPos ε hε)) with
  | MkDPair δF (MkPair posF boundF) =>
    cases (Limit.eps_delta limG (rdiv ε (rtwo R)) (divTwoPos ε hε)) with
    | MkDPair δG (MkPair posG boundG) =>
      cases (CompleteOrderedField.leTotal (field R) δF δG) with
      | Left hle =>
        exact (MkDPair δF (MkPair posF (\x hx0 hxd => convertEps ε (rabs (rsub (radd (f x) (g x)) (radd L M))) (coreEstimate f g x0 L M (rdiv ε (rtwo R)) x (boundF x hx0 hxd) (boundG x hx0 (ltLeTrans (rabs (rsub x x0)) δF δG hxd hle))))))
      | Right hle =>
        exact (MkDPair δG (MkPair posG (\x hx0 hxd => convertEps ε (rabs (rsub (radd (f x) (g x)) (radd L M))) (coreEstimate f g x0 L M (rdiv ε (rtwo R)) x (boundF x hx0 (ltLeTrans (rabs (rsub x x0)) δG δF hxd hle)) (boundG x hx0 hxd)))))
```

- [ ] **Step 2: Verify preset compiles**

Run: `npx tsx -e "
import { compileTTFromText } from './src/compiler/compile';
import { PRESETS } from './src/presets/index';
const preset = PRESETS.find(p => p.name.includes('Real'))!;
const result = compileTTFromText(preset.code);
const failures = result.blocks.flatMap(b => b.declarations).filter(d => d.checkSuccess === false && d.name);
console.log('Failures:', failures.length);
for (const f of failures) console.log(' ', f.name, ':', f.checkErrors?.[0]?.message?.substring(0, 120));
"`
Expected: `Failures: 0`

- [ ] **Step 3: Run full suite**

Run: `npx tsc --noEmit && npm test 2>&1 | tail -5`
Expected: All tests pass.

- [ ] **Step 4: Commit**

```bash
git add src/presets/real-analysis.ts
git commit -m "refactor: limitAdd uses nested case patterns | MkDPair δ (MkPair pos bound) =>"
```

---

### Task 9: Update prose view to handle nested patterns

Since desugaring happens at the proof-tree level, the tree already shows `cases` → `Case A →  cases → Case B`. But the user wrote a FLAT nested pattern. We should render it that way in the prose.

**Files:**
- Modify: `src/proof-tree/proof-prose.ts`, `src/components/ProofTreeEditor.tsx`

- [ ] **Step 1: Investigate current rendering**

After desugaring, `limitAdd` produces:
```
cases ... with
| MkDPair δF _nested1 =>
  cases _nested1 with
  | MkPair posF boundF => ...
```

The prose view will show:
```
By cases on ...
  Case (MkDPair(δF, _nested1)):
    By cases on _nested1
      Case (MkPair(posF, boundF)):
        ...
```

This is technically correct but ugly. The user wants:
```
By cases on ...
  Case (MkDPair(δF, MkPair(posF, boundF))):
    ...
```

- [ ] **Step 2: Decision — defer prose improvement**

Rather than implementing collapsed rendering in this plan, create a follow-up task by adding a comment. The desugared form is functionally correct; the prose cleanup is a separate concern.

In `src/proof-tree/proof-prose.ts`, add a comment near the `caseHeader` emission:

```typescript
// TODO: when a case has a single nested `cases` on a _nested* var,
// collapse them into a flat nested pattern for display.
// E.g., "MkDPair(δ, _nested1)" followed by "cases _nested1 | MkPair(a, b)"
// should render as "MkDPair(δ, MkPair(a, b))".
```

- [ ] **Step 3: Commit**

```bash
git add src/proof-tree/proof-prose.ts
git commit -m "docs: note future prose-collapse for nested case patterns"
```

---

### Task 10: Final verification

- [ ] **Step 1: Run full build and test suite**

```bash
npx tsc --noEmit && npm test
```

Expected: all tests pass, no TypeScript errors.

- [ ] **Step 2: Verify the real-analysis preset compiles cleanly**

```bash
npx tsx -e "
import { compileTTFromText } from './src/compiler/compile';
import { PRESETS } from './src/presets/index';
const preset = PRESETS.find(p => p.name.includes('Real'))!;
const result = compileTTFromText(preset.code);
const failures = result.blocks.flatMap(b => b.declarations).filter(d => d.checkSuccess === false && d.name);
console.log('Real-analysis preset failures:', failures.length);
"
```

Expected: `Real-analysis preset failures: 0`

- [ ] **Step 3: Push all commits**

```bash
git push
```
