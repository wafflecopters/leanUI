# Notation System Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add `infixl`, `infixr`, `infix`, `prefix`, and `notation` declarations that let users define custom operators and syntax in the source language, starting with DPair sigma syntax `(x : A ** P x)`.

**Architecture:** Notation declarations are parsed as a new declaration kind, registered in the parser's operator table during the declaration-parsing pass, and expanded during expression parsing. The parser already has a Pratt parser with an `OperatorInfo` registry — we extend it to accept user-defined entries. For binding notations like DPair's `**`, we add a new `OperatorInfo.binding` flag that tells the Pratt parser to wrap the RHS in a lambda.

**Tech Stack:** TypeScript, Vitest

---

## File Map

| File | Change | Purpose |
|------|--------|---------|
| `src/parser/parser.ts` | Modify | Add `notation`/`infixl`/`infixr`/`prefix` declaration parsing; extend `OperatorInfo` with binding support; add `registerOperator` method |
| `src/parser/parser.test.ts` | Modify | Tests for notation parsing and operator expansion |
| `src/compiler/surface.ts` | Modify | Add `'notation'` to `ParsedDeclaration.kind` if needed (or handle as `'def'` with metadata) |
| `src/compiler/compile.ts` | Modify | Skip notation declarations during type-checking (they're directives, not terms) |
| `language-spec.md` | Modify | Document notation syntax |
| `src/test-programs/notation/` | Create | `.tt` test files for end-to-end notation tests |

---

### Task 1: Extend OperatorInfo and add registerOperator to Parser

The parser already has `OperatorInfo` and `DEFAULT_OPERATORS`. We need to:
1. Add optional `binding` field to `OperatorInfo` (for sigma/DPair-style binders)
2. Add a `registerOperator` method to `Parser`
3. Make the `operators` field mutable (currently set in constructor)

**Files:**
- Modify: `src/parser/parser.ts:104-150` (OperatorInfo, Parser class)
- Test: `src/parser/parser.test.ts`

- [ ] **Step 1: Write failing test**

In `src/parser/parser.test.ts`, add a new describe block:

```typescript
describe('custom operators via registerOperator', () => {
  test('registered infix operator parses as function application', () => {
    const parser = new Parser();
    parser.registerOperator({
      symbol: '**',
      precedence: 40,
      associativity: 'right',
      constName: 'MkDPair',
    });
    const result = parser.parseExpression('a ** b');
    // Should parse as App(App(Const('MkDPair'), a), b)
    expect(result.tag).toBe('App');
    expect((result as any).fn.fn.name).toBe('MkDPair');
  });
});
```

- [ ] **Step 2: Run test to verify it fails**

Run: `npx vitest run src/parser/parser.test.ts -t "registered infix operator"`
Expected: FAIL — `registerOperator` not defined

- [ ] **Step 3: Implement registerOperator**

In `src/parser/parser.ts`, modify the `Parser` class:

```typescript
export interface OperatorInfo {
  symbol: string;
  precedence: number;
  associativity: Associativity;
  constName?: string;
  /** If true, RHS is parsed as a binding form: x ** P becomes MkDPair x (\x => P) */
  binding?: boolean;
}

export class Parser {
  private tokens: Token[] = [];
  private pos = 0;
  private currentSourceMap: SourceMap = new Map();
  private currentPath: IndexPath = [];
  private parenDepth = 0;
  private operators: Record<string, OperatorInfo>;  // was private, now mutable

  constructor(
    operators: Record<string, OperatorInfo> = DEFAULT_OPERATORS
  ) {
    this.operators = { ...operators };  // copy so we can mutate
  }

  /** Register a user-defined operator. */
  registerOperator(op: OperatorInfo): void {
    this.operators[op.symbol] = op;
  }
```

- [ ] **Step 4: Run test to verify it passes**

Run: `npx vitest run src/parser/parser.test.ts -t "registered infix operator"`
Expected: PASS

- [ ] **Step 5: Run full suite**

Run: `npx tsc --noEmit && npm test`

- [ ] **Step 6: Commit**

```bash
git add src/parser/parser.ts src/parser/parser.test.ts
git commit -m "feat: add registerOperator to Parser, binding flag on OperatorInfo"
```

---

### Task 2: Parse `infixl`/`infixr`/`infix`/`prefix` declarations

Add parsing of notation declarations like:
```
infixl 65 + := radd
infixr 40 ** := DPair
prefix 90 - := rneg
```

These are parsed as directives that register operators, not as term declarations.

**Files:**
- Modify: `src/parser/parser.ts` (parseDeclaration, new parseNotationDeclaration)
- Test: `src/parser/parser.test.ts`

- [ ] **Step 1: Write failing test**

```typescript
describe('notation declarations', () => {
  test('infixl declaration is parsed', () => {
    const parser = new Parser();
    const decls = parser.parseDeclarations('infixl 65 + := radd');
    expect(decls.length).toBe(1);
    expect(decls[0].kind).toBe('notation');
    expect((decls[0] as any).notationKind).toBe('infixl');
    expect((decls[0] as any).precedence).toBe(65);
    expect((decls[0] as any).symbol).toBe('+');
    expect((decls[0] as any).target).toBe('radd');
  });

  test('infixr declaration is parsed', () => {
    const parser = new Parser();
    const decls = parser.parseDeclarations('infixr 40 ** := DPair');
    expect(decls.length).toBe(1);
    expect(decls[0].kind).toBe('notation');
    expect((decls[0] as any).notationKind).toBe('infixr');
  });

  test('prefix declaration is parsed', () => {
    const parser = new Parser();
    const decls = parser.parseDeclarations('prefix 90 - := rneg');
    expect(decls.length).toBe(1);
    expect(decls[0].kind).toBe('notation');
    expect((decls[0] as any).notationKind).toBe('prefix');
  });
});
```

- [ ] **Step 2: Run test to verify it fails**

Run: `npx vitest run src/parser/parser.test.ts -t "notation declarations"`
Expected: FAIL

- [ ] **Step 3: Add `'notation'` kind to ParsedDeclaration**

In `src/parser/parser.ts`, update the `ParsedDeclaration` interface (or add the notation fields):

```typescript
export interface ParsedDeclaration {
  kind: 'def' | 'expr' | 'inductive' | 'record' | 'notation';
  // ... existing fields ...

  // Notation-specific fields (only when kind === 'notation')
  notationKind?: 'infixl' | 'infixr' | 'infix' | 'prefix';
  precedence?: number;
  symbol?: string;    // The operator symbol (e.g., '+', '**', '-')
  target?: string;    // The function to desugar to (e.g., 'radd', 'DPair')
}
```

- [ ] **Step 4: Add keyword detection in lexer**

In the lexer, add `infixl`, `infixr`, `infix`, `prefix` as recognized keywords. The simplest approach: in `parseDeclaration`, check if the current IDENT token is one of these words and dispatch to `parseNotationDeclaration`.

```typescript
// In parseDeclaration():
if (current.type === 'IDENT' && ['infixl', 'infixr', 'infix', 'prefix'].includes(current.value)) {
  return this.parseNotationDeclaration();
}
```

- [ ] **Step 5: Implement parseNotationDeclaration**

```typescript
private parseNotationDeclaration(): ParsedDeclaration {
  const notationKind = this.current().value as 'infixl' | 'infixr' | 'infix' | 'prefix';
  this.advance(); // consume infixl/infixr/infix/prefix

  // Parse precedence (number)
  if (this.current().type !== 'NUMBER') {
    throw new Error(`Expected precedence number after '${notationKind}'`);
  }
  const precedence = parseInt(this.current().value, 10);
  this.advance();

  // Parse operator symbol (either OPERATOR token or IDENT for multi-char ops like **)
  const symbolToken = this.current();
  if (symbolToken.type !== 'OPERATOR' && symbolToken.type !== 'IDENT') {
    throw new Error(`Expected operator symbol after precedence`);
  }
  const symbol = symbolToken.value;
  this.advance();

  // Expect :=
  if (this.current().type !== 'ASSIGN' && !(this.current().type === 'OPERATOR' && this.current().value === ':=')) {
    throw new Error(`Expected ':=' after operator symbol`);
  }
  this.advance();

  // Parse target name
  if (this.current().type !== 'IDENT') {
    throw new Error(`Expected function name after ':='`);
  }
  const target = this.current().value;
  this.advance();

  // Register the operator immediately so subsequent expressions can use it
  const assoc: Associativity = notationKind === 'infixl' ? 'left'
    : notationKind === 'infixr' ? 'right'
    : notationKind === 'prefix' ? 'right'  // prefix uses right for nud
    : 'none';

  this.registerOperator({
    symbol,
    precedence,
    associativity: assoc,
    constName: target,
  });

  return {
    kind: 'notation',
    notationKind,
    precedence,
    symbol,
    target,
  };
}
```

- [ ] **Step 6: Run tests**

Run: `npx vitest run src/parser/parser.test.ts -t "notation declarations"`
Expected: PASS

- [ ] **Step 7: Run full suite**

Run: `npx tsc --noEmit && npm test`

- [ ] **Step 8: Commit**

```bash
git add src/parser/parser.ts src/parser/parser.test.ts
git commit -m "feat: parse infixl/infixr/infix/prefix notation declarations"
```

---

### Task 3: Notation declarations affect subsequent parsing

A notation declaration should register the operator so that expressions AFTER it in the same file use the operator.

**Files:**
- Test: `src/parser/parser.test.ts`
- Modify: `src/parser/parser.ts` (may already work from Task 2)

- [ ] **Step 1: Write test**

```typescript
test('infixl operator is usable in subsequent declarations', () => {
  const parser = new Parser();
  const decls = parser.parseDeclarations(`
infixl 65 + := radd

test : Nat
test = a + b
`);
  // Should have 2 declarations: notation + def
  const defs = decls.filter(d => d.kind !== 'notation');
  expect(defs.length).toBe(1);
  // The value of test should be App(App(Const('radd'), Const('a')), Const('b'))
  const val = defs[0].value!;
  expect(val.tag).toBe('App');
  expect((val as any).fn.fn.name).toBe('radd');
});

test('multiple notations compose correctly', () => {
  const parser = new Parser();
  const decls = parser.parseDeclarations(`
infixl 65 + := radd
infixl 70 * := rmul

test : Nat
test = a + b * c
`);
  const defs = decls.filter(d => d.kind !== 'notation');
  const val = defs[0].value!;
  // Should be radd(a, rmul(b, c)) because * binds tighter than +
  expect(val.tag).toBe('App');
  const fn = (val as any).fn;
  expect(fn.fn.name).toBe('radd');     // outer is +
  expect((val as any).arg.fn.fn.name).toBe('rmul');  // inner is *
});
```

- [ ] **Step 2: Run tests and verify**

These should pass if Task 2's `registerOperator` call in `parseNotationDeclaration` works correctly (it registers before subsequent declarations are parsed).

- [ ] **Step 3: Commit**

```bash
git add src/parser/parser.test.ts
git commit -m "test: notation operators work in subsequent declarations"
```

---

### Task 4: Handle binding notation for DPair (`**`)

The DPair sigma syntax `(x : A ** P x)` requires the RHS of `**` to be wrapped in a lambda binding `x`. This is the `binding` flag on `OperatorInfo`.

**Files:**
- Modify: `src/parser/parser.ts` (Pratt parser infix handling)
- Test: `src/parser/parser.test.ts`

- [ ] **Step 1: Write failing test**

```typescript
describe('binding notation (DPair **)', () => {
  test('** with binding wraps RHS in lambda', () => {
    const parser = new Parser();
    parser.registerOperator({
      symbol: '**',
      precedence: 40,
      associativity: 'right',
      constName: 'DPair',
      binding: true,
    });
    // Parse: (x : Nat ** Equal x Zero)
    // Inside parens, the binder (x : Nat) is parsed, then ** triggers binding
    const result = parser.parseExpression('(x : Nat ** Equal x Zero)');
    // Should desugar to: DPair Nat (\x => Equal x Zero)
    // i.e., App(App(Const('DPair'), Const('Nat')), Binder(BLamTT, 'x', _, Equal x Zero))
    expect(result.tag).toBe('App');
    const dpairApp = result as any;
    expect(dpairApp.fn.fn.name).toBe('DPair');
    // First arg is Nat
    expect(dpairApp.fn.arg.name).toBe('Nat');
    // Second arg is a lambda
    expect(dpairApp.arg.tag).toBe('Binder');
    expect(dpairApp.arg.binderKind.tag).toBe('BLamTT');
    expect(dpairApp.arg.name).toBe('x');
  });
});
```

- [ ] **Step 2: Run test to verify it fails**

- [ ] **Step 3: Implement binding operator in Pratt parser**

In `src/parser/parser.ts`, in the infix operator handling section of `expr()` (around line 2230-2253), add handling for `binding` operators:

```typescript
if (token.type === 'OPERATOR') {
  const opInfo = this.operators[token.value];
  if (!opInfo || opInfo.precedence < minPrec) break;

  this.advance();

  if (opInfo.binding) {
    // Binding operator (like ** for DPair):
    // LHS was parsed as a typed binder `(x : A)`
    // Extract the binder name and type from the LHS
    // RHS is wrapped in a lambda: \x => RHS
    const binderName = this.extractBinderName(left);
    const bodyCtx = [binderName, ...ctx];
    const right = this.expr(opInfo.precedence, bodyCtx, path);
    const lambda: TTerm = {
      tag: 'Binder',
      name: binderName,
      binderKind: { tag: 'BLamTT' },
      body: right,
    };
    const opConst = mkConstTT(opInfo.constName || token.value);
    left = mkAppTT(mkAppTT(opConst, left), lambda);
    continue;
  }

  // ... existing non-binding operator handling ...
}
```

The `extractBinderName` helper extracts the variable name from a typed annotation `(x : A)`:
```typescript
private extractBinderName(term: TTerm): string {
  // For Annot (x : A), the term is Const('x'), type is A
  if (term.tag === 'Annot' && term.term.tag === 'Const') return term.term.name;
  if (term.tag === 'Const') return term.name;
  return '_';
}
```

**Important detail:** When `**` is inside parens like `(x : A ** P)`, the parser first parses `x : A` as an annotation (`Annot(Const('x'), Const('A'))`). Then `**` triggers. The LHS is the type `A` (from the annotation), and we extract the binder name `x`. The lambda binds `x` over the RHS `P`. The final term is `DPair(A, \x => P)`.

This requires careful handling — the annotation parsing and the binding operator need to cooperate. The exact implementation will depend on how the parser handles `(x : A ** P)` — it may need special-case logic for annotated binders followed by binding operators.

- [ ] **Step 4: Run test to verify it passes**

- [ ] **Step 5: Run full suite**

Run: `npx tsc --noEmit && npm test`

- [ ] **Step 6: Commit**

```bash
git add src/parser/parser.ts src/parser/parser.test.ts
git commit -m "feat: binding notation for DPair-style sigma syntax"
```

---

### Task 5: Skip notation declarations in compilation

Notation declarations are parser directives — they should NOT be type-checked or elaborated.

**Files:**
- Modify: `src/compiler/compile.ts`

- [ ] **Step 1: Skip notation declarations in the compilation loop**

In `src/compiler/compile.ts`, in the main compilation loop that processes `ParsedDeclaration[]`, add a check:

```typescript
// Skip notation declarations — they're parser directives, not terms
if (decl.kind === 'notation') continue;
```

Add this early in the loop, before any elaboration or type-checking.

- [ ] **Step 2: Run full suite**

Run: `npx tsc --noEmit && npm test`

- [ ] **Step 3: Commit**

```bash
git add src/compiler/compile.ts
git commit -m "fix: skip notation declarations in compilation (parser directives)"
```

---

### Task 6: End-to-end test with DPair

Write a `.tt` file test that uses the notation system with DPair.

**Files:**
- Create: `src/test-programs/notation/dpair-sigma.tt`
- Create: `src/test-programs/notation/infix-basic.tt`

- [ ] **Step 1: Create basic infix test**

Create `src/test-programs/notation/infix-basic.tt`:
```
@test success
@name "infix notation: custom + operator"

inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

add : Nat -> Nat -> Nat
add Zero m = m
add (Succ n) m = Succ (add n m)

infixl 65 + := add

test : Equal (add (Succ Zero) (Succ Zero)) (Succ (Succ Zero))
test = refl

-- Same thing using infix notation
test2 : Equal (Succ Zero + Succ Zero) (Succ (Succ Zero))
test2 = refl
```

- [ ] **Step 2: Create DPair sigma test**

Create `src/test-programs/notation/dpair-sigma.tt`:
```
@test success
@name "binding notation: DPair sigma syntax with **"

inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive DPair (A : Type) (P : A -> Type) : Type where
  MkDPair : (fst : A) -> P fst -> DPair A P

infixr 40 ** := DPair

-- (n : Nat ** Equal n Zero) should desugar to DPair Nat (\n => Equal n Zero)
myType : Type
myType = (n : Nat ** Equal n Zero)

-- Can construct a value
myVal : (n : Nat ** Equal n Zero)
myVal = MkDPair Zero refl
```

- [ ] **Step 3: Run the tests**

Run: `npx vitest run src/test-programs/tt-runner.test.ts -t "infix notation"`
Run: `npx vitest run src/test-programs/tt-runner.test.ts -t "binding notation"`

- [ ] **Step 4: Run full suite**

Run: `npx tsc --noEmit && npm test`

- [ ] **Step 5: Commit**

```bash
git add src/test-programs/notation/
git commit -m "test: end-to-end notation tests for infix and DPair sigma"
```

---

### Task 7: Update language-spec.md

Document the new notation syntax.

**Files:**
- Modify: `language-spec.md`

- [ ] **Step 1: Add notation section**

Add to `language-spec.md`:

```markdown
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

Right-associative operators can be used with typed binders for sigma/DPair syntax:

```
infixr 40 ** := DPair

-- (x : A ** P x)  desugars to  DPair A (\x => P x)
myType : Type
myType = (n : Nat ** Equal n Zero)
```

When `**` follows a typed binder `(x : A)`, the RHS is wrapped in a lambda binding `x`.

### Precedence

Higher numbers bind tighter. Standard precedences:
- `->` (Pi type): 25
- `||`, `∨`: 30
- `&&`, `∧`: 35
- `**` (DPair): 40
- `=`, `<`, `>`, `≤`, `≥`: 50
- `+`, `-`: 65
- `*`, `/`: 70
- `^`: 80
- `-` (prefix): 90
- function application: 100
```

- [ ] **Step 2: Commit**

```bash
git add language-spec.md
git commit -m "docs: document notation declaration syntax"
```

---

### Task 8: Propagate notations across compilation blocks

The `compileTTFromText` function creates a new `Parser()` per block. Notations defined in earlier blocks must be available in later blocks.

**Files:**
- Modify: `src/compiler/compile.ts:1457` (parser creation)

- [ ] **Step 1: Collect notations across blocks**

In `compileTTFromText`, maintain a running operator registry that accumulates notations from all blocks:

```typescript
// Before the block loop:
const customOperators: Record<string, OperatorInfo> = { ...DEFAULT_OPERATORS };

// Inside the block loop, when creating the parser:
const parser = new Parser(customOperators);

// After parsing, collect any notation declarations:
for (const decl of declarations) {
  if (decl.kind === 'notation' && decl.symbol && decl.target) {
    const assoc: Associativity = decl.notationKind === 'infixl' ? 'left'
      : decl.notationKind === 'infixr' ? 'right' : 'none';
    customOperators[decl.symbol] = {
      symbol: decl.symbol,
      precedence: decl.precedence ?? 50,
      associativity: assoc,
      constName: decl.target,
      binding: decl.binding,
    };
  }
}
```

- [ ] **Step 2: Write test with cross-block notation**

Create `src/test-programs/notation/cross-block.tt`:
```
@test success
@name "notation works across declaration blocks"

inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

add : Nat -> Nat -> Nat
add Zero m = m
add (Succ n) m = Succ (add n m)

infixl 65 + := add

-- This is in a new block (after blank line separation)
test : Equal (Succ Zero + Zero) (Succ Zero)
test = refl
```

- [ ] **Step 3: Run full suite**

Run: `npx tsc --noEmit && npm test`

- [ ] **Step 4: Commit**

```bash
git add src/compiler/compile.ts src/test-programs/notation/
git commit -m "feat: propagate notation operators across compilation blocks"
```

---

### Task 9: Wire DPair notation in real-analysis preset

Add the `**` notation for DPair in the real-analysis preset so existing DPair usage can optionally use the new syntax.

**Files:**
- Modify: `src/presets/real-analysis.ts`

- [ ] **Step 1: Add notation declaration**

Add near the top of the real-analysis preset (after the DPair definition):

```
infixr 40 ** := DPair
```

- [ ] **Step 2: Verify the preset still compiles**

Run: `npx vitest run src/test-programs/tt-runner.test.ts -t "real-analysis"`
Or: `npm test`

- [ ] **Step 3: Commit**

```bash
git add src/presets/real-analysis.ts
git commit -m "feat: add ** notation for DPair in real-analysis preset"
```
