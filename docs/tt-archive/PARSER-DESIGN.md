# TT Parser Design

## Philosophy

**Pure ASTs + Separate Source Maps**: AST nodes contain no position data. Position tracking uses a three-map architecture that preserves AST purity while enabling precise error reporting.

**Block-Based Parsing**: Source code is grouped by indentation into independent blocks. Each block is parsed separately, enabling:
- Incremental error isolation (one bad block doesn't kill others)
- Live feedback as user types
- Natural mental model (one definition = one block)

**Pratt Parsing**: Operator precedence handled via Pratt parser (precedence climbing). Enables user-defined infix operators with custom precedence/associativity.

**De Bruijn Indices**: Variables converted to De Bruijn indices during parsing using name context (list of bound variable names). Constants remain named.

## Architecture

### Three-Map Position Tracking

```
Source Code
    ↓ Parser
TTerm + SourceMap          IndexPath → SourceRange
    ↓ Elaborator
TTKTerm + ElabMap          KernelPath → SurfacePath
    ↓ TypeChecker
TypeCheckError             Contains KernelPath
    ↓ Error Resolution
SourceRange                KernelPath → SurfacePath → SourceRange
```

**IndexPath**: Hybrid semantic+positional path through AST
- Field segments: `{kind: 'field', name: 'type'}`
- Array segments: `{kind: 'array', index: 0}`
- Serialized: `"constructors[0].type"`

**Why Three Maps?**
- Parser builds SourceMap (surface AST → source text)
- Elaborator builds ElabMap (kernel AST → surface AST)
- Error resolution chains maps: kernel → surface → source

### Block Processing Pipeline

```
groupByIndentation()  →  SourceBlock[]
    ↓
parseDeclarationsWithSource()  →  (ParsedDeclaration, SourceMap)[]
    ↓
validateDeclarations()  →  Name resolution errors
    ↓
elabToKernelWithMap()  →  (TTKTerm, ElabMap)[]
    ↓
checkDeclarations()  →  Type check errors
    ↓
resolveErrorLocation()  →  Error with SourceRange
```

**Block Line Adjustment**: Each block parsed with line 1 as start. SourceMaps adjusted by `lineOffset = block.startLine - 1` to get file-relative positions.

## Parsing Strategy

### Expression Parsing (Pratt)

**Core Loop**:
```typescript
expr(minPrec, ctx, path):
  left = parsePrefix(ctx, path)
  while current.precedence >= minPrec:
    left = parseInfix(left, ctx, path)
  return left
```

**Precedence Table**:
- Arrow (`->`): 10 (right-assoc)
- User operators: configurable (default 20, left-assoc)
- Application: 100 (left-assoc, implicit)

**Path Propagation**: Every recursive `expr()` call receives `path: IndexPath` parameter. Used to record source positions via `recordRange(path, startToken, endToken)`.

### Declaration Parsing

**Strategy**: Greedy merge of type signatures and definitions
```
name : Type       →  { name, type }
name = value      →  { name, value }
name : Type       →  { name, type, value }
name = value
```

**Inductive Declarations**:
```
inductive Name : Type where
  Ctor1 : T1
  Ctor2 : T2
```

- Type parsed with `exprUntil(0, [], ['WHERE'])` to stop at `where`
- Constructors parsed in loop, each with path `constructors[i].type`
- Constructors added to global symbol table (for name resolution)

### Pattern Matching

**Detection**: Declaration is pattern clause if:
1. Previous declaration exists with same name
2. Current declaration has no type signature
3. Value is lambda with pattern on LHS

**Not Yet Implemented**: Pattern elaboration, totality checking

## Name Resolution

**Phase**: After parsing, before elaboration

**Symbol Context**: `Set<string>` of defined symbols, built incrementally across blocks

**Validation**:
1. Collect all names declared in current block
2. For each term, check all `Const` nodes against context
3. Allow self-references (for recursion)
4. Allow forward references within same block
5. Collect ALL errors (don't stop at first)

**Error Structure**:
```typescript
interface NameResolutionError {
  message: string;
  symbolName: string;
  path: string[];  // IndexPath where error occurred
}
```

## Source Position Recording

### Recording Strategy

**When**: Called after parsing each AST node
**What**: `recordRange(path, startToken, endToken)`
**Where**: Stored in `currentSourceMap: Map<string, SourceRange>`

### Coverage

**Currently Tracked**:
- ✅ Identifiers (constants): `parseIdent()` records single-token range
- ✅ Constructor types: Path `constructors[i].type` passed to `expr()`
- ⚠️ Other nodes: Partially implemented

**Not Yet Tracked**:
- ❌ Lambda domain/body
- ❌ Pi domain/body
- ❌ App function/arg
- ❌ Let binding/value/body
- ❌ Full expression ranges

**Why Partial?**: Identifier positions (most common error location) prioritized. Full coverage planned but not critical for MVP.

## Error Handling

### Parse Errors

**Multi-Error Collection**: Parser throws `ParseErrors` containing array of individual errors. Each error has `(line, col, message)`.

**Recovery Strategy**: Block-level isolation. Parse error in one block doesn't affect others.

### Name Resolution Errors

**Collection**: All undefined symbols collected (don't stop at first)
**Location**: Resolved via SourceMap using error's IndexPath
**Display**: Monaco markers with precise squiggly underlines

### Type Check Errors

**Collection**: Parallel checking (all constructors/clauses checked independently)
**Location**: Resolved via ElabMap → SourceMap chain
**Display**: Monaco markers with file/line/col

## Current State

### Fully Implemented ✅

- Pratt parser with operator precedence
- De Bruijn index conversion
- Block-based parsing with indentation grouping
- Inductive declarations with constructors
- Source position tracking for identifiers
- Name resolution with multi-error collection
- Block line number adjustment
- Error resolution to source positions
- Monaco editor integration

### Partially Implemented ⚠️

- Source position tracking (only identifiers/constructors)
- Pattern matching (detection only, not elaboration)
- Declaration merging (type + value on separate lines)

### Not Implemented ❌

- Full source position coverage (all AST nodes)
- Pattern elaboration and checking
- Totality/termination checking
- Record types
- Mutual recursion analysis
- Positivity checking for inductives

## TODOs

### High Priority

1. **Complete Source Position Tracking**
   - Add paths to `parseLambda`, `parseBinder`, `parseApp`, `parseLet`
   - Record ranges for all AST nodes, not just identifiers
   - Test: Verify errors on all node types have correct locations

2. **Fix Pattern Matching Detection**
   - Current: Only detects if previous decl with same name exists
   - Need: Check if value is actually a pattern (not just any lambda)
   - Issue: False positives when defining multiple functions with same name

3. **Improve Error Messages**
   - Add "Did you mean?" suggestions for typos
   - Show context (surrounding code) in error messages
   - Highlight expected vs actual in type errors

### Medium Priority

4. **Operator Improvements**
   - Support prefix operators (-, not, etc.)
   - Support postfix operators (!, ?, etc.)
   - Allow Unicode operators (∀, ∃, ∧, ∨, etc.)

5. **Declaration Syntax**
   - Support `mutual` blocks for mutual recursion
   - Support `namespace` for grouping
   - Support `section` for common parameters

6. **Error Recovery**
   - Within-block error recovery (continue parsing after error)
   - Better handling of incomplete input (for live editing)

### Low Priority

7. **Performance**
   - Cache parse results per block (only reparse changed blocks)
   - Incremental lexing (reuse tokens from unchanged text)
   - Streaming parser (parse as user types, not on blur)

8. **Syntax Sugar**
   - Implicit arguments `{x : T}` vs explicit `(x : T)`
   - Do-notation for monads
   - List/tuple literals `[1, 2, 3]`, `(a, b, c)`

9. **Documentation**
   - Add doc comments `-- | This function...`
   - Parse and attach to declarations
   - Display in hover tooltips

## Design Decisions

### Why De Bruijn Indices?

**Pros**:
- Avoid capture during substitution
- Alpha-equivalence is structural equality
- Simpler type checker implementation

**Cons**:
- Less readable in debug output
- Requires name context during parsing
- Can't easily reconstruct original names

**Decision**: Use De Bruijn in AST, keep name hints for display.

### Why Block-Based Parsing?

**Pros**:
- Natural for interactive editing
- Errors isolated per block
- Easier incremental parsing
- Matches user mental model

**Cons**:
- Can't detect mutual recursion across blocks
- Harder to handle block-spanning constructs
- Line number adjustment required

**Decision**: Block-based for MVP, may add whole-file mode later.

### Why Pure ASTs?

**Pros**:
- Simpler AST types (no position clutter)
- Can hash/compare ASTs structurally
- Can transform ASTs without position bookkeeping
- Single source of truth for positions (maps)

**Cons**:
- More complex error resolution
- Three maps to maintain (Source, Elab, Error)
- Can't easily get position from AST node

**Decision**: Pure ASTs with separate maps. Complexity justified by cleaner architecture.

### Why IndexPath Instead of AST Pointers?

**Pros**:
- Serializable (can store in DB, send over network)
- Stable across transformations (elaboration, normalization)
- Works with pure ASTs (no mutation/pointers)
- Debuggable (human-readable paths)

**Cons**:
- Requires path propagation through all parsing
- Can become invalid if AST structure changes
- Slower lookup than direct pointers

**Decision**: IndexPath for robustness and serializability.

## References

**Related Files**:
- [tt-parser.ts](src/parser/tt-parser.ts) - Main parser implementation
- [tt-core.ts](src/types/tt-core.ts) - AST definition (TTerm)
- [source-position.ts](src/types/source-position.ts) - Position tracking types
- [name-resolution.ts](src/types/name-resolution.ts) - Symbol validation
- [block-checker.ts](src/parser/block-checker.ts) - Block processing pipeline

**Related Docs**:
- [TT-LAYER-DESIGN.md](TT-LAYER-DESIGN.md) - Overall type theory layer design
