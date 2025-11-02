# LeanUI Architecture Overview

## System Layers

### 1. UI Layer (`src/components/`)
- **EnhancedProofWorkspace**: Main workspace, manages goals, hypotheses, and proof state
- **LetManager**: Manages let-bindings and local proof editors
- **TTViewer**: Displays TT proof terms
- **FocusedExpressionRenderer**: Interactive expression editor with focus paths

### 2. AST Layer (`src/types/enhanced-focus.ts`, `src/types/focus.ts`)
- **ExpressionNode**: UI-level AST for mathematical expressions
  - Types: `equality`, `inequality`, `binop`, `unop`, `literal`, `variable`, `application`, `hole`
  - Each node has: `id`, `type`, `value?`, `operator?`, `children`, `raw`
- **FocusPath**: Path through expression tree (array of child indices)
- **Assumption**: Hypotheses with optional type holes

### 3. TT Layer (`src/types/tt-core.ts`)
- **TTerm**: Typed terms with De Bruijn indices
  - `Var`: De Bruijn variable
  - `Sort`: Universe level
  - `Binder`: Pi, Lambda, or Let
  - `App`: Function application
  - `Const`: Named constant
  - `Hole`: Metavariable to be filled
  - `Annot`: Type annotation
- **TermDefinition**: Top-level theorem/constant
  - `name`: Identifier
  - `type`: Type signature
  - `value`: Implementation (may contain holes)

### 4. Bridge Layer (`src/types/tt-bridge.ts`)
- **expressionNodeToTTerm**: Converts UI AST to TT terms
  - Now accepts `typeContext` to properly handle type holes
  - Falls back to `Real` if type not found
- **startEqualityProof**: Initializes equality proof state
- **applyEqualityStep**: Builds trans/cong/sym proof structure

### 5. Type Checking Layer (`src/types/tt-typecheck.ts`)
- **extractHoles**: Finds all holes in a term
- **findHole**: Locates a specific hole
- **fillHoleWith**: Replaces a hole with computed term
- **instantiateHole**: (Planned) Propagates hole instantiation

## Key Features

### Type Hole System (NEW)
When a goal like `a + a = 2 * a` is parsed:
1. System identifies unbound variable `a`
2. Creates type hole: `?type_a : Type`
3. Hypothesis: `a : ?type_a`
4. Goal uses type hole: `((a : ?type_a) → ((eq ?type_a) ((+ a) a)) ((* 2) a)))`

**Status**: Implemented
- ✅ Type holes created for unbound variables
- ✅ Type context passed through conversion
- ✅ Holes displayed in TT viewer
- ⏸️ User instantiation UI (future)
- ⏸️ Hole propagation engine (future)

### Proof System
- **Hole-based**: Proofs are terms with holes to fill
- **Local editing**: Each let-binding has its own proof workspace
- **No global hole selector**: Work directly in proof boxes
- **Focus management**: Automatic, tracks which hole is being filled

### Equality Proofs
- Uses `trans`/`sym`/`cong` to build proof terms
- Each rule application extends the trans chain
- Holes created for each step
- Focus moves automatically through proof construction

## Data Flow

### Goal Setting
```
User Input → parseExpressionToAST → ExpressionNode
  ↓
Extract unbound vars → Create hypotheses with type holes
  ↓
expressionNodeToTTerm(goal, typeContext) → TTerm
  ↓
createRootTermDefinition(hypotheses, goalTerm) → TermDefinition
  ↓
Display in TTViewer
```

### Rule Application
```
User selects expression → FocusPath
  ↓
Apply transformation → New ExpressionNode
  ↓
Convert to TT → expressionNodeToTTerm(expr, typeContext)
  ↓
applyEqualityStep → Build trans structure
  ↓
Update rootDefinition → fillHoleWith
  ↓
Display updated term
```

## Critical Design Decisions

### 1. De Bruijn Indices
Variables in TT terms use indices, not names. This avoids capture and simplifies substitution.

### 2. Explicit Type Holes
Instead of assuming types (e.g., `Real`), create explicit holes that can be instantiated later.

### 3. Local Proof Workspaces
Each let-binding has its own editor. No global proof manipulation.

### 4. AST + TT Dual Representation
- AST for user interaction (names, infix notation)
- TT for formal reasoning (De Bruijn, application trees)

### 5. Focus-based Editing
Navigation through expressions via paths, not selection.

## File Organization

```
src/
├── components/          # React UI components
│   ├── EnhancedProofWorkspace.tsx
│   ├── LetManager.tsx
│   ├── TTViewer.tsx
│   └── FocusedExpressionRenderer.tsx
├── types/              # Type definitions and logic
│   ├── enhanced-focus.ts     # UI AST types
│   ├── tt-core.ts            # TT term types & constructors
│   ├── tt-bridge.ts          # AST ↔ TT conversion
│   ├── tt-typecheck.ts       # Type checking & hole manipulation
│   └── tt-type-holes.test.ts # Type hole tests
└── config/
    └── syntax-mapping.ts     # Math notation mappings
```

## Testing Strategy

Tests are colocated with implementation:
- `tt-core.test.ts`: TT term construction
- `tt-typecheck.test.ts`: Type checking and hole manipulation
- `tt-type-holes.test.ts`: Type hole system
- `pattern-rules.test.ts`: Pattern matching rules

## Future Work

1. **Hole Instantiation Engine**: Propagate type/term instantiations
2. **Better Type Inference**: Infer types from usage context
3. **Proof Search**: Suggest rules based on goal structure
4. **Tactic System**: High-level proof construction
5. **Lean Integration**: Export to Lean 4 for verification

## Documentation Files

- **TT-LAYER-DESIGN.md**: Detailed TT system design
- **UNIFIED-TERM-MODEL.md**: Term model specification
- **TYPE-HOLES-DESIGN.md**: Type hole system design
- **TODO.md**: Current tasks and priorities
- **This file**: High-level architecture overview

