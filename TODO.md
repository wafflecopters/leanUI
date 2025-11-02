# TODO

## ✅ Recently Completed

### Type Hole System
- [x] Add `typeHoleId` to `Assumption` interface
- [x] Create type holes when parsing goals with unbound variables
- [x] Update TT term construction to use type holes instead of assuming `Prop`
- [x] Add `typeContext` parameter to `expressionNodeToTTerm`
- [x] Pass type context through all recursive calls
- [x] Update call sites to build and pass type context
- [x] Write comprehensive tests for type hole system
- [x] Document type hole design in TYPE-HOLES-DESIGN.md

### Code Cleanup
- [x] Delete fix documentation (.md files documenting individual fixes)
- [x] Keep only architecture/design documentation
- [x] Create ARCHITECTURE-OVERVIEW.md for high-level system understanding

### Bug Fixes
- [x] Add `mkConst` helper function to tt-core.ts
- [x] Add `mkSort` helper (already existed as `mkType`)
- [x] Remove global hole selection UI
- [x] Add 'hole' type to ExpressionNode
- [x] Support 'hole' type in expressionNodeToTTerm conversion
- [x] Support 'hole' type in FocusedExpressionRenderer

## 🚧 In Progress

### Hole Instantiation Engine
**Status**: Design complete, implementation pending

When a user instantiates a type hole (e.g., `?type_a := ℝ`), the system should:
1. Find all occurrences of the hole throughout the term
2. Replace each occurrence with the instantiated value
3. Simplify/normalize as needed
4. Update UI to reflect changes

**Files to implement**:
- `tt-typecheck.ts`: Add `instantiateHole(term, holeId, value)` function
- `EnhancedProofWorkspace.tsx`: Add UI for hole instantiation
- `tt-core.ts`: May need normalization/simplification functions

**Tests needed**:
- Instantiate type hole in Pi type
- Propagation to all term occurrences
- Nested hole instantiation

## 📋 Backlog

### High Priority

#### Better Equality Type Inference
Currently `mkEq` hardcodes `TT_CONSTANTS.Real` as the type parameter. Should infer from arguments.

```typescript
// Current:
return mkApp(mkApp(mkApp(eqConst, TT_CONSTANTS.Real), eqLeft), eqRight);

// Should be:
const inferredType = getTypeOf(eqLeft);  // Could be a type hole!
return mkApp(mkApp(mkApp(eqConst, inferredType), eqLeft), eqRight);
```

#### Proof Completion UI
Each let-binding's proof editor should show when the proof is complete (no holes remain).

- Show "✓ Proof complete" indicator
- Disable rule application when complete
- Show remaining holes count

#### Rule Suggestion System
Based on current goal/hole type, suggest applicable rules.

- Pattern match against goal structure
- Filter rules by applicability
- Show in dropdown/sidebar

### Medium Priority

#### Term Simplification
After proof steps, simplify terms (e.g., `1 * x → x`).

- Implement basic rewrite rules
- Apply automatically or on demand
- Show before/after

#### Export to Lean 4
Convert TT terms to Lean 4 syntax for verification.

- Map TT terms to Lean syntax
- Handle De Bruijn → named variables
- Include imports and context

#### Proof Search
Automatically find proof for simple goals.

- Implement basic tactics (reflexivity, symmetry, etc.)
- Try rule combinations
- Show proof trace

### Low Priority

#### Better Error Messages
When type checking fails, show helpful messages.

- Point to specific subterm
- Suggest fixes
- Show expected vs actual types

#### Undo/Redo
Track proof state history.

- Save snapshots after each step
- Navigate backward/forward
- Show history timeline

#### Proof Serialization
Save/load proofs.

- JSON format for proof state
- Include metadata (author, date, etc.)
- Import/export

## 🔬 Research / Exploration

### Tactic System
High-level proof construction (like Lean's `ring`, `linarith`).

- Define tactic language
- Implement basic tactics
- Extensible architecture

### Visual Proof Editor
Graphical proof tree manipulation.

- Node-based interface
- Drag-and-drop rules
- Automatic layout

### Collaborative Proving
Multiple users working on same proof.

- Real-time synchronization
- Conflict resolution
- Change attribution

## 📝 Documentation Needs

- User guide / tutorial
- API documentation for types
- Contributing guide
- Example proofs

## 🐛 Known Issues

1. **Equality type parameter**: Hardcoded to `Real`, should infer
2. **No hole instantiation UI**: Can't actually instantiate type holes yet
3. **Focus path edge cases**: Some expression structures may not navigate correctly
4. **Memory**: Large proof terms could cause performance issues

## 🎯 Next Steps (Immediate)

1. Test the type hole system in the UI (manual testing)
2. Implement `instantiateHole` function
3. Add UI for type hole instantiation
4. Fix equality type inference to use inferred types
5. Add proof completion indicators

---

**Last Updated**: 2025-11-02
