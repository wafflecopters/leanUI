# TODO

## Upcoming

- [ ] Add inference/checking for `let` expressions
- [ ] Change parser to parse out a general `identifier` instead of var/const/pctor/pvar so that we can disambiguate during elaboration
- [ ] Add multi-let syntax (`let x := a, y := b in ...`)
- [ ] Add infix operator syntax (user-defined operators with precedence)
- [ ] Add custom syntax support (maybe?)
- [ ] Think about namespaces
- [ ] Auto-binder creation - e.g. `Type u -> ...` elaborating to `{u : Level} -> Type u -> ...` if `u` not in scope, or `List A -> ...` elaborating to `{A : Type} -> List A -> ...` if `A` not in scope.

## Improve Wildcard/Meta Naming in Pattern Matching

Currently, wildcards for implicit function parameters get generic names like `?0`, `?1` instead of meaningful names like `A` or `n`. This makes pretty-printed output confusing (looks like unresolved metas).

**The Problem:**
```
nth : {A : Type} -> {n : Nat} -> Vec A n -> Fin n -> A
nth (VCons h _) FZero = h
```
Pretty-prints as:
```
(match ?_scrutinee
  | ?0 (Succ _) (VCons ?0 _ h n2) (FZero _) => h
  ...)
```
Where `?0` is actually the `A` parameter, not an unresolved meta.

**Root Cause:**
- `freshWildcardName()` in [elab.ts:1318-1349](src/compiler/elab.ts#L1318-L1349) generates `?N` when no parameter info is available
- `setCurrentTermParamNames()` exists but is **never called** anywhere
- So top-level implicit params like `{A : Type}` get `?0` names instead of `A0`

**Fix Approach:**
1. Before elaborating patterns in `checkMatchClauseFromSurface`, extract param names from the function type
2. Call `setCurrentTermParamNames(paramNames)` before `elabPatternToKernelWithMap`
3. Call `setCurrentTermParamNames(null)` after to reset state

**Implementation Details:**
- Use `extractConstructorParamNames()` as reference - similar logic for function types
- The `ParamInfo` type already has `name` and `typePrefix` fields
- For `{A : Type}`, should yield `ParamInfo { name: 'A', typePrefix: null }`
- Wildcards would then be named `A0` instead of `?0`

**Files to modify:**
- `src/compiler/compile.ts` - call `setCurrentTermParamNames` around pattern elaboration
- Possibly `src/compiler/elab.ts` - add helper to extract param names from function type

## UI/Text Editor

- [ ] Keyboard shortcut in text editor to comment/uncomment code
- [ ] Keyboard shortcut to toggle binder at cursor between `()` vs `{}`
- [ ] Implement type-at in the editor (show type of expression under cursor)

## Big Projects

- [x] **Records** ✅
  - [x] Parser for record definitions
  - [x] Elaboration + checking for record definitions
  - [x] Projection generation
  - [ ] Elaboration + checking for record call sites (construction, projection via dot notation)
  - [ ] `extends` and elab-inlining

- [ ] **Prop deep dive**
  - [ ] Split out Prop to be independent AST-wise instead of being level 0
  - [ ] Implement all the rules around prop inference and case splitting
  - [ ] Implement large elimination restrictions (can't match on Prop-valued inductive to produce Type-valued result, unless singleton)
  - [ ] Review impredicativity rules for Prop

- [ ] **Case-of and Pattern Refinement**
  - [ ] Implement case-of expression syntax
  - [ ] Nested casing support
  - [ ] Re-elaboration of hoisted patterns
  - [ ] Pattern refinement (dependent pattern matching)

- [ ] **Pattern Matching without K**
  - [ ] Implement axiom K prevention (no deletion rule)
  - [ ] Prevent self-unification to avoid weakK

## Exploration

- [ ] Tactics exploration
- [ ] Explore ways to make TCEnv more monadic / more ergonomic
