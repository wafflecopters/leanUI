# TODO

## Upcoming

- [ ] Add inference/checking for `let` expressions
- [ ] Change parser to parse out a general `identifier` instead of var/const/pctor/pvar so that we can disambiguate during elaboration
- [ ] Add multi-let syntax (`let x := a, y := b in ...`)
- [ ] Add infix operator syntax (user-defined operators with precedence)
- [ ] Add custom syntax support (maybe?)
- [ ] Think about namespaces
- [ ] Auto-binder creation - e.g. `Type u -> ...` elaborating to `{u : Level} -> Type u -> ...` if `u` not in scope, or `List A -> ...` elaborating to `{A : Type} -> List A -> ...` if `A` not in scope.

## UI/Text Editor

- [ ] Keyboard shortcut in text editor to comment/uncomment code
- [ ] Keyboard shortcut to toggle binder at cursor between `()` vs `{}`

## Big Projects

- [ ] **Records**
  - Parser for record definitions
  - Elaboration + checking for record definitions
  - Elaboration + checking for record call sites (construction, projection)
  - `extends` and elab-inlining

- [ ] **Case-of behavior**
  - Nested casing support
  - Re-elaboration of hoisted patterns
  - (BIG PROJECT)

- [ ] **Prop deep dive**
  - Separate Prop as its own AST node instead of just Sort 0
  - Ensure universe inference handles Prop correctly
  - Implement large elimination restrictions (can't match on Prop-valued inductive to produce Type-valued result, unless singleton)
  - Review impredicativity rules for Prop

## Exploration

- [ ] Tactics exploration
- [ ] Explore ways to make TCEnv more monadic / more ergonomic
