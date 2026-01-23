# TODO

## Upcoming

- [ ] Add inference/checking for `let` expressions
- [ ] Add multi-let syntax (`let x := a, y := b in ...`)
- [ ] Add infix operator syntax (user-defined operators with precedence)
- [ ] Add custom syntax support (maybe?)

## UI/Editor

- [ ] Keyboard shortcut in text editor to comment/uncomment code
- [ ] Keyboard shortcut to toggle binder at cursor between `()` vs `{}`

## Big Projects

- [ ] **Records**
  - Parser for record definitions
  - Elaboration + checking for definitions
  - Elaboration + checking for call sites (construction, projection)
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
