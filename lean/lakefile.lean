import Lake
open Lake DSL

/-!
LeanUI Lake package.

This package is the Lean-side backend for leanUI. Two modes:

* **Core mode (default).** The TypeScript bridge invokes `lean --json` directly on a
  temporary file — it does NOT need this package to be built. Fast, offline, no deps.

* **Mathlib mode (opt-in).** Built with `-K mathlib=on`, this package requires Mathlib
  and the bridge invokes `lake env lean --json <file>` with this package as the cwd so
  Mathlib is on the import path. Enable + build once with:

      cd lean
      lake -K mathlib=on update
      lake -K mathlib=on build

  (Mathlib's tag must match the toolchain in `lean-toolchain`.)
-/

package leanui where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

meta if get_config? mathlib |>.isSome then
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"

@[default_target]
lean_lib LeanUI where

-- The extractor as a compiled executable. Building it once (`lake build extract`)
-- avoids recompiling Extract.lean (which imports all of `Lean`) on every analyze
-- call. `supportInterpreter := true` is REQUIRED: the extractor elaborates the
-- user's file, so the binary must expose symbols to the Lean interpreter (else
-- syntax-extension elaborators like `=` fail with "elaboration function not
-- implemented"). The bridge runs this binary when present, else `lean --run`.
lean_exe extract where
  root := `Extract
  supportInterpreter := true
