import Lake
open Lake DSL

package «Peluang» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.style.header, false⟩]

require "leanprover-community" / "mathlib" @ git "v4.35.0"

@[default_target]
lean_lib «Peluang»

@[default_target]
lean_lib «PeluangTest» where
  globs := #[.andSubmodules `PeluangTest]
