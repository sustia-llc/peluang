import Lake
open Lake DSL

package «Peluang» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require "leanprover-community" / "mathlib" @ git "v4.35.0"

@[default_target]
lean_lib «Peluang»

@[default_target]
lean_lib «PeluangTest»
