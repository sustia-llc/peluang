/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
import Batteries.Tactic.Lint
import Peluang

/-!
# Lint

Runs the Batteries declaration linters, `simpNF` among them, over every declaration of the
`Peluang` modules; a linter failure is an error of this file. The file is outside the module
system, so the linters see the imported declarations with their docstrings and bodies.
-/

#lint in Peluang
