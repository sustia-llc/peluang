/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
import PeluangLint

/-!
# Declaration plant, plain form

A `theorem` in a plain (non-`module`) file. The `#guard_msgs` docstring holds the `PeluangLint`
Check B error for the constant it adds to the module.
-/

/--
error: peluangTest: the command adds constants to the module: [PeluangTest.Plant.plainTheorem]
-/
#guard_msgs in
theorem PeluangTest.Plant.plainTheorem : True := trivial
