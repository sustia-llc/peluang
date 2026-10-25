/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

import PeluangLint

/-!
# Declaration plant, `module` form

A `theorem` in a `public section` of a `module` file. The `#guard_msgs` docstring holds the
`PeluangLint` Check B error for the constant it adds to the module.
-/

public section

/--
error: peluangTest: the command adds constants to the module: [PeluangTest.Plant.moduleTheorem]
-/
#guard_msgs in
theorem PeluangTest.Plant.moduleTheorem : True := trivial

end
