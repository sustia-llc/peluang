/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

import PeluangLint

/-!
# Axiom plant

An `example` whose proof term is the axiom `sorryAx`. The `#guard_msgs` docstring holds the
`PeluangLint` Check A error for its hidden `_example` constant.
-/

/--
warning: declaration uses `sorry`
---
error: peluangTest: hidden constant _private.PeluangTest.Plant.Axiom.0._example depends on
axioms outside [propext, Classical.choice, Quot.sound]: [sorryAx]
-/
#guard_msgs (whitespace := lax) in
example : (2 : Nat) + 2 = 4 := sorryAx _ false
