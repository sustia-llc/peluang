/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

import PeluangLint

/-!
# Axiom plant

Two `example`s that use the axiom `sorryAx`: one whose proof term is `sorryAx`, and one whose
proof is the tactic `exact sorryAx _ false`. Each `#guard_msgs` docstring holds the `PeluangLint`
Check A error for the hidden `_example` constant.

One `#eval`, whose `#guard_msgs` docstring holds its output and the `PeluangLint` Check A error
for its hidden `_eval` constant, which has no `_example` name component.
-/

/--
warning: declaration uses `sorry`
---
error: peluangTest: hidden constant _private.PeluangTest.Plant.Axiom.0._example depends on
axioms outside [propext, Classical.choice, Quot.sound]: [sorryAx]
-/
#guard_msgs (whitespace := lax) in
example : (2 : Nat) + 2 = 4 := sorryAx _ false

/--
warning: declaration uses `sorry`
---
error: peluangTest: hidden constant _private.PeluangTest.Plant.Axiom.0._example depends on
axioms outside [propext, Classical.choice, Quot.sound]: [sorryAx]
-/
#guard_msgs (whitespace := lax) in
example : (2 : Nat) + 2 = 4 := by exact sorryAx _ false

/--
info: 1
---
error: peluangTest: hidden constant _private.PeluangTest.Plant.Axiom.0._eval has no `_example`
name component
-/
#guard_msgs (whitespace := lax) in
#eval (1 : Nat)
