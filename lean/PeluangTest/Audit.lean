/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
import PeluangLint
import PeluangTest
import PeluangTest.Lint
import PeluangTest.Plant.Axiom
import PeluangTest.Plant.ModuleTheorem
import PeluangTest.Plant.PlainTheorem

/-!
# Audit

Runs `#peluang_test_audit` over the `.lean` files of the `PeluangTest` library and the imported
`PeluangTest` modules; an audit finding is an error of this file.
-/

#peluang_test_audit
