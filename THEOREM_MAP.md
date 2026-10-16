# THEOREM_MAP

One row per Lean theorem under `lean/Peluang/`: the fully qualified Lean id,
the Rust witness test, and the anchor. Lean proves the universal statement;
the Rust test pins the engine at worked examples and property-generated
inputs. `scripts/check_theorem_map.py` enforces: every `theorem` or `lemma`
under `lean/Peluang/` has a row whose test exists (exactly one `#[test]` under
`tests/formalization_lean/` carrying `/// THEOREM_MAP: <id>`), or an opt-out
comment `-- WITNESS: none (<reason>)` on the line before the declaration.

Comparison rule: a theorem stated up to almost-sure equality is witnessed with
`as_equal`; an equality theorem with `==` on the exact carrier. Witness tests
compile only in the exact lane (`#[cfg(not(feature = "f64-prob"))]`). Rows for
Mathlib-owned theorems are prefixed `mathlib:` and are optional.

Anchor format: `Fritz 2020 Def./Prop./Thm. N.M` (arXiv:1908.07021) and/or the
Café post's `D`/`T` id.

| Lean id | Rust test | anchor |
|---|---|---|
