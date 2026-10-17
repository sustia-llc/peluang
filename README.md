# peluang

Categorical probability with proofs: a Lean 4 library over Mathlib's
`MarkovCategory` (FinStoch, deterministic morphisms, almost-sure equality,
conditionals, conditional independence) and a Rust crate computing the same
structures on finite stochastic kernels, bridged by `THEOREM_MAP.md` — one
Rust witness test per Lean theorem.

Anchor of record: T. Fritz, *A synthetic approach to Markov kernels,
conditional independence and theorems on sufficient statistics*,
arXiv:1908.07021; cited by definition and theorem number.

## Architecture

- `src/` — the crate: `prob.rs` (the `Prob` carrier trait; exact rationals by
  default, `f64` behind the `f64-prob` feature), `error.rs`, and the
  Markov-category modules as they land.
- `lean/` — the Lake project (`Peluang`), pinned to one Lean/Mathlib pair.
- `tests/formalization_lean/` — witness tests tagged `/// THEOREM_MAP: <id>`.
- `THEOREM_MAP.md` — Lean theorem → Rust test → anchor.
- `scripts/check_theorem_map.py` — the coverage check CI runs.
- `scripts/print_axioms.py` — the axioms of every constant defined in the
  `Peluang` library, allowlist `{propext, Classical.choice, Quot.sound}`.
- `scripts/check_lean_source.py` — `sorry`/`admit` terms and `axiom`
  declarations in `lean/` sources, outside comments and literals.

## Requirements

- Rust per `rust-toolchain.toml`; `cargo-nextest` recommended.
- Lean 4 via `elan`; the toolchain is read from `lean/lean-toolchain`.
- Python 3.12+ for the bridge check.

## Test

```sh
cargo nextest run
cargo nextest run --features f64-prob
python3 -I scripts/test_check_theorem_map.py
python3 -I scripts/check_theorem_map.py
python3 -I scripts/test_print_axioms.py
python3 -I scripts/test_check_lean_source.py
python3 -I scripts/check_lean_source.py
env -C lean lake exe cache get
env -C lean lake build
python3 -I scripts/print_axioms.py
```

## Examples

`examples/` holds the crate's usage; none yet.

## Documentation

`cargo doc --no-deps --open`. The Lean library's statements are the
specification; `THEOREM_MAP.md` says which test pins which theorem.

## Acknowledgments

Trait shapes adapted from [`sustia-llc/catgraph`](https://github.com/sustia-llc/catgraph)
(MIT); see `THIRD-PARTY.md`. Mathlib's `CopyDiscardCategory`,
`MarkovCategory`, `PositiveCategory` and `Stoch` are the foundation the Lean
library builds on.

## License

MIT — see `LICENSE`.
