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
  default, `f64` behind the `f64-prob` feature; `sum`), `exec.rs` (behind
  `async`), `error.rs`, and the Markov-category modules as they land.
- `lean/` — the Lake project (`Peluang`), pinned by `lean/lean-toolchain`,
  `lean/lakefile.lean` and `lean/lake-manifest.json`; `lean/Peluang.lean` is
  the library root and imports every file under `lean/Peluang/`.
- `tests/formalization_lean/` — witness tests tagged `/// THEOREM_MAP: <id>`
  (none yet).
- `THEOREM_MAP.md` — Lean theorem → Rust test → anchor.
- `scripts/check_theorem_map.py` — every theorem of the library has a
  `THEOREM_MAP.md` row with an existing witness, or a `-- WITNESS: none`
  opt-out.
- `scripts/print_axioms.py` — the axioms of every constant defined in the
  `Peluang` library, allowlist `{propext, Classical.choice, Quot.sound}`.
- `scripts/probe_selftest.py` — `print_axioms.py` against a planted module
  of `sorry` and `native_decide` constants.
- `scripts/check_lean_source.py` — `sorry`/`admit` terms and `axiom`
  declarations in `lean/` sources, outside comments and literals.

## Features

All off by default.

- `f64-prob` — `Prob` for `f64` with a declared tolerance; witness tests do
  not compile in this lane.
- `parallel` — `prob::sum` runs on rayon (via `rayon-cond`) at or above
  `prob::PAR_THRESHOLD` terms.
- `async` — implies `parallel`; `exec::Executor` owns a rayon pool and
  `Executor::run` awaits a closure on it (`tokio-rayon`). The crate creates
  no async runtime.

## WebAssembly

WASI first: `wasm32-wasip1-threads` with `parallel`/`async`,
`wasm32-wasip1` without them; `wasm32-unknown-unknown` builds the library
with default features. Browsers are out of scope. CI checks these with
`cargo check --lib`.

## Requirements

- Rust per `rust-toolchain.toml`; `cargo-nextest` recommended.
- Lean 4 via `elan`; the toolchain is read from `lean/lean-toolchain`.
- Python 3.12+ for the scripts.

## Test

```sh
# Rust
cargo nextest run
cargo nextest run --features f64-prob
cargo nextest run --features async
cargo nextest run --all-features
# scripts and bridge (no Lean needed)
python3 -I scripts/test_check_theorem_map.py
python3 -I scripts/test_print_axioms.py
python3 -I scripts/test_check_lean_source.py
python3 -I scripts/check_lean_source.py
python3 -I scripts/check_theorem_map.py
# Lean (every lake command runs with lean/ as the working directory)
env -C lean lake exe cache get
env -C lean lake build --no-build Mathlib
env -C lean lake build
python3 -I scripts/print_axioms.py
python3 -I scripts/probe_selftest.py
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
