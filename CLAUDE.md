# CLAUDE.md

`peluang` is a library-first crate (`src/lib.rs`) implementing finite
categorical probability — Markov-category structure on finite stochastic
kernels — beside a Lean 4 library under `lean/` that proves the statements
the crate's witness tests pin. `THEOREM_MAP.md` is the bridge.

## Build & Test

- Rust gates, each in its own shell call with output to a file:
  `cargo metadata --locked`, `cargo fmt --all --check`,
  `cargo clippy --all-targets -- -D warnings` and `cargo nextest run`, each
  over the feature matrix: default, `--features f64-prob`,
  `--features parallel`, `--features async`, `--all-features`;
  `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --all-features`,
  ``rg -n '^\s*(///|//!).*`{3}' src/`` (must print nothing),
  `cargo tree --duplicates --all-features` (prints nothing).
- WASM gate (compile-only, `--lib` only; never `--workspace` or
  `--all-targets` on a wasm target): `cargo check --lib --target
  wasm32-wasip1`, `cargo check --lib --features parallel --target
  wasm32-wasip1-threads`, `cargo check --lib --features async --target
  wasm32-wasip1-threads`, `cargo check --lib --target
  wasm32-unknown-unknown`. The targets are installed with `rustup target
  add wasm32-wasip1 wasm32-wasip1-threads wasm32-unknown-unknown`.
- Bridge gate: `python3 -I scripts/test_check_theorem_map.py`,
  `python3 -I scripts/test_print_axioms.py`,
  `python3 -I scripts/test_check_lean_source.py`,
  `python3 -I scripts/test_check_peluangtest.py`,
  `python3 -I scripts/test_probe_selftest.py`, then
  `python3 -I scripts/check_theorem_map.py`.
- Lean gates, in order, each to a log file:
  1. `env -C lean lake exe cache get`, then `env -C lean lake build
     --no-build Mathlib` (fail closed: a non-zero exit from either stops the
     gate; never fall through to a cold build).
  2. `env -C lean lake build` — `rg -c 'warning:' <log>` must print nothing.
     The build runs Mathlib's style linters (`weak.linter.mathlibStandardSet`
     in `lean/lakefile.lean`, header linter off) and, through
     `lean/PeluangTest/Lint.lean`, `#lint in Peluang`, whose findings are
     build errors.
  3. `python3 -I scripts/check_lean_source.py`: no `sorry`/`admit`/
     `native_decide` term, no standalone `native` word and no `axiom`
     declaration under `lean/` outside `lean/.lake`, with comments,
     docstrings, string and char literals excluded.
  4. `python3 -I scripts/print_axioms.py` (needs step 2): every constant
     of the `Peluang` / `Peluang.*` modules depends only on `{propext,
     Classical.choice, Quot.sound}`; every file under `lean/Peluang/` is
     imported from `lean/Peluang.lean`; the theorems `check_theorem_map.py`
     scans equal the library's source theorems.
  5. `python3 -I scripts/check_peluangtest.py` (needs step 2, runs before
     step 6). Imported
     at private level, the `PeluangTest` modules define no constant. They
     add entries only to `moduleDocExt`, `modPkgExt`, `extraModUses` and
     `deprecatedModuleExt`. The check re-elaborates each test file with
     the lakefile `leanOptions`. Each file has no error and no surviving
     constant. It has one hidden `_example` constant per `example`
     command. Its examples use only `{propext, Classical.choice,
     Quot.sound}`. The check also reports a planted `native_decide`
     example in a temporary file.
  6. `python3 -I scripts/probe_selftest.py`: the probe reports exactly the
     constants of a planted `sorry`/`native_decide` module (the tree is
     restored afterwards).
- Pin: `lean/lean-toolchain` `leanprover/lean4:v4.35.0`; `lean/lakefile.lean`
  Mathlib `@ git "v4.35.0"`; `lean/lake-manifest.json` Mathlib rev
  `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- Witness tests compile only in the exact lane
  (`#[cfg(not(feature = "f64-prob"))]`); the `f64-prob` lane runs law tests
  with declared tolerances only.

## Lifecycle of a proof + witness change

1. Lean statement and proof under `lean/Peluang/`.
2. A `THEOREM_MAP.md` row: fully qualified Lean id → `tests/formalization_lean/<file>.rs::<fn>` → anchor.
3. The Rust test carrying `/// THEOREM_MAP: <id>` directly above `#[test]`;
   a.s.-equality theorems compare with `as_equal`, equalities with `==`.
4. Falsify the witness: perturb the engine, see the test fail with observed vs
   expected in the message, restore.
5. `scripts/check_theorem_map.py` green.

## Conventions

- Library code returns `crate::error::Error` (`thiserror`); `anyhow` only in
  examples and tests. No `unwrap()` in `src/`; `expect("invariant: …")` only
  where a precondition makes the other branch unreachable.
- No code blocks in docstrings while the repo is private (`[lib] doctest =
  false`); usage lives in `examples/` and `tests/`.
- Lean/Mathlib move together as a pair, pinned in `lean/lean-toolchain`,
  `lean/lakefile.lean` and `lean/lake-manifest.json`; never `lake update`.
- Anchors cite Fritz 2020 (arXiv:1908.07021) by definition/theorem number.
- PR per phase; tags `vX.Y.Z` are pins; `CHANGELOG.md` follows Keep a
  Changelog.

## Gotchas (do not regress)

- Every `lake` command runs as `env -C lean lake …`, never `lake -d lean
  …`. elan picks the toolchain from the working directory's
  `lean-toolchain`, not from `-d`: from the repo root, `lake -d lean`
  runs the elan default toolchain. `lake -d lean exe cache get` also
  exits 1 after downloading (`no such file or directory … lean-toolchain`).
  CI uses `working-directory: lean`; `scripts/print_axioms.py` runs `lake`
  with `cwd=lean/`.
- `lake exe cache get` exits 0 ("No files to download") while a Mathlib
  olean is missing; `lake build --no-build Mathlib` exits 3 on it, and
  `lake exe cache get!` restores it.
- `scripts/print_axioms.py` audits the oleans on disk; it refuses to run
  when `lake build --no-build Peluang` reports the build stale (a probe on
  a stale build audits deleted or edited sources).
- `lean_lib Peluang` takes the default root; an `.andSubmodules` glob
  fails the build while `lean/Peluang/` does not exist. Every file under
  `lean/Peluang/` is reached through an import from `lean/Peluang.lean`.
- `lean_lib PeluangTest` (second default target) builds every file under
  `lean/PeluangTest/` through `globs := #[.andSubmodules `PeluangTest]`.
  It holds `example`s and the `#lint` file only; `print_axioms.py` does
  not audit it, and `check_lean_source.py` scans it. `Lint.lean` is a
  plain (non-`module`) file, reached through the glob and not imported
  from `lean/PeluangTest.lean`.
- Lean files use the module system (`module`, `public import`, theorems in
  a `public section`), matching the Mathlib files they import.
