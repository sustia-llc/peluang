# Changelog

All notable changes to this project are documented in this file. The format
follows [Keep a Changelog 1.1.0](https://keepachangelog.com/en/1.1.0/); the
git tag is the authoritative pin.

## [Unreleased]

### Added

- Crate scaffold: `error.rs` (`thiserror` enum, `Result<T>`), `prob.rs`
  (`Prob` trait, exact `Ratio<BigInt>` carrier, `f64` behind `f64-prob`,
  `verify_prob_axioms`), `tests/canonical.rs`.
- `THEOREM_MAP.md` schema and `scripts/check_theorem_map.py`.
- CI: `rust.yml`, `theorem-map.yml`.
