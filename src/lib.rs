//! Finite categorical probability: Markov-category structure on finite
//! stochastic kernels over a probability-weight type `prob::Prob`, bridged to
//! the Lean theorems under `lean/` by `THEOREM_MAP.md`, whose rows pair each
//! theorem with a witness test under `tests/`.

pub mod deterministic;
pub mod error;
#[cfg(feature = "async")]
pub mod exec;
pub mod finset;
pub mod kernel;
pub mod markov;
pub mod prob;
