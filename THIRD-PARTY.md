# Third-party material

Items copied or adapted into this repository, with their licences. Dependencies
declared in `Cargo.toml` and `lean/lakefile.lean` are not listed; their licences
travel with the packages (Mathlib: Apache-2.0).

| item | from | licence | where |
|---|---|---|---|
| a carrier trait paired with a runtime axiom verifier that returns the first violated law by name | `sustia-llc/catgraph`, `catgraph-applied/src/rig.rs` (`Rig`, `verify_rig_axioms`) | MIT | `src/prob.rs` (`Prob`, `verify_prob_axioms`; shape only, no code copied) |
| a composition trait with `domain`, `codomain`, a fallible `compose` in diagrammatic order, and a `composable` check | `sustia-llc/catgraph`, `catgraph/src/category.rs` (`Composable`) | MIT | `src/markov.rs` (`Compose`, shape only, no code copied) |
