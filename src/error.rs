//! Error type returned by every fallible function in the crate.

/// Failure of a crate operation; `law` names the violated axiom as the
/// verifier's identifier string.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// A `prob::Prob` law check failed for the given sample values.
    #[error("Prob axiom violated: {law}")]
    AxiomViolation {
        /// The verifier's identifier for the violated law.
        law: &'static str,
    },
}

/// Result alias over the crate's `Error`.
pub type Result<T> = core::result::Result<T, Error>;
