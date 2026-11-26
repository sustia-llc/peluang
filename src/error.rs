//! Error type returned by every fallible function in the crate.

use crate::finset::FinObj;

/// Failure of a crate operation; `law` names the violated axiom as the
/// verifier's identifier string.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum Error {
    /// A `prob::Prob` law check failed for the given sample values.
    #[error("Prob axiom violated: {law}")]
    AxiomViolation {
        /// The verifier's identifier for the violated law.
        law: &'static str,
    },

    /// Building an `exec::Executor` thread pool failed.
    #[cfg(feature = "async")]
    #[error("thread pool build failed")]
    ThreadPool {
        /// The rayon builder's error.
        #[source]
        source: tokio_rayon::rayon::ThreadPoolBuildError,
    },

    /// `kernel::Kernel::new` received data of the wrong length.
    #[error("kernel data has length {found}, expected {expected}")]
    DataLength {
        /// `dom.card() * cod.card()`.
        expected: usize,
        /// The length received.
        found: usize,
    },

    /// `kernel::Kernel::new` received an entry that fails `Prob::is_nonneg`.
    #[error("kernel weight at input {input}, output {output} fails is_nonneg")]
    NegativeWeight {
        /// The input index of the entry.
        input: usize,
        /// The output index of the entry.
        output: usize,
    },

    /// `kernel::Kernel::new` received a column that fails
    /// `Prob::is_normalized`.
    #[error("kernel column of input {input} fails is_normalized")]
    NotNormalized {
        /// The input index of the column.
        input: usize,
    },

    /// A composition whose first codomain differs from its second domain.
    #[error("not composable: codomain {codomain:?}, domain {domain:?}")]
    NotComposable {
        /// The codomain of the first morphism.
        codomain: FinObj,
        /// The domain of the second morphism.
        domain: FinObj,
    },

    /// Two morphisms compared as parallel whose domains or codomains differ.
    #[error("not parallel: {:?} → {:?} and {:?} → {:?}", .fst.0, .fst.1, .snd.0, .snd.1)]
    NotParallel {
        /// The domain and codomain of the first morphism: of `f` in
        /// `almost_sure::as_equal`, of `psi ≫ f` in
        /// `prob_space::is_state_preserving`.
        fst: Box<(FinObj, FinObj)>,
        /// The domain and codomain of the second morphism: of `g` in
        /// `almost_sure::as_equal`, of `phi` in
        /// `prob_space::is_state_preserving`.
        snd: Box<(FinObj, FinObj)>,
    },

    /// A marginal or conditional whose codomain is not `fst ⊗ snd`.
    #[error("codomain {codomain:?} is not the tensor of {fst:?} and {snd:?}")]
    NotATensor {
        /// The codomain of the kernel.
        codomain: FinObj,
        /// The first factor requested.
        fst: FinObj,
        /// The second factor requested.
        snd: FinObj,
    },

    /// `bayes::bayesian_inverse` received a `p`, or `prob_space::coupling`,
    /// `prob_space::is_state_preserving` or
    /// `independence::is_cond_independent_state` a `psi`, whose domain is not
    /// the unit object.
    #[error("domain {domain:?} is not the unit object")]
    NotAState {
        /// The domain of that kernel.
        domain: FinObj,
    },

    /// `markov::Kernel::marginal` or
    /// `independence::is_cond_independent_state` received a list that is not a
    /// strictly increasing list of indices into the factors of the codomain:
    /// it is not strictly increasing, or it holds an index that is not below
    /// the number of factors.
    #[error(
        "{list:?} is not a strictly increasing list of indices into the factors of \
         {codomain:?}"
    )]
    NotAFactorList {
        /// The codomain of the kernel.
        codomain: FinObj,
        /// The list received.
        list: Vec<usize>,
    },

    /// `independence::is_cond_independent_state` received two lists that
    /// share an index.
    #[error("the lists {fst:?} and {snd:?} of factor indices of {codomain:?} share an index")]
    SharedFactorIndex {
        /// The codomain of the kernel.
        codomain: FinObj,
        /// The list of the pair that comes first in the argument order.
        fst: Vec<usize>,
        /// The list of the pair that comes later in the argument order.
        snd: Vec<usize>,
    },

    /// `conditional::conditional` or `conditional::conditional_snd` met a
    /// zero-mass column and `Prob::div_checked` returned `None` on `P::one()`
    /// over `P::one()` added `card` times.
    #[error("no uniform weight over {card} outputs")]
    NoUniformWeight {
        /// The cardinality of the conditional's codomain.
        card: usize,
    },

    /// `finset::FinObj::labeled` received a repeated label.
    #[error("duplicate label {label:?}")]
    DuplicateLabel {
        /// The label that repeats.
        label: String,
    },

    /// A product `fst * snd` overflows `usize`, or reserving the `Vec` capacity
    /// of that many elements failed. No other allocation reports this error.
    #[error("size {fst} * {snd} is too large")]
    TooLarge {
        /// The first operand.
        fst: usize,
        /// The second operand.
        snd: usize,
        /// The error of the reservation, `None` on an overflowing product.
        #[source]
        source: Option<std::collections::TryReserveError>,
    },

    /// `kernel::Kernel::from_fn` received a function with an output out of
    /// range.
    #[error("input {input} maps to output {output}, out of range")]
    NotAFunction {
        /// The input index.
        input: usize,
        /// The output index returned.
        output: usize,
    },
}

/// Result alias over the crate's `Error`.
pub type Result<T> = core::result::Result<T, Error>;
