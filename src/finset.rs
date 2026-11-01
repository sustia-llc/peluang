//! Finite objects: ordered lists of factors, each a cardinality with optional
//! element labels, with the tensor product as concatenation of the lists.

use std::collections::BTreeSet;

use crate::error::{Error, Result};

/// `rows * cols`, or `Error::TooLarge` when the product overflows `usize`.
pub(crate) fn product(rows: usize, cols: usize) -> Result<usize> {
    rows.checked_mul(cols).ok_or(Error::TooLarge {
        fst: rows,
        snd: cols,
    })
}

/// An empty vector with capacity for `rows * cols` elements, or
/// `Error::TooLarge` when the product overflows `usize` or the allocator
/// refuses it.
pub(crate) fn reserve<T>(rows: usize, cols: usize) -> Result<Vec<T>> {
    let len = product(rows, cols)?;
    let mut out = Vec::new();
    out.try_reserve_exact(len).map_err(|_| Error::TooLarge {
        fst: rows,
        snd: cols,
    })?;
    Ok(out)
}

/// One factor of a `FinObj`: a cardinality, possibly `0`, with optional element
/// labels.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Factor {
    card: usize,
    labels: Option<Vec<String>>,
}

impl Factor {
    /// The number of elements.
    pub fn card(&self) -> usize {
        self.card
    }

    /// The element labels in index order, `None` on an unlabeled factor.
    pub fn labels(&self) -> Option<&[String]> {
        self.labels.as_deref()
    }
}

/// A finite object: the product of an ordered list of factors. Two objects are
/// equal exactly when their factor lists are equal, labels included.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinObj {
    factors: Vec<Factor>,
    card: usize,
}

impl FinObj {
    /// The object with one unlabeled factor of `card` elements.
    pub fn new(card: usize) -> Self {
        Self {
            factors: vec![Factor { card, labels: None }],
            card,
        }
    }

    /// The object with one factor whose elements are `labels` in order, or
    /// `Error::DuplicateLabel` naming the first label that repeats.
    pub fn labeled(labels: Vec<String>) -> Result<Self> {
        let mut seen = BTreeSet::new();
        for label in &labels {
            if !seen.insert(label) {
                return Err(Error::DuplicateLabel {
                    label: label.clone(),
                });
            }
        }
        let card = labels.len();
        Ok(Self {
            factors: vec![Factor {
                card,
                labels: Some(labels),
            }],
            card,
        })
    }

    /// The monoidal unit: no factors, one element.
    pub fn unit() -> Self {
        Self {
            factors: Vec::new(),
            card: 1,
        }
    }

    /// The product of the factor cardinalities.
    pub fn card(&self) -> usize {
        self.card
    }

    /// The factors in order.
    pub fn factors(&self) -> &[Factor] {
        &self.factors
    }

    /// The object whose factors are those of `self` followed by those of
    /// `other`, or `Error::TooLarge` when the cardinality product overflows
    /// `usize` or the factor list cannot be allocated.
    pub fn tensor(&self, other: &Self) -> Result<Self> {
        let card = product(self.card, other.card)?;
        let mut factors = reserve(self.factors.len() + other.factors.len(), 1)?;
        factors.extend_from_slice(&self.factors);
        factors.extend_from_slice(&other.factors);
        Ok(Self { factors, card })
    }
}
