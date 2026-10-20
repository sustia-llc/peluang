//! Canonical integration tests for the `Prob` trait: law verification,
//! checked division and normalization, in the exact lane and the `f64` lane.

#[cfg(not(feature = "f64-prob"))]
mod common;

mod rejection {
    use peluang::error::Error;
    use peluang::prob::{Exact, Prob, verify_prob_axioms};

    /// Exact weights whose `add` is left projection: associative, with `zero`
    /// as right identity, non-commutative.
    #[derive(Clone, Debug, PartialEq)]
    struct LeftProj(Exact);

    impl Prob for LeftProj {
        fn zero() -> Self {
            LeftProj(Exact::zero())
        }

        fn one() -> Self {
            LeftProj(Exact::one())
        }

        fn add(&self, _other: &Self) -> Self {
            self.clone()
        }

        fn mul(&self, other: &Self) -> Self {
            LeftProj(self.0.mul(&other.0))
        }

        fn div_checked(&self, other: &Self) -> Option<Self> {
            self.0.div_checked(&other.0).map(LeftProj)
        }

        fn is_nonneg(&self) -> bool {
            self.0.is_nonneg()
        }

        fn approx_eq(&self, other: &Self) -> bool {
            self.0.approx_eq(&other.0)
        }
    }

    #[test]
    fn verify_prob_axioms_rejects_noncommutative_add() {
        let a = LeftProj(Exact::new(7.into(), 10.into()));
        let b = LeftProj(Exact::new(3.into(), 10.into()));
        let c = LeftProj(Exact::new(1.into(), 2.into()));
        let got = verify_prob_axioms(&a, &b, &c);
        assert!(
            matches!(got, Err(Error::AxiomViolation { law: "add_comm" })),
            "expected Err(AxiomViolation {{ law: \"add_comm\" }}) on left-projection add, got {got:?}"
        );
    }
}

#[cfg(not(feature = "f64-prob"))]
mod exact {
    use crate::common::{closed_form, telescoping};
    use peluang::error::Error;
    use peluang::prob::{Exact, PAR_THRESHOLD, Prob, sum, verify_prob_axioms};

    fn r(n: i64, d: i64) -> Exact {
        Exact::new(n.into(), d.into())
    }

    #[test]
    fn verify_prob_axioms_holds_on_nonzero_triple() {
        let (a, b, c) = (r(7, 10), r(3, 10), r(1, 2));
        let got = verify_prob_axioms(&a, &b, &c);
        assert!(
            got.is_ok(),
            "expected Ok(()) on (7/10, 3/10, 1/2), got {got:?}"
        );
    }

    #[test]
    fn verify_prob_axioms_holds_with_zero_sample() {
        let (a, b, c) = (r(0, 1), r(1, 1), r(2, 3));
        let got = verify_prob_axioms(&a, &b, &c);
        assert!(got.is_ok(), "expected Ok(()) on (0, 1, 2/3), got {got:?}");
    }

    #[test]
    fn axiom_violation_displays_law() {
        let err = Error::AxiomViolation { law: "add_comm" };
        let shown = err.to_string();
        assert_eq!(
            shown, "Prob axiom violated: add_comm",
            "expected Display to name the law, got {shown:?}"
        );
    }

    #[test]
    fn div_checked_by_zero_is_none() {
        let got = r(3, 5).div_checked(&Exact::zero());
        assert_eq!(got, None, "expected None for 3/5 ÷ 0, got {got:?}");
    }

    #[test]
    fn div_checked_rain_given_cold() {
        let got = r(3, 5).div_checked(&r(4, 5));
        let want = Some(r(3, 4));
        assert_eq!(got, want, "expected 3/5 ÷ 4/5 = Some(3/4), got {got:?}");
    }

    #[test]
    fn is_normalized_true_on_complementary_pair() {
        let got = Exact::is_normalized([r(7, 10), r(3, 10)]);
        assert!(got, "expected [7/10, 3/10] normalized (sum 1), got {got}");
    }

    #[test]
    fn is_normalized_false_when_sum_exceeds_one() {
        let got = Exact::is_normalized([r(7, 10), r(3, 10), r(1, 10)]);
        assert!(
            !got,
            "expected [7/10, 3/10, 1/10] not normalized (sum 11/10), got {got}"
        );
    }

    #[test]
    fn is_normalized_false_on_empty() {
        let got = Exact::is_normalized(Vec::<Exact>::new());
        assert!(!got, "expected [] not normalized (sum 0), got {got}");
    }

    #[test]
    fn sum_telescopes_across_threshold() {
        for n in [
            0,
            1,
            PAR_THRESHOLD - 1,
            PAR_THRESHOLD,
            3 * PAR_THRESHOLD + 7,
        ] {
            let got = sum(&telescoping(n));
            let want = closed_form(n);
            assert_eq!(
                got, want,
                "expected sum of 1/((i+1)(i+2)) over i in 0..{n} = {want}, got {got}"
            );
        }
    }

    #[test]
    fn is_nonneg_sign() {
        let pos = r(3, 5).is_nonneg();
        let zero = Exact::zero().is_nonneg();
        let neg = r(-1, 5).is_nonneg();
        assert!(pos, "expected 3/5 nonneg, got {pos}");
        assert!(zero, "expected 0 nonneg, got {zero}");
        assert!(!neg, "expected -1/5 not nonneg, got {neg}");
    }
}

#[cfg(feature = "f64-prob")]
mod float {
    use peluang::prob::{Prob, verify_prob_axioms};

    #[test]
    fn verify_prob_axioms_holds_on_nonzero_triple() {
        let got = verify_prob_axioms(&0.7_f64, &0.3, &0.5);
        assert!(
            got.is_ok(),
            "expected Ok(()) on (0.7, 0.3, 0.5), got {got:?}"
        );
    }

    #[test]
    fn verify_prob_axioms_holds_with_zero_sample() {
        let got = verify_prob_axioms(&0.0_f64, &1.0, &(2.0 / 3.0));
        assert!(got.is_ok(), "expected Ok(()) on (0, 1, 2/3), got {got:?}");
    }

    #[test]
    fn div_checked_by_zero_is_none() {
        let got = 0.6_f64.div_checked(&0.0);
        assert_eq!(got, None, "expected None for 0.6 ÷ 0.0, got {got:?}");
    }

    #[test]
    fn div_checked_rain_given_cold() {
        let got = 0.6_f64.div_checked(&0.8);
        let holds = matches!(got, Some(q) if q.approx_eq(&0.75));
        assert!(holds, "expected 0.6 ÷ 0.8 ≈ Some(0.75), got {got:?}");
    }

    #[test]
    fn is_normalized_true_on_complementary_pair() {
        let got = f64::is_normalized([0.7, 0.3]);
        assert!(got, "expected [0.7, 0.3] normalized (sum 1.0), got {got}");
    }

    #[test]
    fn is_normalized_true_within_tolerance() {
        let got = f64::is_normalized([0.1; 10]);
        assert!(
            got,
            "expected [0.1; 10] normalized within F64_TOLERANCE, got {got}"
        );
    }

    #[test]
    fn is_normalized_false_when_sum_exceeds_one() {
        let got = f64::is_normalized([0.7, 0.3, 0.1]);
        assert!(
            !got,
            "expected [0.7, 0.3, 0.1] not normalized (sum 1.1), got {got}"
        );
    }

    #[test]
    fn is_normalized_false_on_empty() {
        let got = f64::is_normalized(Vec::<f64>::new());
        assert!(!got, "expected [] not normalized (sum 0.0), got {got}");
    }

    #[test]
    fn is_nonneg_sign() {
        let pos = 0.6_f64.is_nonneg();
        let zero = 0.0_f64.is_nonneg();
        let neg = (-0.2_f64).is_nonneg();
        assert!(pos, "expected 0.6 nonneg, got {pos}");
        assert!(zero, "expected 0.0 nonneg, got {zero}");
        assert!(!neg, "expected -0.2 not nonneg, got {neg}");
    }
}
