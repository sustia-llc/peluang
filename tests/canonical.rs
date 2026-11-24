//! Canonical integration tests. On `Exact` weights in every feature lane: the
//! `Prob` trait (law verification, checked division and normalization), the
//! rejections of each `Kernel` constructor and operation, `Kernel::approx_eq`,
//! composition and tensor at literals, `is_deterministic`, `is_independent` at
//! a two-input kernel and at a 3×2 state, the rejection of a
//! wrong split by `is_independent` and of misaligned domains by
//! `cond_indep_form`, results across `PAR_THRESHOLD`, size
//! errors, and the post's eq. (9). In every feature lane: the `FinObj` object
//! laws and rejections. On `f64` weights under `f64-prob`: the `Prob` trait,
//! `Kernel::approx_eq`, the input tests of `Kernel::new`, worked `compose`,
//! `tensor`, marginals and `is_deterministic` under `Kernel::approx_eq`,
//! `is_independent` under `Prob::approx_eq`, and `bayesian_inverse`,
//! `is_bayesian_inverse` and `is_as_deterministic`.

mod common;
#[path = "formalization_lean/fixtures.rs"]
mod fixtures;

mod rejection {
    use peluang::bayes::bayesian_inverse;
    use peluang::error::{Error, Result};
    use peluang::finset::FinObj;
    use peluang::kernel::Kernel;
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

    /// Under left-projection `add`, a fold from `P::zero()` stays at
    /// `P::zero()`: the mass of each column of the joint, and `P::one()` added
    /// three times.
    #[test]
    fn bayesian_inverse_reports_no_uniform_weight_on_left_projection_add() -> Result<()> {
        let (x, y) = (FinObj::new(3), FinObj::new(2));
        let p = Kernel::<LeftProj>::from_fn(FinObj::unit(), x.clone(), |_| 0)?;
        let f = Kernel::<LeftProj>::from_fn(x, y, |_| 0)?;
        let got = bayesian_inverse(&p, &f);
        assert!(
            matches!(got, Err(Error::NoUniformWeight { card: 3 })),
            "bayesian_inverse(point at 0 of [3], constant 0 : [3] → [2]) on left-projection add: \
             expected Err(NoUniformWeight {{ card: 3 }}), observed {got:?}"
        );
        Ok(())
    }
}

mod exact {
    use crate::common::{closed_form, telescoping};
    use crate::fixtures::r;
    use peluang::error::Error;
    use peluang::prob::{Exact, PAR_THRESHOLD, Prob, sum, verify_prob_axioms};

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

mod objects {
    use crate::fixtures::labels;
    use peluang::error::{Error, Result};
    use peluang::finset::FinObj;

    #[test]
    fn tensor_is_concatenation() -> Result<()> {
        let (x, y, z) = (FinObj::new(2), labels(&["a", "b", "c"])?, FinObj::new(5));
        let i = FinObj::unit();
        let left = x.tensor(&y)?.tensor(&z)?;
        let right = x.tensor(&y.tensor(&z)?)?;
        assert_eq!(left, right, "expected (X ⊗ Y) ⊗ Z == X ⊗ (Y ⊗ Z)");
        assert_eq!(x.tensor(&i)?, x, "expected X ⊗ I == X");
        assert_eq!(i.tensor(&x)?, x, "expected I ⊗ X == X");
        let observed = (left.card(), left.factors().to_vec());
        let expected = (30, [x.factors(), y.factors(), z.factors()].concat());
        assert_eq!(
            observed, expected,
            "expected card 30 and the factors of X, Y, Z in order, observed on the left"
        );
        Ok(())
    }

    #[test]
    fn one_element_object_is_not_unit() {
        let (one, unit) = (FinObj::new(1), FinObj::unit());
        assert_ne!(one, unit, "expected FinObj::new(1) != FinObj::unit()");
        assert_eq!(
            (one.card(), unit.card()),
            (1, 1),
            "expected card 1 on both, observed on the left"
        );
    }

    #[test]
    fn tensor_overflow_is_too_large() {
        let got = FinObj::new(usize::MAX).tensor(&FinObj::new(2));
        assert!(
            matches!(
                got,
                Err(Error::TooLarge {
                    fst: usize::MAX,
                    snd: 2,
                    source: None
                })
            ),
            "expected TooLarge {{ fst: usize::MAX, snd: 2, source: None }}, observed {got:?}"
        );
    }

    #[test]
    fn labeled_rejects_a_repeat() {
        let got = labels(&["idle", "on", "off", "on", "off"]);
        assert!(
            matches!(&got, Err(Error::DuplicateLabel { label }) if label == "on"),
            "expected DuplicateLabel {{ label: \"on\" }}, observed {got:?}"
        );
    }

    #[test]
    fn labels_are_part_of_identity() -> Result<()> {
        let abc = labels(&["a", "b", "c"])?;
        let xyz = labels(&["x", "y", "z"])?;
        assert_eq!(
            (abc.card(), xyz.card()),
            (3, 3),
            "expected equal cardinalities, observed on the left"
        );
        assert_ne!(abc, xyz, "expected different labels to compare unequal");
        assert_ne!(abc, FinObj::new(3), "expected labels to count against none");
        Ok(())
    }
}

mod kernels {
    use std::collections::TryReserveError;
    use std::error::Error as StdError;

    use crate::c_tensor_s;
    use crate::common::{closed_form, telescoping};
    use crate::fixtures::{
        assert_kernel, c, d, e, f, h, labels, lit, obj_s, obj_t, obj_w, points, psi_t, r, s, show,
    };
    use peluang::deterministic::is_deterministic;
    use peluang::error::{Error, Result};
    use peluang::finset::FinObj;
    use peluang::independence::{cond_indep_form, is_independent};
    use peluang::kernel::Kernel;
    use peluang::markov::{Compose, Tensor};
    use peluang::prob::{Exact, PAR_THRESHOLD, Prob};

    #[test]
    fn compose_across_labels_is_not_composable() -> Result<()> {
        let abc = FinObj::labeled(vec!["a".to_owned(), "b".to_owned(), "c".to_owned()])?;
        let f = Kernel::state(abc.clone(), vec![r(1, 1), r(0, 1), r(0, 1)])?;
        let got = f.compose(&s()?);
        assert!(
            matches!(&got, Err(Error::NotComposable { codomain, domain })
                if *codomain == abc && *domain == obj_w()?),
            "expected NotComposable from abc to W, observed {got:?}"
        );
        Ok(())
    }

    #[test]
    fn new_rejects_each_input_in_order() {
        let got = Kernel::<Exact>::new(FinObj::new(usize::MAX), FinObj::new(2), Vec::new());
        assert!(
            matches!(
                got,
                Err(Error::TooLarge {
                    fst: usize::MAX,
                    snd: 2,
                    source: None
                })
            ),
            "expected TooLarge {{ fst: usize::MAX, snd: 2, source: None }} ahead of DataLength, observed {got:?}"
        );

        let (dom, cod) = (FinObj::new(2), FinObj::new(3));
        let got = Kernel::new(dom.clone(), cod.clone(), vec![r(1, 1); 5]);
        assert!(
            matches!(
                got,
                Err(Error::DataLength {
                    expected: 6,
                    found: 5
                })
            ),
            "expected DataLength {{ expected: 6, found: 5 }}, observed {got:?}"
        );

        let negative = vec![r(1, 2), r(1, 1), r(1, 1), r(-1, 3), r(0, 1), r(4, 3)];
        let got = Kernel::new(dom.clone(), cod.clone(), negative);
        assert!(
            matches!(
                got,
                Err(Error::NegativeWeight {
                    input: 1,
                    output: 0
                })
            ),
            "expected NegativeWeight at input 1, output 0 ahead of the unnormalized column 0, observed {got:?}"
        );

        let unnormalized = vec![r(1, 1), r(0, 1), r(0, 1), r(1, 2), r(1, 2), r(1, 2)];
        let got = Kernel::new(dom, cod, unnormalized);
        assert!(
            matches!(got, Err(Error::NotNormalized { input: 1 })),
            "expected NotNormalized at input 1, observed {got:?}"
        );
    }

    #[test]
    fn empty_domain_is_accepted_and_empty_codomain_rejected() -> Result<()> {
        let empty = Kernel::<Exact>::new(FinObj::new(0), FinObj::new(3), Vec::new())?;
        assert_eq!(
            empty.column(0),
            None,
            "expected no column on ∅ → Y, observed on the left"
        );
        let got = Kernel::<Exact>::new(FinObj::new(2), FinObj::new(0), Vec::new());
        assert!(
            matches!(got, Err(Error::NotNormalized { input: 0 })),
            "expected NotNormalized at input 0 on X → ∅, observed {got:?}"
        );
        Ok(())
    }

    #[test]
    fn state_has_unit_domain() -> Result<()> {
        let state = psi_t()?;
        assert_eq!(
            state.domain(),
            &FinObj::unit(),
            "expected domain FinObj::unit(), observed on the left"
        );
        assert_kernel(
            "psi_t",
            &state,
            &Kernel::new(FinObj::unit(), obj_t()?, vec![r(1, 5), r(4, 5)])?,
        );
        Ok(())
    }

    #[test]
    fn from_fn_rejects_an_output_out_of_range() -> Result<()> {
        let got = Kernel::<Exact>::from_fn(FinObj::new(3), FinObj::new(4), |x| 2 * x + 1);
        assert!(
            matches!(
                got,
                Err(Error::NotAFunction {
                    input: 2,
                    output: 5
                })
            ),
            "expected NotAFunction at input 2, output 5, observed {got:?}"
        );
        let got = Kernel::<Exact>::from_fn(obj_w()?, obj_s()?, |x| usize::from(x > 0))?;
        assert_kernel("from_fn", &got, &d()?);
        Ok(())
    }

    #[test]
    fn compose_is_chapman_kolmogorov_in_diagrammatic_order() -> Result<()> {
        let t = obj_t()?;
        let a = lit(
            t.clone(),
            t.clone(),
            &[&[r(1, 2), r(1, 2)], &[r(1, 4), r(3, 4)]],
        )?;
        let b = lit(
            t.clone(),
            t.clone(),
            &[&[r(1, 3), r(2, 3)], &[r(1, 1), r(0, 1)]],
        )?;
        let a_then_b = lit(
            t.clone(),
            t.clone(),
            &[&[r(2, 3), r(1, 3)], &[r(5, 6), r(1, 6)]],
        )?;
        let b_then_a = lit(
            t.clone(),
            t.clone(),
            &[&[r(1, 3), r(2, 3)], &[r(1, 2), r(1, 2)]],
        )?;
        assert_kernel("a ≫ b", &a.compose(&b)?, &a_then_b);
        assert_kernel("b ≫ a", &b.compose(&a)?, &b_then_a);
        assert_kernel("c ≫ s", &c()?.compose(&s()?)?, &h()?);

        let got = s()?.compose(&c()?);
        assert!(
            matches!(&got, Err(Error::NotComposable { codomain, domain })
                if *codomain == obj_s()? && *domain == t),
            "expected NotComposable from S to T, observed {got:?}"
        );
        let got = s()?.composable(&c()?);
        assert!(
            matches!(got, Err(Error::NotComposable { .. })),
            "expected composable to report NotComposable, observed {got:?}"
        );
        Ok(())
    }

    #[test]
    fn tensor_is_the_product_with_the_first_factor_major() -> Result<()> {
        let t = obj_t()?;
        let a = lit(
            t.clone(),
            t.clone(),
            &[&[r(1, 2), r(1, 2)], &[r(1, 4), r(3, 4)]],
        )?;
        let b = lit(
            t.clone(),
            t.clone(),
            &[&[r(1, 3), r(2, 3)], &[r(1, 1), r(0, 1)]],
        )?;
        let tt = t.tensor(&t)?;
        let expected = lit(
            tt.clone(),
            tt,
            &[
                &[r(1, 6), r(1, 3), r(1, 6), r(1, 3)],
                &[r(1, 2), r(0, 1), r(1, 2), r(0, 1)],
                &[r(1, 12), r(1, 6), r(1, 4), r(1, 2)],
                &[r(1, 4), r(0, 1), r(3, 4), r(0, 1)],
            ],
        )?;
        assert_kernel("a ⊗ₘ b", &a.tensor(&b)?, &expected);

        let mixed = c()?.tensor(&psi_t()?)?;
        let expected = lit(
            obj_t()?,
            obj_w()?.tensor(&obj_t()?)?,
            &[
                &[r(1, 10), r(2, 5), r(1, 10), r(2, 5), r(0, 1), r(0, 1)],
                &[r(0, 1), r(0, 1), r(1, 20), r(1, 5), r(3, 20), r(3, 5)],
            ],
        )?;
        assert_kernel("c ⊗ₘ psi_t", &mixed, &expected);

        assert_kernel("c ⊗ₘ s", &c()?.tensor(&s()?)?, &c_tensor_s()?);
        Ok(())
    }

    #[test]
    fn tensor_overflow_is_too_large() -> Result<()> {
        let huge = FinObj::new(usize::MAX);
        let empty = Kernel::<Exact>::new(FinObj::new(0), huge, Vec::new())?;
        let got = empty.tensor(&empty);
        assert!(
            matches!(
                got,
                Err(Error::TooLarge {
                    fst: usize::MAX,
                    snd: usize::MAX,
                    source: None
                })
            ),
            "expected TooLarge from the codomain product, observed {got:?}"
        );
        Ok(())
    }

    #[test]
    fn approx_eq_compares_objects_and_entries() -> Result<()> {
        let first = |cod: FinObj| points(FinObj::unit(), cod, &[0]);
        let on_off = first(obj_s()?)?;
        for (name, other, expected) in [
            ("itself", first(obj_s()?)?, true),
            (
                "another entry",
                Kernel::state(obj_s()?, vec![r(0, 1), r(1, 1)])?,
                false,
            ),
            ("other labels", first(obj_t()?)?, false),
            ("other cardinality", first(obj_w()?)?, false),
        ] {
            let observed = on_off.approx_eq(&other);
            assert_eq!(
                observed, expected,
                "codomain, {name}: expected {expected}, observed {observed}"
            );
        }
        let del_s = Kernel::<Exact>::del(&obj_s()?)?;
        for (name, other) in [
            ("other labels", Kernel::del(&obj_t()?)?),
            ("other cardinality", Kernel::del(&obj_w()?)?),
        ] {
            let observed = del_s.approx_eq(&other);
            assert!(
                !observed,
                "domain, {name}: expected false, observed {observed}"
            );
        }
        Ok(())
    }

    #[track_caller]
    fn assert_not_a_tensor(
        route: &str,
        got: &Result<Kernel<Exact>>,
        cod: &FinObj,
        x: &FinObj,
        y: &FinObj,
    ) {
        assert!(
            matches!(got, Err(Error::NotATensor { codomain, fst, snd })
                if codomain == cod && fst == x && snd == y),
            "{route}: expected NotATensor {{ codomain: {cod:?}, fst: {x:?}, snd: {y:?} }}, observed {got:?}"
        );
    }

    #[test]
    fn marginals_reject_a_wrong_split() -> Result<()> {
        let (one, two, three) = (FinObj::new(1), FinObj::new(2), FinObj::new(3));
        let point = vec![r(1, 1), r(0, 1), r(0, 1), r(0, 1), r(0, 1), r(0, 1)];
        let cod = two.tensor(&three)?;
        let joint = Kernel::state(cod.clone(), point.clone())?;
        for (route, got, x, y) in [
            (
                "marginal_fst, 3·2 split",
                joint.marginal_fst(&three, &two),
                &three,
                &two,
            ),
            (
                "marginal_snd, 3·2 split",
                joint.marginal_snd(&three, &two),
                &three,
                &two,
            ),
            (
                "marginal_fst, mismatch only on snd",
                joint.marginal_fst(&two, &two),
                &two,
                &two,
            ),
            (
                "marginal_snd, mismatch only on fst",
                joint.marginal_snd(&one, &three),
                &one,
                &three,
            ),
        ] {
            assert_not_a_tensor(route, &got, &cod, x, y);
        }

        let (abc, xyz) = (labels(&["a", "b", "c"])?, labels(&["x", "y", "z"])?);
        let labeled_cod = abc.tensor(&two)?;
        let labeled = Kernel::state(labeled_cod.clone(), point.clone())?;
        assert_not_a_tensor(
            "marginal_fst, labels differ at equal cardinalities",
            &labeled.marginal_fst(&xyz, &two),
            &labeled_cod,
            &xyz,
            &two,
        );

        let flat = FinObj::new(6);
        let joint = Kernel::state(flat.clone(), point)?;
        let got = joint.marginal_fst(&two, &three);
        assert!(
            matches!(got, Err(Error::NotATensor { .. })),
            "expected NotATensor on a single 6-element factor, observed {got:?}"
        );
        let longer = two.tensor(&three)?;
        assert_not_a_tensor(
            "marginal_fst, x has more factors than the codomain",
            &joint.marginal_fst(&longer, &FinObj::unit()),
            &flat,
            &longer,
            &FinObj::unit(),
        );
        let huge = FinObj::new(usize::MAX);
        let got = joint.marginal_snd(&huge, &huge);
        assert!(
            matches!(got, Err(Error::NotATensor { .. })),
            "expected NotATensor on a split whose product overflows, observed {got:?}"
        );
        Ok(())
    }

    #[test]
    fn marginals_of_an_empty_domain_compute_no_terms() -> Result<()> {
        let (empty, one, huge) = (FinObj::new(0), FinObj::new(1), FinObj::new(usize::MAX));

        let joint = Kernel::<Exact>::new(empty.clone(), one.tensor(&huge)?, Vec::new())?;
        let expected = Kernel::new(empty.clone(), one.clone(), Vec::new())?;
        let got = joint.marginal_fst(&one, &huge);
        assert!(
            got.as_ref().is_ok_and(|kernel| *kernel == expected),
            "marginal_fst summing a factor of usize::MAX: expected {expected:?}, observed {got:?}"
        );

        let joint = Kernel::<Exact>::new(empty.clone(), huge.tensor(&one)?, Vec::new())?;
        let expected = Kernel::new(empty, one.clone(), Vec::new())?;
        let got = joint.marginal_snd(&huge, &one);
        assert!(
            got.as_ref().is_ok_and(|kernel| *kernel == expected),
            "marginal_snd summing a factor of usize::MAX: expected {expected:?}, observed {got:?}"
        );
        Ok(())
    }

    #[test]
    fn is_deterministic_at_the_fixtures() -> Result<()> {
        for (name, kernel, expected) in [
            ("psi_t", psi_t()?, false),
            ("s", s()?, false),
            ("d", d()?, true),
            ("e", e()?, true),
        ] {
            let observed = is_deterministic(&kernel)?;
            assert_eq!(
                observed,
                expected,
                "is_deterministic({name}) on {}: expected {expected}, observed {observed}",
                show(&kernel)
            );
        }
        Ok(())
    }

    #[test]
    fn is_deterministic_on_an_empty_domain_builds_no_copy() -> Result<()> {
        let empty = Kernel::<Exact>::new(FinObj::new(0), FinObj::new(1 << 32), Vec::new())?;
        let got = is_deterministic(&empty);
        assert!(
            matches!(got, Ok(true)),
            "expected Ok(true) on ∅ → 2^32 elements, observed {got:?}"
        );
        Ok(())
    }

    #[test]
    fn is_independent_rejects_a_wrong_split() -> Result<()> {
        let (w, sp, t) = (obj_w()?, obj_s()?, obj_t()?);
        let joint = f()?;
        let cod = w.tensor(&sp)?;
        for (route, x, y) in [
            ("factors swapped", &sp, &w),
            ("mismatch only on snd", &w, &t),
        ] {
            let got = is_independent(&joint, x, y);
            assert!(
                matches!(&got, Err(Error::NotATensor { codomain, fst, snd })
                    if *codomain == cod && fst == x && snd == y),
                "is_independent(f), {route}: expected NotATensor {{ codomain: {cod:?}, fst: {x:?}, snd: {y:?} }}, observed {got:?}"
            );
        }
        Ok(())
    }

    #[test]
    fn is_independent_reads_every_input() -> Result<()> {
        let (sp, t) = (obj_s()?, obj_t()?);
        let cod = t.tensor(&sp)?;
        let quarters: &[Exact] = &[r(1, 4), r(1, 4), r(1, 4), r(1, 4)];
        let product: &[Exact] = &[r(1, 6), r(1, 2), r(1, 12), r(1, 4)];
        let diagonal: &[Exact] = &[r(1, 2), r(0, 1), r(0, 1), r(1, 2)];
        for (name, columns, expected) in [
            ("product at both inputs", [quarters, product], true),
            ("product at input 0 only", [quarters, diagonal], false),
        ] {
            let kernel = lit(sp.clone(), cod.clone(), &columns)?;
            let observed = is_independent(&kernel, &t, &sp)?;
            assert_eq!(
                observed,
                expected,
                "is_independent({name}) on {}: expected {expected}, observed {observed}",
                show(&kernel)
            );
        }
        Ok(())
    }

    #[test]
    fn is_independent_reads_every_output() -> Result<()> {
        let cod = obj_w()?.tensor(&obj_s()?)?;
        for (name, weights, expected) in [
            (
                "product of (1/2, 1/4, 1/4) and (1/2, 1/2)",
                vec![r(1, 4), r(1, 4), r(1, 8), r(1, 8), r(1, 8), r(1, 8)],
                true,
            ),
            (
                "same marginals, factors at (sunny, on) only",
                vec![r(1, 4), r(1, 4), r(1, 4), r(0, 1), r(0, 1), r(1, 4)],
                false,
            ),
        ] {
            let state = Kernel::state(cod.clone(), weights)?;
            let observed = is_independent(&state, &obj_w()?, &obj_s()?)?;
            assert_eq!(
                observed,
                expected,
                "is_independent({name}) on {}: expected {expected}, observed {observed}",
                show(&state)
            );
        }
        Ok(())
    }

    #[test]
    fn cond_indep_form_rejects_misaligned_domains() -> Result<()> {
        let (sp, t) = (obj_s()?, obj_t()?);
        let (ts, st) = (t.tensor(&sp)?, sp.tensor(&t)?);
        let ssst = sp.tensor(&st)?;
        let g = h()?;
        for (route, h_dom, k_dom, codomain, domain) in [
            ("h on W ⊗ A", &st, &st, &ts, &st),
            ("k on A ⊗ W", &ts, &ts, &st, &ts),
            ("split shifted from h to k", &t, &ssst, &ts, &t),
        ] {
            let got = cond_indep_form(&g, &Kernel::del(h_dom)?, &Kernel::del(k_dom)?);
            assert!(
                matches!(&got, Err(Error::NotComposable { codomain: cod, domain: dom })
                    if cod == codomain && dom == domain),
                "cond_indep_form(h, del, del), {route}: expected NotComposable {{ codomain: {codomain:?}, domain: {domain:?} }}, observed {got:?}"
            );
        }
        Ok(())
    }

    /// `(on, off)` weights of the first `k` terms against the rest.
    fn split_weight(k: usize) -> Result<Kernel<Exact>> {
        let denominator = i64::try_from(k + 1).expect("invariant: test sizes fit in i64");
        Kernel::state(obj_s()?, vec![closed_form(k), r(1, denominator)])
    }

    #[test]
    fn composites_match_closed_forms_across_threshold() -> Result<()> {
        for m in [PAR_THRESHOLD - 1, PAR_THRESHOLD, 3 * PAR_THRESHOLD + 7] {
            let k = m / 2;
            let middle = FinObj::new(m);
            let denominator = i64::try_from(m).expect("invariant: test sizes fit in i64");
            let mut weights = telescoping(m - 1);
            weights.push(r(1, denominator));
            let expected = split_weight(k)?;

            let outputs: Vec<usize> = (0..m).map(|y| usize::from(y >= k)).collect();
            let f = Kernel::state(middle.clone(), weights.clone())?;
            let g = points(middle.clone(), obj_s()?, &outputs)?;
            assert_kernel(
                &format!("compose over {m} terms"),
                &f.compose(&g)?,
                &expected,
            );

            let zero = Exact::zero();
            let on_off: Vec<(Exact, Exact)> = weights
                .into_iter()
                .enumerate()
                .map(|(y, weight)| {
                    if y < k {
                        (weight, zero.clone())
                    } else {
                        (zero.clone(), weight)
                    }
                })
                .collect();
            let by_s: Vec<Exact> = on_off
                .iter()
                .map(|(on, _)| on.clone())
                .chain(on_off.iter().map(|(_, off)| off.clone()))
                .collect();
            let by_m: Vec<Exact> = on_off
                .iter()
                .flat_map(|(on, off)| [on.clone(), off.clone()])
                .collect();
            let s_then_m = Kernel::state(obj_s()?.tensor(&middle)?, by_s)?;
            let m_then_s = Kernel::state(middle.tensor(&obj_s()?)?, by_m)?;
            assert_kernel(
                &format!("marginal_fst over {m} terms"),
                &s_then_m.marginal_fst(&obj_s()?, &middle)?,
                &expected,
            );
            assert_kernel(
                &format!("marginal_snd over {m} terms"),
                &m_then_s.marginal_snd(&middle, &obj_s()?)?,
                &expected,
            );
        }
        Ok(())
    }

    #[test]
    fn oversized_kernels_are_too_large_errors() {
        let n = 1_usize << 31;
        let got = Kernel::<Exact>::identity(&FinObj::new(n));
        assert!(
            matches!(got, Err(Error::TooLarge { fst, snd, source: Some(_) }) if fst == n && snd == n),
            "expected TooLarge with a source on 2^62 entries past isize::MAX bytes, observed {got:?}"
        );
        let n = 1_usize << 46;
        let got = Kernel::<Exact>::del(&FinObj::new(n));
        assert!(
            matches!(got, Err(Error::TooLarge { fst, snd: 1, source: Some(_) }) if fst == n),
            "expected TooLarge with a source from the allocator on 2^46 entries, observed {got:?}"
        );
        let n = 1_usize << 32;
        let got = Kernel::<Exact>::copy(&FinObj::new(n));
        assert!(
            matches!(got, Err(Error::TooLarge { fst, snd, source: None }) if fst == n && snd == n),
            "expected TooLarge from an overflowing n·n with no source, observed {got:?}"
        );
        let m = 1_usize << 33;
        let got = Kernel::<Exact>::swap(&FinObj::new(n), &FinObj::new(m));
        assert!(
            matches!(got, Err(Error::TooLarge { fst, snd, source: None }) if fst == n && snd == m),
            "expected TooLarge from an overflowing n·m with fst = n, snd = m and no source, observed {got:?}"
        );
    }

    #[test]
    fn too_large_reports_its_source_through_the_error_trait() {
        let reservation = Kernel::<Exact>::identity(&FinObj::new(1_usize << 31));
        let source = reservation.as_ref().err().and_then(StdError::source);
        assert!(
            source.is_some_and(|source| source.is::<TryReserveError>()),
            "expected a TryReserveError source on a failed reservation, observed {source:?}"
        );
        let overflow = FinObj::new(usize::MAX).tensor(&FinObj::new(2));
        let source = overflow.as_ref().err().and_then(StdError::source);
        assert!(
            source.is_none(),
            "expected no source on an overflowing product, observed {source:?}"
        );
    }

    /// The observations of the post's table as `(W, H, T3, sprinkler on)`, each
    /// component an index into its object.
    const TABLE: [(usize, usize, usize, bool); 7] = [
        (0, 1, 1, false),
        (0, 0, 0, true),
        (1, 0, 0, true),
        (1, 1, 1, true),
        (2, 1, 2, false),
        (1, 0, 2, true),
        (0, 1, 2, false),
    ];

    fn climate_index(w: usize, h: usize, t: usize) -> usize {
        w * 6 + h * 3 + t
    }

    #[test]
    fn sprinkler_eq_9_is_exact_at_either_fill() -> Result<()> {
        let hum = FinObj::labeled(vec!["dry".to_owned(), "humid".to_owned()])?;
        let t3 = FinObj::labeled(vec!["hot".to_owned(), "mild".to_owned(), "cold".to_owned()])?;
        let climate = obj_w()?.tensor(&hum)?.tensor(&t3)?;

        let mut atoms = vec![Exact::zero(); climate.card()];
        atoms[climate_index(0, 0, 0)] = r(1, 5);
        atoms[climate_index(2, 1, 2)] = r(3, 10);
        atoms[climate_index(1, 1, 1)] = r(3, 10);
        atoms[climate_index(1, 0, 0)] = r(1, 5);
        let p = Kernel::state(climate.clone(), atoms)?;

        let expected = Kernel::state(obj_s()?, vec![r(7, 10), r(3, 10)])?;
        for fill_on in [false, true] {
            let mut on = vec![fill_on; climate.card()];
            for (w, h, t, row_on) in TABLE {
                on[climate_index(w, h, t)] = row_on;
            }
            let outputs: Vec<usize> = on.iter().map(|&row_on| usize::from(!row_on)).collect();
            let f = points(climate.clone(), obj_s()?, &outputs)?;
            assert_kernel(
                &format!("f ∘ p with fill_on = {fill_on}"),
                &p.compose(&f)?,
                &expected,
            );
        }
        Ok(())
    }
}

/// `c ⊗ₘ s : T ⊗ W → W ⊗ S`, the literal.
fn c_tensor_s() -> peluang::error::Result<peluang::kernel::Kernel<peluang::prob::Exact>> {
    use crate::fixtures::{lit, obj_s, obj_t, obj_w, r};

    lit(
        obj_t()?.tensor(&obj_w()?)?,
        obj_w()?.tensor(&obj_s()?)?,
        &[
            &[r(1, 6), r(1, 3), r(1, 6), r(1, 3), r(0, 1), r(0, 1)],
            &[r(1, 2), r(0, 1), r(1, 2), r(0, 1), r(0, 1), r(0, 1)],
            &[r(0, 1), r(1, 2), r(0, 1), r(1, 2), r(0, 1), r(0, 1)],
            &[r(0, 1), r(0, 1), r(1, 12), r(1, 6), r(1, 4), r(1, 2)],
            &[r(0, 1), r(0, 1), r(1, 4), r(0, 1), r(3, 4), r(0, 1)],
            &[r(0, 1), r(0, 1), r(0, 1), r(1, 4), r(0, 1), r(3, 4)],
        ],
    )
}

#[cfg(feature = "f64-prob")]
mod float_kernels {
    use crate::c_tensor_s;
    use crate::fixtures::{c, d, f, h, hot, k, obj_p, obj_s, obj_t, obj_w, psi_t, s};
    use num_traits::ToPrimitive;
    use peluang::almost_sure::as_equal;
    use peluang::bayes::{bayesian_inverse, is_bayesian_inverse};
    use peluang::deterministic::{is_as_deterministic, is_deterministic};
    use peluang::error::{Error, Result};
    use peluang::finset::FinObj;
    use peluang::independence::is_independent;
    use peluang::kernel::Kernel;
    use peluang::markov::{Compose, Tensor};
    use peluang::prob::{Exact, F64_TOLERANCE};

    fn column(weights: Vec<f64>) -> Result<Kernel<f64>> {
        Kernel::new(FinObj::new(1), FinObj::new(weights.len()), weights)
    }

    /// `k` with each weight of each `Kernel::column` converted to `f64`,
    /// through `Kernel::new`.
    fn floats(k: &Kernel<Exact>) -> Result<Kernel<f64>> {
        let data: Vec<f64> = (0..k.domain().card())
            .filter_map(|x| k.column(x))
            .flatten()
            .map(|weight| {
                weight
                    .to_f64()
                    .expect("invariant: fixture weights are finite")
            })
            .collect();
        Kernel::new(k.domain().clone(), k.codomain().clone(), data)
    }

    #[track_caller]
    fn assert_approx(side: &str, observed: &Kernel<f64>, expected: &Kernel<f64>) {
        assert!(
            observed.approx_eq(expected),
            "{side}: expected {expected:?} within {F64_TOLERANCE}, observed {observed:?}"
        );
    }

    #[test]
    fn approx_eq_holds_within_tolerance_only() -> Result<()> {
        let base = column(vec![0.5, 0.5])?;
        let within = column(vec![0.5 + F64_TOLERANCE / 4.0, 0.5 - F64_TOLERANCE / 4.0])?;
        let beyond = column(vec![0.5 + 2.0 * F64_TOLERANCE, 0.5 - 2.0 * F64_TOLERANCE])?;
        assert_ne!(base, within, "expected the pair to differ as values");
        assert_approx("within tolerance", &within, &base);
        let observed = beyond.approx_eq(&base);
        assert!(
            !observed,
            "expected false beyond F64_TOLERANCE, observed {observed}"
        );
        Ok(())
    }

    #[test]
    fn compose_is_chapman_kolmogorov() -> Result<()> {
        assert_approx(
            "c ≫ s",
            &floats(&c()?)?.compose(&floats(&s()?)?)?,
            &floats(&h()?)?,
        );
        Ok(())
    }

    #[test]
    fn tensor_has_the_first_factor_major() -> Result<()> {
        assert_approx(
            "c ⊗ₘ s",
            &floats(&c()?)?.tensor(&floats(&s()?)?)?,
            &floats(&c_tensor_s()?)?,
        );
        Ok(())
    }

    #[test]
    fn marginals_of_the_joint() -> Result<()> {
        let (w, sp) = (obj_w()?, obj_s()?);
        let joint = floats(&f()?)?;
        assert_approx(
            "marginal_fst",
            &joint.marginal_fst(&w, &sp)?,
            &floats(&c()?)?,
        );
        assert_approx(
            "marginal_snd",
            &joint.marginal_snd(&w, &sp)?,
            &floats(&h()?)?,
        );
        Ok(())
    }

    #[test]
    fn is_deterministic_under_approx_eq() -> Result<()> {
        let tilt = F64_TOLERANCE / 4.0;
        let near = Kernel::new(obj_s()?, obj_t()?, vec![1.0 - tilt, tilt, 0.0, 1.0])?;
        for (name, kernel, expected) in [
            ("d", floats(&d()?)?, true),
            ("within tolerance of a function", near, true),
            ("s", floats(&s()?)?, false),
        ] {
            let observed = is_deterministic(&kernel)?;
            assert_eq!(
                observed, expected,
                "is_deterministic({name}) on {kernel:?}: expected {expected}, observed {observed}"
            );
        }
        Ok(())
    }

    #[test]
    fn is_independent_under_approx_eq() -> Result<()> {
        let tp = obj_t()?.tensor(&obj_p()?)?;
        let tilted =
            |tilt: f64| Kernel::state(tp.clone(), vec![0.25 + tilt, 0.25 - tilt, 0.25, 0.25]);
        let (within, beyond) = (F64_TOLERANCE / 4.0, 4.0 * F64_TOLERANCE);
        let two_inputs = Kernel::new(
            FinObj::new(2),
            tp.clone(),
            vec![
                0.25 + within,
                0.25 - within,
                0.25,
                0.25,
                0.1 + beyond,
                0.4 - beyond,
                0.1,
                0.4,
            ],
        )?;
        for (name, kernel, expected) in [
            ("uniform product", tilted(0.0)?, true),
            ("tilted by F64_TOLERANCE / 4", tilted(within)?, true),
            ("tilted by 4 · F64_TOLERANCE", tilted(beyond)?, false),
            (
                "input 0 tilted by F64_TOLERANCE / 4, input 1 by 4 · F64_TOLERANCE",
                two_inputs,
                false,
            ),
        ] {
            let observed = is_independent(&kernel, &obj_t()?, &obj_p()?)?;
            assert_eq!(
                observed, expected,
                "is_independent({name}) on {kernel:?}: expected {expected}, observed {observed}"
            );
        }
        Ok(())
    }

    #[track_caller]
    fn assert_flag(call: &str, got: &Result<bool>, expected: bool) {
        assert!(
            matches!(got, Ok(observed) if *observed == expected),
            "{call}: expected Ok({expected}), observed {got:?}"
        );
    }

    #[track_caller]
    fn assert_inverse(call: &str, got: &Result<Kernel<f64>>, expected: &Kernel<f64>) {
        assert!(
            matches!(got, Ok(observed) if observed.approx_eq(expected)),
            "{call}: expected Ok({expected:?}) within {F64_TOLERANCE}, observed {got:?}"
        );
    }

    #[test]
    fn bayesian_inverse_under_approx_eq() -> Result<()> {
        let (w, t, c) = (obj_w()?, obj_t()?, floats(&c()?)?);
        let third = 1.0 / 3.0;
        let plain = Kernel::new(
            w.clone(),
            t.clone(),
            vec![1.0, 0.0, third, 1.0 - third, 0.0, 1.0],
        )?;
        let filled = Kernel::new(w, t, vec![1.0, 0.0, 1.0, 0.0, 0.5, 0.5])?;
        for (name, p, expected) in [
            ("psi_t", floats(&psi_t()?)?, plain),
            ("hot, no mass at rainy", floats(&hot()?)?, filled),
        ] {
            assert_inverse(
                &format!("bayesian_inverse({name}, c)"),
                &bayesian_inverse(&p, &c),
                &expected,
            );
        }
        Ok(())
    }

    #[test]
    fn is_bayesian_inverse_under_approx_eq() -> Result<()> {
        let (psi_t, c) = (floats(&psi_t()?)?, floats(&c()?)?);
        let (third, tilt) = (1.0 / 3.0, F64_TOLERANCE / 4.0);
        let inverse = |hot_at_cloudy: f64| {
            Kernel::new(
                obj_w()?,
                obj_t()?,
                vec![1.0, 0.0, hot_at_cloudy, 1.0 - hot_at_cloudy, 0.0, 1.0],
            )
        };
        for (name, g, expected) in [
            ("cloudy (1/3, 2/3)", inverse(third)?, true),
            (
                "cloudy tilted by F64_TOLERANCE / 4",
                inverse(third + tilt)?,
                true,
            ),
            ("cloudy (2/3, 1/3)", inverse(1.0 - third)?, false),
        ] {
            assert_flag(
                &format!("is_bayesian_inverse(psi_t, c, {name}) on {g:?}"),
                &is_bayesian_inverse(&psi_t, &c, &g),
                expected,
            );
        }
        Ok(())
    }

    /// The expected values are those of a measured run.
    #[test]
    fn is_bayesian_inverse_passes_two_kernels_that_fail_as_equal_measured() -> Result<()> {
        let two = FinObj::new(2);
        let p = Kernel::state(two.clone(), vec![1.0 - 1e-13, 1e-13])?;
        let id = Kernel::<f64>::identity(&two)?;
        let constant = Kernel::<f64>::from_fn(two.clone(), two, |_| 0)?;
        assert_flag(
            "measured: is_bayesian_inverse((1 - 1e-13, 1e-13), 𝟙, 𝟙)",
            &is_bayesian_inverse(&p, &id, &id),
            true,
        );
        assert_flag(
            "measured: is_bayesian_inverse((1 - 1e-13, 1e-13), 𝟙, constant 0)",
            &is_bayesian_inverse(&p, &id, &constant),
            true,
        );
        assert_flag(
            "measured: as_equal((1 - 1e-13, 1e-13) ≫ 𝟙, 𝟙, constant 0)",
            &as_equal(&p.compose(&id)?, &id, &constant),
            false,
        );
        Ok(())
    }

    /// The expected value is that of a measured run: the joint weight
    /// `1e-200 * 1e-200` at `(y0, x0)` is `0.0`.
    #[test]
    fn bayesian_inverse_fills_an_underflowed_column_uniformly_measured() -> Result<()> {
        let two = FinObj::new(2);
        let p = Kernel::state(two.clone(), vec![1e-200, 1.0])?;
        let f = Kernel::new(two.clone(), two.clone(), vec![1e-200, 1.0, 0.0, 1.0])?;
        let expected = Kernel::new(two.clone(), two, vec![0.5, 0.5, 1e-200, 1.0])?;
        assert_inverse(
            "measured: bayesian_inverse((1e-200, 1), x0 → (1e-200, 1), x1 → (0, 1))",
            &bayesian_inverse(&p, &f),
            &expected,
        );
        Ok(())
    }

    /// The expected values of the last two cases are those of a measured run.
    /// In the fourth case the weight `1e-200` of `tiny` at `x1` is below
    /// `F64_TOLERANCE` and `!= 0.0`, so `x1` counts as reached. In the fifth
    /// case the weight `1e-200 * 1e-200` of `under` at `x1` is `0.0`, so `x1`
    /// counts as unreached.
    #[test]
    fn is_as_deterministic_under_approx_eq() -> Result<()> {
        let (two, tilt) = (FinObj::new(2), F64_TOLERANCE / 4.0);
        let k = floats(&k()?)?;
        let near = Kernel::new(two.clone(), two.clone(), vec![1.0 - tilt, tilt, 0.5, 0.5])?;
        let tiny = Kernel::state(two.clone(), vec![1.0, 1e-200])?;
        let step = Kernel::new(
            two.clone(),
            two.clone(),
            vec![1.0, 0.0, 1.0 - 1e-200, 1e-200],
        )?;
        let under = tiny.compose(&step)?;
        assert_eq!(
            under.column(0),
            Some(&[1.0, 0.0][..]),
            "measured: expected (1, 1e-200) ≫ step = (1, 0), observed on the left"
        );
        for (name, p, f, expected) in [
            ("hot, k", floats(&hot()?)?, &k, true),
            ("psi_t, k", floats(&psi_t()?)?, &k, false),
            (
                "(1, 0), x0 within F64_TOLERANCE / 4 of a function",
                Kernel::state(two.clone(), vec![1.0, 0.0])?,
                &near,
                true,
            ),
            ("measured: (1, 1e-200), x1 → (1/2, 1/2)", tiny, &near, false),
            (
                "measured: (1, 1e-200) ≫ step, x1 → (1/2, 1/2)",
                under,
                &near,
                true,
            ),
        ] {
            assert_flag(
                &format!("is_as_deterministic({name}) on p = {p:?}, f = {f:?}"),
                &is_as_deterministic(&p, f),
                expected,
            );
        }
        Ok(())
    }

    #[test]
    fn new_rejects_nan_and_infinite_entries() {
        let got = column(vec![0.5, f64::NAN]);
        assert!(
            matches!(
                got,
                Err(Error::NegativeWeight {
                    input: 0,
                    output: 1
                })
            ),
            "expected NegativeWeight at the NaN entry, observed {got:?}"
        );
        let got = column(vec![f64::INFINITY, 0.0]);
        assert!(
            matches!(got, Err(Error::NotNormalized { input: 0 })),
            "expected NotNormalized on an infinite entry, observed {got:?}"
        );
    }

    #[test]
    fn new_accepts_a_column_within_tolerance() {
        let within = vec![0.5, 0.5 + F64_TOLERANCE / 2.0];
        let got = column(within);
        assert!(
            got.is_ok(),
            "expected Ok within F64_TOLERANCE of 1, observed {got:?}"
        );
        let beyond = vec![0.5, 0.5 + 2.0 * F64_TOLERANCE];
        let got = column(beyond);
        assert!(
            matches!(got, Err(Error::NotNormalized { input: 0 })),
            "expected NotNormalized beyond F64_TOLERANCE of 1, observed {got:?}"
        );
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
