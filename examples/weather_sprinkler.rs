//! The running example on `Exact` weights: the temperature state
//! `psi_t : I → T`, the weather kernel `c : T → W` and the sprinkler kernel
//! `s : W → S`, composed into the weather and sprinkler states and the joint
//! state on `W ⊗ S`, whose two marginals are printed beside the composites.
//! `main` returns an error when a marginal differs from its composite.

use peluang::error::Result;
use peluang::finset::FinObj;
use peluang::kernel::Kernel;
use peluang::markov::Compose;
use peluang::prob::Exact;

fn r(n: i64, d: i64) -> Exact {
    Exact::new(n.into(), d.into())
}

fn labels(names: &[&str]) -> Result<FinObj> {
    FinObj::labeled(names.iter().map(|&name| name.to_owned()).collect())
}

/// The names of the elements of `x`, first factor major, each joining one
/// label (or index) per factor with `·`.
fn element_names(x: &FinObj) -> Vec<String> {
    x.factors()
        .iter()
        .fold(vec![String::new()], |names, factor| {
            let own: Vec<String> = factor
                .labels()
                .map(<[String]>::to_vec)
                .unwrap_or_else(|| (0..factor.card()).map(|y| y.to_string()).collect());
            names
                .iter()
                .flat_map(|prefix| {
                    own.iter().map(move |label| {
                        if prefix.is_empty() {
                            label.clone()
                        } else {
                            format!("{prefix}·{label}")
                        }
                    })
                })
                .collect()
        })
}

/// `name`, then each column of `k` on its own line as `element: weight` pairs.
fn show(name: &str, k: &Kernel<Exact>) -> String {
    let outputs = element_names(k.codomain());
    let columns: Vec<String> = (0..k.domain().card())
        .filter_map(|x| k.column(x))
        .map(|column| {
            let pairs: Vec<String> = outputs
                .iter()
                .zip(column)
                .map(|(label, weight)| format!("{label}: {weight}"))
                .collect();
            format!("  {}", pairs.join(", "))
        })
        .collect();
    format!("{name}\n{}", columns.join("\n"))
}

fn main() -> std::result::Result<(), Box<dyn std::error::Error>> {
    let w = labels(&["sunny", "cloudy", "rainy"])?;
    let t = labels(&["hot", "cold"])?;
    let s_obj = labels(&["on", "off"])?;

    let psi_t = Kernel::state(t.clone(), vec![r(1, 5), r(4, 5)])?;
    let c = Kernel::new(
        t,
        w.clone(),
        vec![r(1, 2), r(1, 2), r(0, 1), r(0, 1), r(1, 4), r(3, 4)],
    )?;
    let s = Kernel::new(
        w.clone(),
        s_obj.clone(),
        vec![r(1, 3), r(2, 3), r(1, 1), r(0, 1), r(0, 1), r(1, 1)],
    )?;

    let weather = psi_t.compose(&c)?;
    let sprinkler = weather.compose(&s)?;
    let joint = weather
        .compose(&Kernel::copy(&w)?)?
        .compose(&Kernel::whisker_left(&w, &s)?)?;
    let weather_marginal = joint.marginal_fst(&w, &s_obj)?;
    let sprinkler_marginal = joint.marginal_snd(&w, &s_obj)?;

    println!("{}", show("psi_t ≫ c : I → W", &weather));
    println!("{}", show("psi_t ≫ c ≫ s : I → S", &sprinkler));
    println!("{}", show("psi_t ≫ c ≫ Δ[W] ≫ (W ◁ s) : I → W ⊗ S", &joint));
    println!(
        "{}",
        show("marginal_fst of the joint : I → W", &weather_marginal)
    );
    println!(
        "{}",
        show("marginal_snd of the joint : I → S", &sprinkler_marginal)
    );
    if weather_marginal != weather {
        return Err("marginal_fst of the joint differs from psi_t ≫ c".into());
    }
    if sprinkler_marginal != sprinkler {
        return Err("marginal_snd of the joint differs from psi_t ≫ c ≫ s".into());
    }
    println!("marginal_fst equals psi_t ≫ c; marginal_snd equals psi_t ≫ c ≫ s");
    Ok(())
}
