//! Implementation a sampler from the Discrete Gaussian Distribution
use std::convert::TryInto;
use std::error;

type RandResult<R> = Result<R, Box<dyn error::Error>>;

pub(crate) fn sample_uniform_u64() -> RandResult<u64> {
    let mut buffer = [0; core::mem::size_of::<u64>()];
    getrandom::getrandom(&mut buffer)?;
    Ok(u64::from_be_bytes(buffer))
}

fn sample_uniform_u64_below(upper: u64) -> RandResult<u64> {
    // v % upper is unbiased for any v < MAX - MAX % upper, because
    // MAX - MAX % upper evenly folds into [0, upper) RAND_MAX/upper times
    loop {
        let v = sample_uniform_u64()?;
        if v <= u64::MAX - u64::MAX % upper {
            return Ok(v % upper);
        }
    }
}

fn sample_bernoulli_frac(n: u64, d: u64) -> RandResult<bool> {
    assert!(d > 0);
    assert!(n <= d);
    let s = sample_uniform_u64_below(d)?;
    return Ok(s < n);
}

/// Sample from the Bernoulli(exp(-(n/d))) distribution, where $n \leq d$.
///
/// `sample_bernoulli_exp1` either returns `Err(e)`, due to a lack of system entropy,
/// or `Ok(out)`, where `out` is distributed as $Bernoulli(exp(-(n/d)))$.
fn sample_bernoulli_exp1(n: u64, d: u64) -> RandResult<bool> {
    assert!(n <= d);
    let mut k = 1;
    loop {
        if sample_bernoulli_frac(n, d * k)? {
            k += 1; //TODO handle overflows, if we can't use exact arithmetics
        } else {
            return Ok(k % 2 != 0);
        }
    }
}

/// Sample from the Bernoulli(exp(-(n/d))) distribution.
///
/// `sample_bernoulli_exp` either returns `Err(e)` due to a lack of system entropy,
/// or `Ok(out)`, where `out` is distributed as $Bernoulli(exp(-(n/d)))$.
fn sample_bernoulli_exp(mut n: u64, d: u64) -> RandResult<bool> {
    assert!(d > 0);
    // Sample floor(n/d) independent Bernoulli(exp(-1))
    // If all are 1, return Bernoulli(exp(-((n/d)-floor(n/d))))
    while n > d {
        if sample_bernoulli_exp1(1, 1)? {
            n -= d;
        } else {
            return Ok(false);
        }
    }
    sample_bernoulli_exp1(n, d)
}

/// Sample from the geometric distribution (slow).
///
/// `sample_geometric_exp_slow` either returns `Err(e)` due to a lack of system entropy,
/// or `Ok(out)`, where `out` is distributed as $Geometric(1 - exp(-n/d))$.
fn sample_geometric_exp_slow(n: u64, d: u64) -> RandResult<u64> {
    assert!(d > 0);
    let mut k = 0;
    loop {
        if sample_bernoulli_exp(n, d)? {
            k += 1; //TODO handle overflows, if we can't use exact arithmetics
        } else {
            return Ok(k);
        }
    }
}

/// Sample from the geometric distribution (fast).
///
/// `sample_geometric_exp_fast` either returns `Err(e)` due to a lack of system entropy,
/// or `Ok(out)`, where `out` is distributed as $Geometric(1 - exp(-n/d))$.
fn sample_geometric_exp_fast(n: u64, d: u64) -> RandResult<u64> {
    assert!(d > 0);
    if n == 0 {
        return Ok(0);
    }

    let mut u = sample_uniform_u64_below(d)?;
    while !sample_bernoulli_exp(u, d)? {
        u = sample_uniform_u64_below(d)?;
    }
    let v2 = sample_geometric_exp_slow(1, 1)?;
    Ok((v2 * d + u) / n)
}

/// Sample from the discrete laplace distribution.
///
/// `sample_discrete_laplace` either returns `Err(e)` due to a lack of system entropy,
/// or `Ok(out)`, where `out` is distributed as $\mathcal{L}_\mathbb{Z}(0, n/d)$.
///
/// # Citation
/// * [CKS20 The Discrete Gaussian for Differential Privacy](https://arxiv.org/abs/2004.00010)
pub fn sample_discrete_laplace(n: u64, d: u64) -> RandResult<i64> {
    assert!(d > 0);
    if n == 0 {
        return Ok(0);
    }

    loop {
        let positive = sample_bernoulli_frac(1, 2)?; //TODO maybe get a distict standard bernoulli sampler
        let magnitude: i64 = sample_geometric_exp_fast(d, n)?.try_into()?;
        if positive || magnitude != 0 {
            return Ok(if positive { magnitude } else { -magnitude });
        }
    }
}

/// Sample from the discrete gaussian distribution.
///
/// `sample_discrete_gaussian` either returns `Err(e)` due to a lack of system entropy,
/// or `Ok(out)`, where `out` is distributed as $\mathcal{N}_\mathbb{Z}(0, (n/d)^2)$.
///
/// # Citation
/// * [CKS20 The Discrete Gaussian for Differential Privacy](https://arxiv.org/abs/2004.00010)
pub fn sample_discrete_gaussian(n: u64, d: u64) -> RandResult<i64> {
    assert!(d > 0);
    if n == 0 {
        return Ok(0);
    }
    let t = n / d + 1;
    loop {
        let y = sample_discrete_laplace(t, 1)?;
        let y_abs: u64 = y.abs().try_into()?;
        if sample_bernoulli_exp(
            (d.pow(2) * (d * t * y_abs).pow(2) + n.pow(4)) - 2 * t * y_abs * (n * d).pow(2), //TODO overflow danger
            2 * (t * n * d).pow(2),
        )? {
            return Ok(y);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn test_samplers() {
        // compute sample mean and variance
        fn sample_stat<F: Fn() -> f64>(sampler: F, n: u64) -> (f64, f64) {
            let samples = (1..n).map(|_| sampler());
            let mean = samples.clone().sum::<f64>() / n as f64;
            let var = samples.map(|s| (s - mean) * (s - mean)).sum::<f64>() / n as f64;

            return (mean, var);
        }

        let n = 10000;

        println!(
            "uniform (should be ~4.5, ~8.25): {:?}\n
             bernoulli (should be ~0.1, ~0.09): {:?}\n
             exp bernoulli <1 (should be ~0.904, ~0.086): {:?}\n
             exp bernoulli (should be ~0.22, ~0.173): {:?}\n
             exp geom (should be ~9.5, ~99.91): {:?}\n
             laplace (should be ~0, ~800): {:?}\n
             gauss(should be ~0, ~400): {:?}\n",
            sample_stat(|| sample_uniform_u64_below(10).unwrap() as f64, n),
            sample_stat(
                || if sample_bernoulli_frac(1, 10).unwrap() {
                    1.
                } else {
                    0.
                },
                n
            ),
            sample_stat(
                || if sample_bernoulli_exp1(1, 10).unwrap() {
                    1.
                } else {
                    0.
                },
                n
            ),
            sample_stat(
                || if sample_bernoulli_exp(3, 2).unwrap() {
                    1.
                } else {
                    0.
                },
                n
            ),
            sample_stat(|| sample_geometric_exp_fast(1, 10).unwrap() as f64, n),
            sample_stat(|| sample_discrete_laplace(20, 1).unwrap() as f64, n),
            sample_stat(|| sample_discrete_gaussian(20, 1).unwrap() as f64, n),
        );

        /*
        let samples: Vec<i64> = (1..n)
            .map(|_| sample_discrete_gaussian(20, 1).unwrap())
            .collect();
        println!("{:?}", samples);
        fs::write("foo.txt", format!("{:?}", samples)).expect("Unable to write file");
        */
    }
}
