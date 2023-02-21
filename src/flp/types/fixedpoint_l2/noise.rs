//! Implementation of a sampler from the Discrete Gaussian Distribution.
//!
//! Follows
//!     Clément Canonne, Gautam Kamath, Thomas Steinke. The Discrete Gaussian for Differential Privacy. 2020.
//!     https://arxiv.org/abs/2004.00010

// Copyright (c) 2022 President and Fellows of Harvard College
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
//
// This file incorporates work covered by the following copyright and
// permission notice:
//
//   Copyright 2020 Thomas Steinke
//
//   Licensed under the Apache License, Version 2.0 (the "License");
//   you may not use this file except in compliance with the License.
//   You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in writing, software
//   distributed under the License is distributed on an "AS IS" BASIS,
//   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//   See the License for the specific language governing permissions and
//   limitations under the License.

//   The following code is adapted from the opendp implementation to reduce dependencies:
//       https://github.com/opendp/opendp/blob/main/rust/src/traits/samplers/cks20

use std::convert::TryInto;
use std::error;

type RandResult<R> = Result<R, Box<dyn error::Error>>;

/// Sample from the discrete uniform distribution over u64.
///
/// `sample_uniform_u64` either returns `Err(e)`, due to a lack of system entropy,
/// or `Ok(out)`, where `out` is distributed uniformly over u64.
pub(crate) fn sample_uniform_u64() -> RandResult<u64> {
    let mut buffer = [0; core::mem::size_of::<u64>()];
    getrandom::getrandom(&mut buffer)?;
    Ok(u64::from_be_bytes(buffer))
}

/// Sample from the discrete uniform distribution on $[0, upper)$.
///
/// `sample_uniform_u64_below` either returns `Err(e)`, due to a lack of system entropy,
/// or `Ok(out)`, where `out` is distributed uniformly over $[0, upper)$.
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

/// Sample from the Bernoulli(n/d) distribution, where $n \leq d$.
///
/// `sample_bernoulli_frac` either returns `Err(e)`, due to a lack of system entropy,
/// or `Ok(out)`, where `out` is distributed as $Bernoulli(n/d)$.
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
    assert!(d > 0);
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

/// Sample from the geometric distribution with parameter 1 - exp(-n/d) (slow).
///
/// `sample_geometric_exp_slow` either returns `Err(e)` due to a lack of system entropy,
/// or `Ok(out)`, where `out` is distributed as $Geometric(1 - exp(-n/d))$.
fn sample_geometric_exp_slow(n: u64, d: u64) -> RandResult<u64> {
    assert!(d > 0);
    let mut k = 0;
    loop {
        if sample_bernoulli_exp(n, d)? {
            k += 1;
        } else {
            return Ok(k);
        }
    }
}

/// Sample from the geometric distribution  with parameter 1 - exp(-n/d) (fast).
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
        // prevent some overflows
        let num_abs = if d.pow(2) * t * y_abs >= n.pow(2) {
            d.pow(2) * t * y_abs - n.pow(2)
        } else {
            n.pow(2) - d.pow(2) * t * y_abs
        };
        if sample_bernoulli_exp(num_abs.pow(2), 2 * (t * n * d).pow(2))? {
            return Ok(y);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use statest::ks::*;
    use statrs::{
        distribution::{Normal, Uniform, Univariate},
        function::erf,
    };

    /// see if `sampler` likely samples from `dist` using the Kolmogorov–Smirnov test
    fn kolmogorov_smirnov<F: Fn() -> f64, T: Univariate<f64, f64>>(sampler: F, dist: T) -> bool {
        let t_vec = (0..4000).map(|_| sampler()).collect::<Vec<f64>>();
        t_vec.ks1(&dist, 0.05)
    }

    pub fn test_proportion_parameters<FS: Fn() -> f64>(
        sampler: FS,
        p_pop: f64,
        err_margin: f64,
    ) -> bool {
        /// returns z-statistic that satisfies p == ∫P(x)dx over (-∞, z),
        ///     where P is the standard normal distribution
        pub fn normal_cdf_inverse(p: f64) -> f64 {
            std::f64::consts::SQRT_2 * erf::erfc_inv(2.0 * p)
        }

        let z_stat = normal_cdf_inverse(0.000005).abs();

        // derived sample size necessary to conduct the test
        let n = (p_pop * (1. - p_pop) * (z_stat / err_margin).powf(2.)).ceil();

        // confidence interval for the mean
        let abs_p_tol = z_stat * (p_pop * (1. - p_pop) / n).sqrt(); // almost the same as err_margin

        // take n samples from the distribution, compute average as empirical proportion
        let p_emp = (0..n as i64).map(|_| sampler()).sum::<f64>() / n;

        (p_emp - p_pop).abs() < abs_p_tol
    }

    #[test]
    fn test_gauss() {
        [200, 300, 400, 2000, 10000].iter().for_each(|p| {
            let sampler = || sample_discrete_gaussian(*p, 1).unwrap() as f64;
            assert!(
                kolmogorov_smirnov(sampler, Normal::new(0., *p as f64).unwrap()),
                "Empirical test of discrete Gaussian({:?}) sampler failed.",
                p
            );
        })
    }

    #[test]
    fn test_bernoulli() {
        [2, 5, 7, 9].iter().for_each(|p| {
            let sampler = || {
                if sample_bernoulli_frac(1, *p).unwrap() {
                    1.
                } else {
                    0.
                }
            };
            assert!(
                test_proportion_parameters(sampler, 1. / (*p as f64), 1. / (100. * (*p as f64))),
                "Empirical evaluation of the Bernoulli(1/{:?}) distribution failed",
                p
            )
        })
    }
    
    #[test]
    fn test_samplers() {
        // compute sample mean and variance
        fn sample_stat<F: Fn() -> f64>(sampler: F, n: u64) -> (f64, f64, f64, f64) {
            let samples = (1..n).map(|_| sampler());
            let mean = samples.clone().sum::<f64>() / n as f64;
            let var = samples
                .clone()
                .map(|s| (s - mean) * (s - mean))
                .sum::<f64>()
                / n as f64;
            let skew = samples.clone().map(|s| (s - mean).powf(3.)).sum::<f64>()
                / (var.sqrt().powf(3.) * (n as f64));
            let kurt = samples.map(|s| (s - mean).powf(4.)).sum::<f64>()
                / (var.sqrt().powf(4.) * (n as f64));

            return (mean, var, skew, kurt);
        }

        let n = 10000;

        println!(
            "uniform (should be ~4.5, ~8.25, ~0, ~2.22): {:?}\n
             bernoulli (should be ~0.1, ~0.09, ~2.66, ~8.111): {:?}\n
             exp bernoulli <1 (should be ~0.904, ~0.086, ~-2.76, ~8.61): {:?}\n
             exp bernoulli (should be ~0.22, ~0.173, 1.33, ~2.76): {:?}\n
             exp geom (should be ~9.5, ~99.91, ~9, ~2): {:?}\n
             laplace (should be ~0, ~800, ~0, ~6): {:?}\n
             gauss(should be ~0, ~400, ~0, ~3): {:?}\n",
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
    }

}
