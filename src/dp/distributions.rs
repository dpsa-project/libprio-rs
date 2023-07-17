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

//! Implementation of a sampler from the Discrete Gaussian Distribution.
//!
//! Follows
//!     Clément Canonne, Gautam Kamath, Thomas Steinke. The Discrete Gaussian for Differential Privacy. 2020.
//!     <https://arxiv.org/pdf/2004.00010.pdf>

use num_bigint::{BigInt, BigUint, UniformBigUint};
use num_integer::Integer;
use num_iter::range_inclusive;
use num_rational::Ratio;
use num_traits::{One, Zero};
use rand::{distributions::uniform::UniformSampler, distributions::Distribution, Rng};

use super::{
    DifferentialPrivacyBudget, DifferentialPrivacyDistribution, DifferentialPrivacyStrategy,
    DpError, ZCdpBudget,
};

/// Sample from the Bernoulli(gamma) distribution, where $gamma /leq 1$.
///
/// `sample_bernoulli(gamma, rng)` returns numbers distributed as $Bernoulli(gamma)$.
/// using the given random number generator for base randomness. The procedure is as described
/// on page 30 of [[CKS20]].
///
/// [CKS20]: https://arxiv.org/pdf/2004.00010.pdf
fn sample_bernoulli<R: Rng + ?Sized>(gamma: &Ratio<BigUint>, rng: &mut R) -> bool {
    let d = gamma.denom();
    assert!(!d.is_zero());
    assert!(gamma <= &Ratio::<BigUint>::one());

    // sample uniform biguint in {1,...,d}
    // uses the implementation of rand::Uniform for num_bigint::BigUint
    let s = UniformBigUint::sample_single_inclusive(BigUint::one(), d, rng);

    s <= *gamma.numer()
}

/// Sample from the Bernoulli(exp(-gamma)) distribution.
///
/// `sample_bernoulli_exp(gamma, rng)` returns numbers distributed as $Bernoulli(exp(-gamma))$,
/// using the given random number generator for base randomness. Follows Algorithm 1 of [[CKS20]].
///
/// [CKS20]: https://arxiv.org/pdf/2004.00010.pdf
fn sample_bernoulli_exp<R: Rng + ?Sized>(gamma: &Ratio<BigUint>, rng: &mut R) -> bool {
    assert!(!gamma.denom().is_zero());

    if gamma <= &Ratio::<BigUint>::one() {
        let mut k = BigUint::one();
        loop {
            if sample_bernoulli(&(gamma / k.clone()), rng) {
                k += 1u8;
            } else {
                return k.is_odd();
            }
        }
    } else {
        for _ in range_inclusive(BigUint::one(), gamma.floor().to_integer()) {
            if !sample_bernoulli_exp(&Ratio::<BigUint>::one(), rng) {
                return false;
            }
        }
        sample_bernoulli_exp(&(gamma - gamma.floor()), rng)
    }
}

/// Sample from the geometric distribution  with parameter 1 - exp(-gamma).
///
/// `sample_geometric_exp(gamma, rng)` returns numbers distributed according to
/// $Geometric(1 - exp(-gamma))$, using the given random number generator for base randomness.
/// The code follows all but the last three lines of Algorithm 2 in [[CKS20]].
///
/// [CKS20]: https://arxiv.org/pdf/2004.00010.pdf
fn sample_geometric_exp<R: Rng + ?Sized>(gamma: &Ratio<BigUint>, rng: &mut R) -> BigUint {
    let (s, t) = (gamma.numer(), gamma.denom());
    assert!(!t.is_zero());
    if gamma.is_zero() {
        return BigUint::zero();
    }

    // sampler for uniform biguint in {0...t-1}
    // uses the implementation of rand::Uniform for num_bigint::BigUint
    let usampler = UniformBigUint::new(BigUint::zero(), t);
    let mut u = usampler.sample(rng);

    while !sample_bernoulli_exp(&Ratio::<BigUint>::new(u.clone(), t.clone()), rng) {
        u = usampler.sample(rng);
    }

    let mut v = BigUint::zero();
    loop {
        if sample_bernoulli_exp(&Ratio::<BigUint>::one(), rng) {
            v += 1u8;
        } else {
            break;
        }
    }

    // we do integer division, so the following term equals floor((u + t*v)/s)
    (u + t * v) / s
}

/// Sample from the discrete Laplace distribution.
///
/// `sample_discrete_laplace(scale, rng)` returns numbers distributed according to
/// $\mathcal{L}_\mathbb{Z}(0, scale)$, using the given random number generator for base randomness.
/// This follows Algorithm 2 of [[CKS20]], using a subfunction for geometric sampling.
///
/// [CKS20]: https://arxiv.org/pdf/2004.00010.pdf
fn sample_discrete_laplace<R: Rng + ?Sized>(scale: &Ratio<BigUint>, rng: &mut R) -> BigInt {
    let (s, t) = (scale.numer(), scale.denom());
    assert!(!t.is_zero());
    if s.is_zero() {
        return BigInt::zero();
    }

    loop {
        let negative = sample_bernoulli(&Ratio::<BigUint>::new(BigUint::one(), 2u8.into()), rng);
        let y: BigInt = sample_geometric_exp(&scale.recip(), rng).into();
        if negative && y.is_zero() {
            continue;
        } else {
            return if negative { -y } else { y };
        }
    }
}

/// Sample from the discrete Gaussian distribution.
///
/// `sample_discrete_gaussian(sigma, rng)` returns `BigInt` numbers distributed as
/// $\mathcal{N}_\mathbb{Z}(0, sigma^2)$, using the given random number generator for base
/// randomness. Follows Algorithm 3 from [[CKS20]].
///
/// [CKS20]: https://arxiv.org/pdf/2004.00010.pdf
fn sample_discrete_gaussian<R: Rng + ?Sized>(sigma: &Ratio<BigUint>, rng: &mut R) -> BigInt {
    assert!(!sigma.denom().is_zero());
    if sigma.is_zero() {
        return 0.into();
    }
    let t = sigma.floor() + BigUint::one();
    let sub = sigma.pow(2) / t.clone();
    loop {
        let y = sample_discrete_laplace(&t, rng);

        // absolute value without type conversion
        let y_abs: Ratio<BigUint> = BigUint::new(y.to_u32_digits().1).into();

        let fact = (sigma.pow(2) * BigUint::from(2u8)).recip();

        // unsigned subtraction-followed-by-square
        let prob: Ratio<BigUint> = if y_abs < sub.clone() {
            (sub.clone() - y_abs).pow(2) * fact
        } else {
            (y_abs - sub.clone()).pow(2) * fact
        };

        if sample_bernoulli_exp(&prob, rng) {
            return y;
        }
    }
}

/// Samples `BigInt` numbers according to the discrete Gaussian distribution with mean zero.
/// The distribution is defined over the integers, represented by arbitrary-precision integers.
/// The sampling procedure follows [[CKS20]].
///
/// [CKS20]: https://arxiv.org/pdf/2004.00010.pdf
#[derive(Clone, Debug)]
pub struct DiscreteGaussian {
    /// The standard deviation of the distribution.
    std: Ratio<BigUint>,
}

impl DiscreteGaussian {
    /// Create a new sampler from the Discrete Gaussian Distribution with the given
    /// standard deviation and mean zero. Errors if the input has denominator zero.
    pub fn new_checked(std: Ratio<BigUint>) -> Result<DiscreteGaussian, DpError> {
        if std.denom().is_zero() {
            return Err(DpError::ZeroDenominator());
        }
        Ok(DiscreteGaussian { std })
    }
}

impl Distribution<BigInt> for DiscreteGaussian {
    fn sample<R>(&self, rng: &mut R) -> BigInt
    where
        R: Rng + ?Sized,
    {
        sample_discrete_gaussian(&self.std, rng)
    }
}

impl DifferentialPrivacyDistribution for DiscreteGaussian {}

/// A DP strategy using the discrete gaussian distribution.
pub struct DiscreteGaussianDpStrategy<B>
where
    B: DifferentialPrivacyBudget,
{
    budget: B,
}

/// A DP strategy using the discrete gaussian distribution providing zero-concentrated DP.
pub type ZCdpDiscreteGaussian = DiscreteGaussianDpStrategy<ZCdpBudget>;

impl DifferentialPrivacyStrategy for DiscreteGaussianDpStrategy<ZCdpBudget> {
    type Budget = ZCdpBudget;
    type Distribution = DiscreteGaussian;
    type Sensitivity = Ratio<BigUint>;

    fn from_budget(budget: ZCdpBudget) -> DiscreteGaussianDpStrategy<ZCdpBudget> {
        DiscreteGaussianDpStrategy { budget }
    }

    /// Create a new sampler from the Discrete Gaussian Distribution with a standard
    /// deviation calibrated to provide `1/2 epsilon^2` zero-concentrated differential
    /// privacy when added to the result of an integer-valued function with sensitivity
    /// `sensitivity`, following Theorem 4 from [[CKS20]]
    ///
    /// [CKS20]: https://arxiv.org/pdf/2004.00010.pdf
    fn create_distribution(
        &self,
        sensitivity: Ratio<BigUint>,
    ) -> Result<DiscreteGaussian, DpError> {
        match DiscreteGaussian::new_checked(sensitivity / self.budget.epsilon.clone()) {
            Ok(d) => Ok(d),
            Err(e) => Err(e),
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::dp::Rational;
    use crate::vdaf::prg::{Seed, SeedStreamSha3};

    use num_bigint::BigUint;
    use rand::distributions::Distribution;
    use rand::SeedableRng;

    #[test]
    fn test_discrete_gaussian() {
        let sampler =
            DiscreteGaussian::new_checked(Ratio::<BigUint>::from_integer(BigUint::from(5u8)))
                .unwrap();

        // check samples are consistent
        let mut rng = SeedStreamSha3::from_seed(Seed::from_bytes([0u8; 16]));
        let samples: Vec<i8> = (0..10)
            .map(|_| i8::try_from(sampler.sample(&mut rng)).unwrap())
            .collect();
        let samples1: Vec<i8> = (0..10)
            .map(|_| i8::try_from(sampler.sample(&mut rng)).unwrap())
            .collect();
        assert_eq!(samples, vec!(3, 8, -7, 1, 2, 10, 8, -3, 0, 0));
        assert_eq!(samples1, vec!(-1, 2, 5, -1, -1, 3, 3, -1, -1, 3));
    }

    #[test]
    /// Make sure that the distribution created by `create_distribution`
    /// of `ZCdpDicreteGaussian` is the same one as manually creating one
    /// by using the constructor of `DiscreteGaussian` directly.
    fn test_zcdp_discrete_gaussian() {
        // sample from a manually created distribution
        let sampler1 =
            DiscreteGaussian::new_checked(Ratio::<BigUint>::from_integer(BigUint::from(4u8)))
                .unwrap();
        let mut rng = SeedStreamSha3::from_seed(Seed::from_bytes([0u8; 16]));
        let samples1: Vec<i8> = (0..10)
            .map(|_| i8::try_from(sampler1.sample(&mut rng)).unwrap())
            .collect();

        // sample from the distribution created by the `zcdp` strategy
        let zcdp = ZCdpDiscreteGaussian {
            budget: ZCdpBudget::new(Rational::try_from(0.25).unwrap()),
        };
        let sampler2 = zcdp
            .create_distribution(Ratio::<BigUint>::from_integer(1u8.into()))
            .unwrap();
        let mut rng2 = SeedStreamSha3::from_seed(Seed::from_bytes([0u8; 16]));
        let samples2: Vec<i8> = (0..10)
            .map(|_| i8::try_from(sampler2.sample(&mut rng2)).unwrap())
            .collect();

        assert_eq!(samples2, samples1);
    }
}
