// SPDX-License-Identifier: MPL-2.0

//! Differential privacy (DP) primitives.
use num_bigint::{BigInt, BigUint, TryFromBigIntError};
use num_rational::{BigRational, Ratio};

/// Errors propagated by methods in this module.
#[derive(Debug, thiserror::Error)]
pub enum DpError {
    /// Tried to use an infinite float as privacy parameter.
    #[error(
        "DP error: input value was not a valid privacy parameter. \
             It should to be a non-negative, finite float."
    )]
    InvalidFloat,

    /// Tried to construct a rational number with zero denominator.
    #[error("DP error: input denominator was zero.")]
    ZeroDenominator,

    /// Tried to convert BigInt into something incompatible.
    #[error("DP error: {0}")]
    BigIntConversion(#[from] TryFromBigIntError<BigInt>),
}

/// Positive finite precision rational number to represent DP and noise distribution parameters in
/// protocol messages and manipulate them without rounding errors.
#[derive(Clone, Debug)]
pub struct Rational(Ratio<BigUint>);

impl Rational {
    /// Construct a [`Rational`] number from numerator `n` and denominator `d`. Errors if denominator is zero.
    pub fn from_unsigned<T>(n: T, d: T) -> Result<Self, DpError>
    where
        T: Into<u128>,
    {
        // we don't want to expose BigUint in the public api, hence the Into<u128> bound
        let d = d.into();
        if d == 0 {
            Err(DpError::ZeroDenominator)
        } else {
            Ok(Rational(Ratio::<BigUint>::new(n.into().into(), d.into())))
        }
    }
}

impl TryFrom<f32> for Rational {
    type Error = DpError;
    fn try_from(value: f32) -> Result<Self, DpError> {
        match BigRational::from_float(value) {
            Some(y) => Ok(Rational(Ratio::<BigUint>::new(
                y.numer().clone().try_into()?,
                y.denom().clone().try_into()?,
            ))),
            None => Err(DpError::InvalidFloat)?,
        }
    }
}

/// Marker trait for differential privacy budgets (regardless of the specific accounting method).
pub trait DifferentialPrivacyBudget {}

/// Marker trait for differential privacy scalar noise distributions.
pub trait DifferentialPrivacyDistribution {}

/// Zero-concentrated differential privacy (ZCDP) budget as defined in [[BS16]].
///
/// [BS16]: https://arxiv.org/pdf/1605.02065.pdf
pub struct ZCdpBudget {
    epsilon: Ratio<BigUint>,
}

impl ZCdpBudget {
    /// Create a budget for parameter `epsilon`, using the notation from [[CKS20]] where `rho = (epsilon**2)/2`
    /// for a `rho`-ZCDP budget.
    ///
    /// [CKS20]: https://arxiv.org/pdf/2004.00010.pdf
    pub fn new(epsilon: Rational) -> Self {
        Self { epsilon: epsilon.0 }
    }
}

impl DifferentialPrivacyBudget for ZCdpBudget {}

/// Strategy to make aggregate results differentially private, e.g. by adding noise from a specific
/// type of distribution instantiated with a given DP budget.
pub trait DifferentialPrivacyStrategy {
    /// The type of the DP budget, i.e. the variant of differential privacy that can be obtained
    /// by using this strategy.
    type Budget: DifferentialPrivacyBudget;

    /// The distribution type this strategy will use to generate the noise.
    type Distribution: DifferentialPrivacyDistribution;

    /// The type the sensitivity used for privacy analysis has.
    type Sensitivity;

    /// Create a strategy from a differential privacy budget. The distribution created with
    /// `create_distribution` should provide the amount of privacy specified here.
    fn from_budget(b: Self::Budget) -> Self;

    /// Create a new distribution parametrized s.t. adding samples to the result of a function
    /// with sensitivity `s` will yield differential privacy of the DP variant given in the
    /// `Budget` type. Can error upon invalid parameters.
    fn create_distribution(&self, s: Self::Sensitivity) -> Result<Self::Distribution, DpError>;
}

pub mod distributions;

mod experimental_strategy;
