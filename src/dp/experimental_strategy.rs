//! Combinators for `DifferentialPrivacyStrategy`s.
///
/// This file implements the "product strategy" for two dp strategies,
/// this strategy takes a pair of budgets and a pair of sensitivities,
/// and produces a pair of distributions.
/// This should be useful for cases where a VDAF needs to sample from
/// two different distributions, for example two gaussians with different
/// standard deviations. See test case below.
use super::{
    DifferentialPrivacyBudget, DifferentialPrivacyDistribution, DifferentialPrivacyStrategy,
    DpError,
};

/// The privacy budget for the product strategy is a pair of budgets.
impl<A, B> DifferentialPrivacyBudget for (A, B)
where
    A: DifferentialPrivacyBudget,
    B: DifferentialPrivacyBudget,
{
}

/// Given two distributions, the independent product distribution of them is simply a tuple containing both.
/// Note we use a tuple struct for the combination of the following reasons:
///  - Pure tuples have no associated meaning of the intended kind of distribution.
///  - Using a struct field names makes for too cumbersome notation below.
struct ProductDpDistribution<A, B>(A, B);

impl<A, B> DifferentialPrivacyDistribution for ProductDpDistribution<A, B>
where
    A: DifferentialPrivacyDistribution,
    B: DifferentialPrivacyDistribution,
{
}

/// The product strategy for two strategies `A` and `B`.
struct ProductDpStrategy<A, B> {
    strategy: (A, B),
}

impl<A, B> DifferentialPrivacyStrategy for ProductDpStrategy<A, B>
where
    A: DifferentialPrivacyStrategy,
    B: DifferentialPrivacyStrategy,
{
    type Budget = (A::Budget, B::Budget);
    type Distribution = ProductDpDistribution<A::Distribution, B::Distribution>;
    type Sensitivity = (A::Sensitivity, B::Sensitivity);

    fn from_budget(b: Self::Budget) -> Self {
        Self {
            strategy: (A::from_budget(b.0), B::from_budget(b.1)),
        }
    }

    fn create_distribution(&self, s: Self::Sensitivity) -> Result<Self::Distribution, DpError> {
        let a = self.strategy.0.create_distribution(s.0)?;
        let b = self.strategy.1.create_distribution(s.1)?;
        Ok(ProductDpDistribution(a, b))
    }
}

/// This test shows how to create a strategy consisting of two gaussians.
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        dp::{distributions::ZCdpDiscreteGaussian, ZCdpBudget},
        vdaf::prg::{Seed, SeedStreamSha3},
    };
    use num_bigint::BigUint;
    use num_rational::Ratio;
    use rand::{distributions::Distribution, SeedableRng};

    #[test]
    fn test_double_discrete_gaussian() {
        // A type alias is enough to define the strategy from two `ZCdpDiscreteGaussian`s.
        type MyStrategy = ProductDpStrategy<ZCdpDiscreteGaussian, ZCdpDiscreteGaussian>;

        // Choosing budgets and sensitivities for both gaussians.
        let budget0 = ZCdpBudget {
            epsilon: Ratio::<BigUint>::from_integer(1u8.into()),
        };
        let budget1 = ZCdpBudget {
            epsilon: Ratio::<BigUint>::from_integer(2u8.into()),
        };
        let sensitivity0 = Ratio::<BigUint>::from_integer(10u8.into());
        let sensitivity1 = Ratio::<BigUint>::from_integer(20u8.into());

        // Creating the strategy and using it to get the (pair of) distributions
        // is done exactly the same way as for e.g. ZCdpDicreteGaussian.
        let strategy = MyStrategy::from_budget((budget0, budget1));
        let distribution = strategy
            .create_distribution((sensitivity0, sensitivity1))
            .unwrap();

        let mut rng = SeedStreamSha3::from_seed(Seed::from_bytes([0u8; 16]));

        // Now we can use both distributions to sample values.
        let sample0 = distribution.0.sample(&mut rng);
        let sample1 = distribution.1.sample(&mut rng);
        let sample2 = distribution.0.sample(&mut rng);
        let sample3 = distribution.1.sample(&mut rng);

        // And check that they are deterministic.
        assert_eq!(i8::try_from(sample0).unwrap(), 6);
        assert_eq!(i8::try_from(sample1).unwrap(), 19);
        assert_eq!(i8::try_from(sample2).unwrap(), 19);
        assert_eq!(i8::try_from(sample3).unwrap(), -4);
    }
}
