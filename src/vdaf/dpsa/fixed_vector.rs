
use fixed::traits::{Fixed, FixedUnsigned};

use crate::vdaf::dpsa::associated_field::*;
use crate::field::FieldElement;
use crate::flp::{FlpError, Gadget, Type};
use crate::flp::types::{truncate_call_check, valid_call_check};
use crate::polynomial::poly_range_check;
use crate::flp::gadgets::PolyEval;
use std::convert::{TryFrom, TryInto};


#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixedPointVecSum<T: FixedUnsigned + AssociatedField>
{
    bits_per_entry: usize,
    entries: usize,
    one: <<T as AssociatedField>::Field as FieldElement>::Integer,
    max_summand: <<T as AssociatedField>::Field as FieldElement>::Integer,
    range_checker: Vec<<T as AssociatedField>::Field>,
}

impl<T: FixedUnsigned + AssociatedField> FixedPointVecSum<T>
{
    pub fn new(entries: usize) -> Result<Self, FlpError>
    {

        // TODO: change this!
        let bits = (<T as Fixed>::INT_NBITS + <T as Fixed>::FRAC_NBITS).try_into().unwrap();

        let bits_int = <<T as AssociatedField>::Field as FieldElement>::Integer::try_from(bits).map_err(|err| {
            FlpError::Encode(format!(
                "bit length ({}) cannot be represented as a field element: {:?}",
                bits, err,
            ))
        })?;

        let fzero = <<T as AssociatedField>::Field as FieldElement>::Integer::from(<<T as AssociatedField>::Field as FieldElement>::zero());
        if <<T as AssociatedField>::Field as FieldElement>::modulus() >> bits_int == fzero {
            return Err(FlpError::Encode(format!(
                "bit length ({}) exceeds field modulus",
                bits,
            )));
        }

        let fone = <<T as AssociatedField>::Field as FieldElement>::one();
        let one = <<T as AssociatedField>::Field as FieldElement>::Integer::from(fone);
        let max_summand = (one << bits_int) - one;

        Ok(Self {
            bits_per_entry: bits,
            entries,
            one,
            max_summand,
            range_checker: poly_range_check(0, 2),
        })
    }
}



impl<T: FixedUnsigned + AssociatedField> Type for FixedPointVecSum<T>
{
    type Measurement = Vec<T>;
    type AggregateResult = Vec<T>;
    type Field = <T as AssociatedField>::Field;

    fn encode_measurement(&self, fp_summands: &Vec<T>) -> Result<Vec<Self::Field>, FlpError>
    {

        let mut encoded: Vec<Self::Field> = Vec::with_capacity(self.bits_per_entry * self.entries);

        for fp_summand in fp_summands
        {
            let summand = &(<T as AssociatedField>::embed(fp_summand));

            if *summand > self.max_summand
            {
                return Err(FlpError::Encode(
                    "value of summand exceeds bit length".to_string(),
                ));
            }

            for l in 0..self.bits_per_entry
            {
                let l = <Self::Field as FieldElement>::Integer::try_from(l).unwrap();
                let w = Self::Field::from((*summand >> l) & self.one);
                encoded.push(w);
            }
        }


        Ok(encoded)
    }

    fn decode_result(&self, data: &[Self::Field]) -> Result<Vec<T>, FlpError>
    {
        if data.len() != self.entries
        {
            return Err(FlpError::Decode("unexpected input length".into()));
        }
        let mut res = vec![];
        for d in data
        {
            let val = <T as AssociatedField>::extract(<Self::Field as FieldElement>::Integer::from(*d))?;
            res.push(val);
        }
        Ok(res)
    }

    fn gadget(&self) -> Vec<Box<dyn Gadget<Self::Field>>>
    {
        vec![Box::new(PolyEval::new(
            self.range_checker.clone(),
            self.bits_per_entry * self.entries,
        ))]
    }

   fn valid(
        &self,
        g: &mut Vec<Box<dyn Gadget<Self::Field>>>,
        input: &[Self::Field],
        joint_rand: &[Self::Field],
        _num_shares: usize,
    ) -> Result<Self::Field, FlpError>
    {
        valid_call_check(self, input, joint_rand)?;

        // Check that each element of `data` is a 0 or 1.
        let mut range_check = Self::Field::zero();
        let mut r = joint_rand[0];
        for chunk in input.chunks(1) {
            range_check += r * g[0].call(chunk)?;
            r *= joint_rand[0];
        }

        Ok(range_check)
    }

    fn truncate(&self, input: Vec<Self::Field>) -> Result<Vec<Self::Field>, FlpError>
    {
        truncate_call_check(self, &input)?;

        let mut decoded_vector = vec![];

        for i_entry in 0..self.entries
        {
            let start = i_entry * self.bits_per_entry;
            let end = (i_entry + 1) * self.bits_per_entry;

            let mut decoded = Self::Field::zero();
            for (l, bit) in input[start..end].iter().enumerate()
            {
                let w = Self::Field::from( <Self::Field as FieldElement>::Integer::try_from(1 << l).unwrap() );
                decoded += w * *bit;
            }
            decoded_vector.push(decoded);
        }
        Ok(decoded_vector)
    }

    fn input_len(&self) -> usize {
        self.bits_per_entry * self.entries
    }

    fn proof_len(&self) -> usize {
        2 * ((1 + (self.bits_per_entry * self.entries)).next_power_of_two() - 1) + 2
    }

    fn verifier_len(&self) -> usize {
        3
    }

    fn output_len(&self) -> usize {
        self.entries
    }

    fn joint_rand_len(&self) -> usize {
        1
    }

    fn prove_rand_len(&self) -> usize {
        1
    }

    fn query_rand_len(&self) -> usize {
        1
    }
}




/////////////////////////////////////////////////////////////////////////////////////////////////
// Testing


#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{random_vector, split_vector, Field96 as TestField};
    use fixed::*;
    use fixed::types::extra::*;
    use fixed_macro::fixed;

    // Number of shares to split input and proofs into in `flp_test`.
    const NUM_SHARES: usize = 3;
    type FP = FixedU64<U8>;
    type S = FixedPointVecSum::<FP>;

    struct ValidityTestCase<F> {
        expect_valid: bool,
        expected_output: Option<Vec<F>>,
    }

    #[test]
    fn test_fixed_point_vector_sum() {
        let entries = 3;
        let sum = S::new(entries).unwrap();

        ////////////////////////////////
        // Round trip
        let input_vec = vec![
            fixed!(27.5 : U56F8),
            fixed!(12.125 : U56F8),
            fixed!(0.25 : U56F8)
        ];

        assert_eq!(
            sum.decode_result(&sum.truncate(sum.encode_measurement(&input_vec).unwrap()).unwrap())
                .unwrap(),
            input_vec
        );

        // Test FLP on valid input.
        flp_validity_test(
            &sum,
            &sum.encode_measurement(&input_vec).unwrap(),
            &ValidityTestCase {
                expect_valid: true,
                expected_output: Some(vec![TestField::from((27 << 8) + (1 << 7)),
                                           TestField::from((12 << 8) + (1 << 5)),
                                           TestField::from((0 << 8)  + (1 << 6))

                ]),
            },
        )
        .unwrap();
    }

    fn flp_validity_test<T: Type>(
        typ: &T,
        input: &[T::Field],
        t: &ValidityTestCase<T::Field>,
    ) -> Result<(), FlpError> {
        let mut gadgets = typ.gadget();

        if input.len() != typ.input_len() {
            return Err(FlpError::Test(format!(
                "unexpected input length: got {}; want {}",
                input.len(),
                typ.input_len()
            )));
        }

        if typ.query_rand_len() != gadgets.len() {
            return Err(FlpError::Test(format!(
                "query rand length: got {}; want {}",
                typ.query_rand_len(),
                gadgets.len()
            )));
        }

        let joint_rand = random_vector(typ.joint_rand_len()).unwrap();
        let prove_rand = random_vector(typ.prove_rand_len()).unwrap();
        let query_rand = random_vector(typ.query_rand_len()).unwrap();

        // Run the validity circuit.
        let v = typ.valid(&mut gadgets, input, &joint_rand, 1)?;
        if v != T::Field::zero() && t.expect_valid {
            return Err(FlpError::Test(format!(
                "expected valid input: valid() returned {}",
                v
            )));
        }
        if v == T::Field::zero() && !t.expect_valid {
            return Err(FlpError::Test(format!(
                "expected invalid input: valid() returned {}",
                v
            )));
        }

        // Generate the proof.
        let proof = typ.prove(input, &prove_rand, &joint_rand)?;
        if proof.len() != typ.proof_len() {
            return Err(FlpError::Test(format!(
                "unexpected proof length: got {}; want {}",
                proof.len(),
                typ.proof_len()
            )));
        }

        // Query the proof.
        let verifier = typ.query(input, &proof, &query_rand, &joint_rand, 1)?;
        if verifier.len() != typ.verifier_len() {
            return Err(FlpError::Test(format!(
                "unexpected verifier length: got {}; want {}",
                verifier.len(),
                typ.verifier_len()
            )));
        }

        // Decide if the input is valid.
        let res = typ.decide(&verifier)?;
        if res != t.expect_valid {
            return Err(FlpError::Test(format!(
                "decision is {}; want {}",
                res, t.expect_valid,
            )));
        }

        // Run distributed FLP.
        let input_shares: Vec<Vec<T::Field>> = split_vector(input, NUM_SHARES)
            .unwrap()
            .into_iter()
            .collect();

        let proof_shares: Vec<Vec<T::Field>> = split_vector(&proof, NUM_SHARES)
            .unwrap()
            .into_iter()
            .collect();

        let verifier: Vec<T::Field> = (0..NUM_SHARES)
            .map(|i| {
                typ.query(
                    &input_shares[i],
                    &proof_shares[i],
                    &query_rand,
                    &joint_rand,
                    NUM_SHARES,
                )
                .unwrap()
            })
            .reduce(|mut left, right| {
                for (x, y) in left.iter_mut().zip(right.iter()) {
                    *x += *y;
                }
                left
            })
            .unwrap();

        let res = typ.decide(&verifier)?;
        if res != t.expect_valid {
            return Err(FlpError::Test(format!(
                "distributed decision is {}; want {}",
                res, t.expect_valid,
            )));
        }

        // Try verifying various proof mutants.
        for i in 0..proof.len() {
            let mut mutated_proof = proof.clone();
            mutated_proof[i] += T::Field::one();
            let verifier = typ.query(input, &mutated_proof, &query_rand, &joint_rand, 1)?;
            if typ.decide(&verifier)? {
                return Err(FlpError::Test(format!(
                    "decision for proof mutant {} is {}; want {}",
                    i, true, false,
                )));
            }
        }

        // Try verifying a proof that is too short.
        let mut mutated_proof = proof.clone();
        mutated_proof.truncate(gadgets[0].arity() - 1);
        if typ
            .query(input, &mutated_proof, &query_rand, &joint_rand, 1)
            .is_ok()
        {
            return Err(FlpError::Test(
                "query on short proof succeeded; want failure".to_string(),
            ));
        }

        // Try verifying a proof that is too long.
        let mut mutated_proof = proof;
        mutated_proof.extend_from_slice(&[T::Field::one(); 17]);
        if typ
            .query(input, &mutated_proof, &query_rand, &joint_rand, 1)
            .is_ok()
        {
            return Err(FlpError::Test(
                "query on long proof succeeded; want failure".to_string(),
            ));
        }

        if let Some(ref want) = t.expected_output {
            let got = typ.truncate(input.to_vec())?;

            if got.len() != typ.output_len() {
                return Err(FlpError::Test(format!(
                    "unexpected output length: got {}; want {}",
                    got.len(),
                    typ.output_len()
                )));
            }

            if &got != want {
                return Err(FlpError::Test(format!(
                    "unexpected output: got {:?}; want {:?}",
                    got, want
                )));
            }
        }

        Ok(())
    }
}






