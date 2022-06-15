
use fixed::*;
use fixed::types::extra::*;
use fixed::traits::{Fixed, FixedUnsigned};

use crate::vdaf::dpsa::associated_field::*;
use crate::field::{FieldElement, Field96};
use crate::flp::{FlpError, Gadget, Type};
use crate::flp::types::{truncate_call_check, valid_call_check};
use crate::polynomial::poly_range_check;
use crate::flp::gadgets::PolyEval;
use std::convert::{TryFrom, TryInto};


#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixedPointL2BoundedVecSum<T: FixedUnsigned + AssociatedField>
{
    bits_per_entry: usize,
    entries: usize,
    bits_for_norm: usize,
    one: <<T as AssociatedField>::Field as FieldElement>::Integer,
    max_summand: <<T as AssociatedField>::Field as FieldElement>::Integer,
    range_checker: Vec<<T as AssociatedField>::Field>,
}



impl<T: FixedUnsigned + AssociatedField> FixedPointL2BoundedVecSum<T>
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





impl<T: FixedUnsigned + AssociatedField> Type for FixedPointL2BoundedVecSum<T>
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







