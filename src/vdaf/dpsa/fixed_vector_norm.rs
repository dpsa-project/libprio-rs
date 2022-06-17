
//use fixed::*;
//use fixed::types::extra::*;
use fixed::traits::{Fixed, FixedUnsigned};

//use crate::vdaf::dpsa::associated_field::*;
use crate::field::{FieldElement};
use crate::flp::{FlpError, Gadget, Type};
use crate::flp::types::{truncate_call_check, valid_call_check};
use crate::polynomial::poly_range_check;
use crate::flp::gadgets::PolyEval;

use std::{
    convert::{TryFrom, TryInto},
    marker::PhantomData,
    fmt::{Debug},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixedPointL2BoundedVecSum<T: FixedUnsigned, F: FieldElement>
{
    bits_per_entry: usize,
    entries: usize,
    bits_for_norm: usize,
    one: <F as FieldElement>::Integer,
    max_summand: <F as FieldElement>::Integer,
    range_01_checker: Vec<F>,
    square_computer: Vec<F>,
    phantom: PhantomData<T>,
}



impl<T: FixedUnsigned, F: FieldElement> FixedPointL2BoundedVecSum<T, F>
{
    pub fn new(entries: usize) -> Result<Self, FlpError>
    {
        let bits = (<T as Fixed>::INT_NBITS + <T as Fixed>::FRAC_NBITS).try_into().unwrap();

        let bits_int = <F as FieldElement>::Integer::try_from(bits).map_err(|err| {
            FlpError::Encode(format!(
                "bit length ({}) cannot be represented as a field element: {:?}",
                bits, err,
            ))
        })?;

        let fzero = <F as FieldElement>::Integer::from(<F as FieldElement>::zero());
        if <F as FieldElement>::modulus() >> bits_int == fzero {
            return Err(FlpError::Encode(format!(
                "bit length ({}) exceeds field modulus",
                bits,
            )));
        }

        let fone = <F as FieldElement>::one();
        let one = <F as FieldElement>::Integer::from(fone);
        let max_summand = (one << bits_int) - one;

        ///////////////////////////
        // make sure that the maximal value that the norm can take fits into our field
        // it is: `entries * 2^(2*bits + 1)`
        println!("bits is {bits}");
        let usize_max_norm_value : usize = entries * (1 << (2 * bits + 1));
        let max_norm_value = <F as FieldElement>::Integer::try_from(usize_max_norm_value).map_err(|err| {
            FlpError::Encode(format!(
                "bit length ({}) cannot be represented as a FieldElement::Integer: {:?}",
                bits, err,
            ))
        })?;
        //
        if max_norm_value > <F as FieldElement>::modulus()
        {
            return Err(FlpError::Encode(format!(
                "The maximal norm value ({}) exceeds field modulus",
                usize_max_norm_value,
            )));
        }
        println!("The max norm_value is: {:?}\nThe field modulus is: {:?}", max_norm_value, <F as FieldElement>::modulus());

        ///////////////////////////
        // The norm of our vector should be less than `2^(2*(bits - 1))`
        // This means that a valid norm is given exactly by a binary
        // number with the following number of bits.
        let bits_for_norm = 2 * (bits - 1);


        ///////////////////////////
        // return the constructed self
        Ok(Self {
            bits_per_entry: bits,
            entries,
            bits_for_norm,
            one,
            max_summand,
            range_01_checker: poly_range_check(0, 2),
            square_computer: vec![F::zero(), F::zero(), F::one()],
            phantom: PhantomData
        })
    }
}



/////////////////////////////////////////////////////////////////////////////////
// helper functions


//
// computing the value of binary encoded bit vectors
fn decode_field_bits<F>(bits: &[F]) -> F where
    F : FieldElement
{

    let mut decoded = F::zero();
    for (l, bit) in bits.iter().enumerate()
    {
        let w = F::from( F::Integer::try_from(1 << l).unwrap() );
        decoded += w * *bit;
    }
    decoded
}


//
// computing the norm of a vector of field entries
fn compute_norm_of_entries<F,Fs,SquareFun,E>(entries: Fs, bits_per_entry: usize, sq: &mut SquareFun) -> Result<F,E> where
    F : FieldElement,
    Fs : IntoIterator<Item = F>,
    SquareFun : FnMut(F) -> Result<F,E>
{
    //--------------------------------------------
    // norm computation
    //
    // We need to ensure that norm(entries) = claimed_norm
    // let entries = &input[0..self.entries*self.bits_per_entry];
    let mut computed_norm = F::zero();
    //
    // constants
    let constant_part = F::Integer::try_from(1 << (2*bits_per_entry - 2)).unwrap();
    let linear_part   = F::Integer::try_from(1 << (bits_per_entry)).unwrap();
    //
    for entry in entries.into_iter()
    {
        let summand = sq(entry)?
            + F::from(constant_part)
            - F::from(linear_part)*(entry);
        computed_norm += summand;
    }
    Ok(computed_norm)
}




impl<T: FixedUnsigned, F: FieldElement> Type for FixedPointL2BoundedVecSum<T, F> where
    F::Integer: TryFrom<<T as Fixed>::Bits>,
    F::Integer: TryFrom<usize>,
    T::Bits: TryFrom<F::Integer>,
    <T::Bits as TryFrom<F::Integer>>::Error: Debug,
    <F::Integer as TryFrom<T::Bits>>::Error: Debug,
{
    type Measurement = Vec<T>;
    type AggregateResult = Vec<T>;
    type Field = F;

    fn encode_measurement(&self, fp_summands: &Vec<T>) -> Result<Vec<Self::Field>, FlpError>
    {

        // first convert all my entries to the field-integers
        let mut integer_entries : Vec<<Self::Field as FieldElement>::Integer>  = Vec::with_capacity(self.entries);
        for fp_summand in fp_summands
        {
            let summand = &F::Integer::try_from(<T as Fixed>::to_bits(*fp_summand)).unwrap();

            if *summand > self.max_summand
            {
                return Err(FlpError::Encode(
                    "value of summand exceeds bit length".to_string(),
                ));
            }
            integer_entries.push(*summand);
        }


        // then encode them bitwise
        let mut encoded: Vec<Self::Field> = Vec::with_capacity(self.bits_per_entry * self.entries + self.bits_for_norm);

        for entry in integer_entries.clone()
        {

            // push all bits of all entries
            for l in 0..self.bits_per_entry
            {
                let l = <Self::Field as FieldElement>::Integer::try_from(l).unwrap();
                let w = Self::Field::from((entry >> l) & self.one);
                encoded.push(w);
            }
        }

        // compute the norm
        let field_entries = integer_entries.iter().map(|&x| Self::Field::from(x));
        let norm = compute_norm_of_entries::<_,_,_,FlpError>(field_entries, self.bits_per_entry, &mut |x| Ok(x * x))?;
        let norm_int = <Self::Field as FieldElement>::Integer::from(norm);

        // push the bits of the norm
        for l in 0..self.bits_for_norm
        {
            let l = <Self::Field as FieldElement>::Integer::try_from(l).unwrap();
            let w = Self::Field::from((norm_int >> l) & self.one);
            encoded.push(w);
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
            let val = T::from_bits(T::Bits::try_from(<Self::Field as FieldElement>::Integer::from(*d)).unwrap());
            res.push(val);
        }
        Ok(res)
    }

    fn gadget(&self) -> Vec<Box<dyn Gadget<Self::Field>>>
    {
        // We need two gadgets:
        //
        // (0): check that field element is 0 or 1
        let gadget0 = PolyEval::new(
            self.range_01_checker.clone(),
            self.bits_per_entry * self.entries + self.bits_for_norm,
        );
        //
        // (1): compute square of field element
        let gadget1 = PolyEval::new(
            self.square_computer.clone(),
            self.entries,
        );

        vec![Box::new(gadget0), Box::new(gadget1)]
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


        //--------------------------------------------
        // range checking
        //
        // (I) for encoded input vector entries
        //    We need to make sure that all the input vector entries
        //    contain only 0/1 field elements.
        //
        // (II) for encoded norm
        //    The norm should also be encoded by 0/1 field elements.
        //    Every such encoded number represents a valid norm.
        //
        // Since all input vector entry (field-)bits, as well as the norm bits, are contiguous,
        // we do the check directly for all bits [0..entries*bits_per_entry + bits_for_norm].
        //
        // Check that each element is a 0 or 1:
        let mut validity_check = Self::Field::zero();
        let mut r = joint_rand[0];
        for chunk in input.chunks(1) {
            validity_check += r * g[0].call(chunk)?;
            r *= joint_rand[0];
        }


        //--------------------------------------------
        // norm computation
        //
        // an iterator over the decoded entries
        println!("before entry decoding");
        let decoded_entries =
            input[0..self.entries*self.bits_per_entry]
            .chunks(self.bits_per_entry)
            .map(decode_field_bits);
        //
        // the computed norm
        let computed_norm = compute_norm_of_entries(decoded_entries, self.bits_per_entry, &mut |x| g[1].call(std::slice::from_ref(&x)))?;
        //
        // the claimed norm
        let claimed_norm_enc = &input[self.entries*self.bits_per_entry..];
        println!("before norm decoding, it is: {:?}", claimed_norm_enc);
        println!("parameters are: \nself.entries: {}\nself.bits_per_entry: {}\nself.bits_for_norm: {}\nnorm_length: {}", self.entries, self.bits_per_entry, self.bits_for_norm, claimed_norm_enc.len());
        let claimed_norm = decode_field_bits(claimed_norm_enc);
        //
        // add the check that computed norm == claimed norm
        validity_check += r * (computed_norm - claimed_norm);


        // Return the result
        Ok(validity_check)
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
        self.bits_per_entry * self.entries + self.bits_for_norm
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
        2
    }

    fn query_rand_len(&self) -> usize {
        1
    }
}







