
use fixed::types::extra::*;
use fixed::*;
use num::*;

use crate::field::FieldElement;

use std::iter::*;
use std::convert::Into;

// use crate::flp::gadgets::{BlindPolyEval, Mul, ParallelSumGadget, PolyEval};
// use crate::flp::{FlpError, Gadget, Type};
// use crate::polynomial::poly_range_check;

// use std::convert::TryFrom;
// use std::marker::PhantomData;

pub fn fixed_id(a: FixedI16<U8>) -> FixedI16<U8> {
    a
}


//////////////////////////////////////////////////////////////
// basics

fn from_bool<I>(b:bool) -> I
    where I : Num
{
    if b {one()} else {zero()}
}


//////////////////////////////////////////////////////////////
// Definition of bit encodings

pub trait HasBitEncoding<X,B>
{
    type BitEncodingParameter;
    fn encode_bits_size(p: &Self::BitEncodingParameter) -> usize;
    fn encode_bits(p: &Self::BitEncodingParameter, x: &X) -> Vec<B>;
    fn decode_bits(p: &Self::BitEncodingParameter, bs: &Vec<B>) -> (X,Vec<B>);
}

//////////////////////////////////////////////////////////////
// Bit encodings for primitives



impl<B> HasBitEncoding<i32,B> for ()
    where
      B : Num + Into<i32> + Clone
{
   type BitEncodingParameter = ();

    fn encode_bits(_:&(), x: &i32) -> Vec<B> {
        let get_bit = |i| from_bool(((x >> i) & 1) == 1);

        (0..32).map(get_bit).collect()
    }

    fn encode_bits_size(_:&()) -> usize {32}

    fn decode_bits(_:&(), bits: &Vec<B>) -> (i32,Vec<B>) {
        let (relevant,rest) = bits.split_at(32);
        let set_bit = |(i,bit): (usize,&B)| (Into::<i32>::into(bit.clone()) << i);
        let res : i32
            = zip(0..32, relevant.into_iter())
            .map(set_bit)
            .sum();
        (res, rest.to_vec())
    }
}


#[test]
fn test_encode_bits_i32() {
    let x:i32 = 9;
    let x_:Vec<i8> = <()>::encode_bits(&(),&x);
    let b:Vec<i8>
        = vec![1,0,0,1,
               0,0,0,0,
               0,0,0,0,
               0,0,0,0,
               0,0,0,0,
               0,0,0,0,
               0,0,0,0,
               0,0,0,0];
    assert_eq!(x_, b);
}


//////////////////////////////////////////////////////////////
// Bit encodings for vectors of things
impl<B, X, Z> HasBitEncoding<Vec<X>,B> for Z
    where
        B : Clone,
        Z : HasBitEncoding<X,B>
    {
    type BitEncodingParameter = (usize, Z::BitEncodingParameter);
    fn encode_bits((size,param): &(usize, Z::BitEncodingParameter), xs: &Vec<X>) -> Vec<B> {
        assert_eq!(size, xs.len());
        xs.iter().flat_map(|x| Z::encode_bits(param, x)).collect()
    }
    fn encode_bits_size((size,param): &(usize, Z::BitEncodingParameter)) -> usize {
        Z::encode_bits_size(param) * size
    }
    fn decode_bits((size,param): &(usize, Z::BitEncodingParameter), bits: &Vec<B>) -> (Vec<X>,Vec<B>) {
        let (relevant_slice,rest_slice) = bits.split_at(Z::encode_bits_size(&param) * size);
        let relevant = relevant_slice.to_vec();
        let rest = rest_slice.to_vec();

        let mut res : Vec<X> = Vec::with_capacity(*size);
        for _ in 0..*size {
            let (item, relevant) = Z::decode_bits(&param, &relevant);
            res.push(item);
        }

        (res, rest)
    }
}
