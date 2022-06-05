use fixed::types::extra::*;
use fixed::*;
use num::*;

use crate::field::FieldElement;

use std::iter::*;
use std::convert::Into;

mod generic_bit_encoding;


pub fn fixed_id(a: FixedI16<U8>) -> FixedI16<U8> {
    a
}


