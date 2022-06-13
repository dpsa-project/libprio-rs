
use fixed::*;
use fixed::types::extra::*;
use fixed::traits::{Fixed, FixedUnsigned};

use crate::field::{FieldElement, Field96};
use crate::flp::{FlpError, Gadget, Type};
use crate::flp::types::{truncate_call_check, valid_call_check};
use crate::polynomial::poly_range_check;
use crate::flp::gadgets::PolyEval;
use std::convert::{TryFrom, TryInto};

/// Objects with this trait have a FieldElement type attached, into which their instances
/// must be embeddable and re-extractable.
pub trait AssociatedField {
    /// The field type that allows an embedding of the trait bearer.
    type Field: FieldElement;

    /// Convert a value to the corresponding integer representation
    /// in the associated field.
    fn embed(&self) -> <Self::Field as FieldElement>::Integer;

    /// Convert the integer value of a field element to the corresponding value.
    /// Should be the inverse of the embed function, erroring on elements not in
    /// embed's image.
    fn extract(felem: <Self::Field as FieldElement>::Integer) -> Result<Self, FlpError> where Self: Sized;
}

impl<U: Unsigned + LeEqU64> AssociatedField for FixedU64<U>{
    type Field = Field96;

    /// The bit string representing a Fixed64 number is interpreted as an integer in Field96.
    fn embed(&self) -> <Field96 as FieldElement>::Integer {
        let bits = u128::from(FixedU64::to_bits(*self));
        let felem = <Field96 as From<u128>>::from(bits);
        <Field96 as FieldElement>::Integer::from(felem)
    }

    /// If the field element can be represented as u64 integer, the bitstring of said integer
    /// is interpreted as Fixed64<U> decimal.
    fn extract(felem: <Field96 as FieldElement>::Integer) -> Result<Self, FlpError> {
        let intval = <u64 as TryFrom<<Field96 as FieldElement>::Integer>>::try_from(felem);
        Ok(FixedU64::<U>::from_bits(intval.unwrap()))
    }
}
