// Copyright 2012-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A dynamically-sized view into a contiguous sequence, `[T]`.
//!
//! Slices are a view into a block of memory represented as a pointer and a
//! length.
//!
//! ```
//! // slicing a Vec
//! let vec = vec![1, 2, 3];
//! let int_slice = &vec[..];
//! // coercing an array to a slice
//! let str_slice: &[&str] = &["one", "two", "three"];
//! ```
//!
//! Slices are either mutable or shared. The shared slice type is `&[T]`,
//! while the mutable slice type is `&mut [T]`, where `T` represents the element
//! type. For example, you can mutate the block of memory that a mutable slice
//! points to:
//!
//! ```
//! let x = &mut [1, 2, 3];
//! x[1] = 7;
//! assert_eq!(x, &[1, 7, 3]);
//! ```
//!
//! Here are some of the things this module contains:
//!
//! ## Structs
//!
//! There are several structs that are useful for slices, such as `Iter`, which
//! represents iteration over a slice.
//!
//! ## Trait Implementations
//!
//! There are several implementations of common traits for slices. Some examples
//! include:
//!
//! * `Clone`
//! * `Eq`, `Ord` - for slices whose element type are `Eq` or `Ord`.
//! * `Hash` - for slices whose element type is `Hash`
//!
//! ## Iteration
//!
//! The slices implement `IntoIterator`. The iterator yields references to the
//! slice elements.
//!
//! ```
//! let numbers = &[0, 1, 2];
//! for n in numbers {
//!     println!("{} is a number!", n);
//! }
//! ```
//!
//! The mutable slice yields mutable references to the elements:
//!
//! ```
//! let mut scores = [7, 8, 9];
//! for score in &mut scores[..] {
//!     *score += 1;
//! }
//! ```
//!
//! This iterator yields mutable references to the slice's elements, so while
//! the element type of the slice is `i32`, the element type of the iterator is
//! `&mut i32`.
//!
//! * `.iter()` and `.iter_mut()` are the explicit methods to return the default
//!   iterators.
//! * Further methods that return iterators are `.split()`, `.splitn()`,
//!   `.chunks()`, `.windows()` and more.
//!
//! *[See also the slice primitive type](../primitive.slice.html).*

// Many of the usings in this module are only used in the test configuration.
// It's cleaner to just turn off the unused_imports warning than to fix them.
#![allow(unused_imports)]

use alloc::boxed::Box;
use core::clone::Clone;
use core::cmp::Ordering::{self, Greater, Less};
use core::cmp::{self, Ord, PartialEq};
use core::iter::Iterator;
use core::marker::Sized;
use core::mem::size_of;
use core::mem;
use core::ops::FnMut;
use core::option::Option::{self, Some, None};
use core::ptr;
use core::result::Result;
use core::slice as core_slice;

use borrow::{Borrow, BorrowMut, ToOwned};
use vec::Vec;

pub use core::slice::{Chunks, Windows};
pub use core::slice::{Iter, IterMut};
pub use core::slice::{SplitMut, ChunksMut, Split};
pub use core::slice::{SplitN, RSplitN, SplitNMut, RSplitNMut};
#[allow(deprecated)]
pub use core::slice::{bytes};
pub use core::slice::{from_raw_parts, from_raw_parts_mut};

////////////////////////////////////////////////////////////////////////////////
// Basic slice extension methods
////////////////////////////////////////////////////////////////////////////////

// HACK(japaric) needed for the implementation of `vec!` macro during testing
// NB see the hack module in this file for more details
#[cfg(test)]
pub use self::hack::into_vec;

// HACK(japaric) needed for the implementation of `Vec::clone` during testing
// NB see the hack module in this file for more details
#[cfg(test)]
pub use self::hack::to_vec;

// HACK(japaric): With cfg(test) `impl [T]` is not available, these three
// functions are actually methods that are in `impl [T]` but not in
// `core::slice::SliceExt` - we need to supply these functions for the
// `test_permutations` test
pub mod hack {
    use alloc::boxed::Box;
    use core::clone::Clone;
    #[cfg(test)]
    use core::iter::Iterator;
    use core::mem;
    #[cfg(test)]
    use core::option::Option::{Some, None};

    #[cfg(test)]
    use string::ToString;
    use vec::Vec;

    #[cfg(test)]
    pub fn into_vec<T>(mut b: Box<[T]>) -> Vec<T> {
        unsafe {
            let xs = Vec::from_raw_parts(b.as_mut_ptr(), b.len(), b.len());
            mem::forget(b);
            xs
        }
    }

    #[inline]
    pub fn to_vec<T>(s: &[T]) -> Vec<T>
        where T: Clone
    {
        let mut vector = Vec::with_capacity(s.len());
        vector.push_all(s);
        vector
    }
}

////////////////////////////////////////////////////////////////////////////////
// Extension traits for slices over specific kinds of data
////////////////////////////////////////////////////////////////////////////////
/// An extension trait for concatenating slices
pub trait SliceConcatExt<T: ?Sized> {
    /// The resulting type after concatenation
    type Output;

    /// Flattens a slice of `T` into a single value `Self::Output`.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(["hello", "world"].concat(), "helloworld");
    /// ```
    fn concat(&self) -> Self::Output;

    /// Flattens a slice of `T` into a single value `Self::Output`, placing a
    /// given separator between each.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(["hello", "world"].join(" "), "hello world");
    /// ```
    fn join(&self, sep: &T) -> Self::Output;

    /// Flattens a slice of `T` into a single value `Self::Output`, placing a
    /// given separator between each.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(deprecated)]
    /// assert_eq!(["hello", "world"].connect(" "), "hello world");
    /// ```
    fn connect(&self, sep: &T) -> Self::Output;
}

impl<T: Clone, V: Borrow<[T]>> SliceConcatExt<T> for [V] {
    type Output = Vec<T>;

    fn concat(&self) -> Vec<T> {
        let size = self.iter().fold(0, |acc, v| acc + v.borrow().len());
        let mut result = Vec::with_capacity(size);
        for v in self {
            result.push_all(v.borrow())
        }
        result
    }

    fn join(&self, sep: &T) -> Vec<T> {
        let size = self.iter().fold(0, |acc, v| acc + v.borrow().len());
        let mut result = Vec::with_capacity(size + self.len());
        let mut first = true;
        for v in self {
            if first {
                first = false
            } else {
                result.push(sep.clone())
            }
            result.push_all(v.borrow())
        }
        result
    }

    fn connect(&self, sep: &T) -> Vec<T> {
        ::core_collections::slice::SliceConcatExt::join(self, sep)
    }
}

////////////////////////////////////////////////////////////////////////////////
// Standard trait implementations for slices
////////////////////////////////////////////////////////////////////////////////

impl<T> Borrow<[T]> for Vec<T> {
    fn borrow(&self) -> &[T] {
        &self[..]
    }
}

impl<T> BorrowMut<[T]> for Vec<T> {
    fn borrow_mut(&mut self) -> &mut [T] {
        &mut self[..]
    }
}
