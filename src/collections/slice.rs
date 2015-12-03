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
pub use core::slice::{bytes, mut_ref_slice, ref_slice};
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

////////////////////////////////////////////////////////////////////////////////
// Sorting
////////////////////////////////////////////////////////////////////////////////

fn insertion_sort<T, F>(v: &mut [T], mut compare: F)
    where F: FnMut(&T, &T) -> Ordering
{
    let len = v.len() as isize;
    let buf_v = v.as_mut_ptr();

    // 1 <= i < len;
    for i in 1..len {
        // j satisfies: 0 <= j <= i;
        let mut j = i;
        unsafe {
            // `i` is in bounds.
            let read_ptr = buf_v.offset(i) as *const T;

            // find where to insert, we need to do strict <,
            // rather than <=, to maintain stability.

            // 0 <= j - 1 < len, so .offset(j - 1) is in bounds.
            while j > 0 && compare(&*read_ptr, &*buf_v.offset(j - 1)) == Less {
                j -= 1;
            }

            // shift everything to the right, to make space to
            // insert this value.

            // j + 1 could be `len` (for the last `i`), but in
            // that case, `i == j` so we don't copy. The
            // `.offset(j)` is always in bounds.

            if i != j {
                let tmp = ptr::read(read_ptr);
                ptr::copy(&*buf_v.offset(j), buf_v.offset(j + 1), (i - j) as usize);
                ptr::copy_nonoverlapping(&tmp, buf_v.offset(j), 1);
                mem::forget(tmp);
            }
        }
    }
}

fn merge_sort<T, F>(v: &mut [T], mut compare: F)
    where F: FnMut(&T, &T) -> Ordering
{
    // warning: this wildly uses unsafe.
    const BASE_INSERTION: usize = 32;
    const LARGE_INSERTION: usize = 16;

    // FIXME #12092: smaller insertion runs seems to make sorting
    // vectors of large elements a little faster on some platforms,
    // but hasn't been tested/tuned extensively
    let insertion = if size_of::<T>() <= 16 {
        BASE_INSERTION
    } else {
        LARGE_INSERTION
    };

    let len = v.len();

    // short vectors get sorted in-place via insertion sort to avoid allocations
    if len <= insertion {
        insertion_sort(v, compare);
        return;
    }

    // allocate some memory to use as scratch memory, we keep the
    // length 0 so we can keep shallow copies of the contents of `v`
    // without risking the dtors running on an object twice if
    // `compare` panics.
    let mut working_space = Vec::with_capacity(2 * len);
    // these both are buffers of length `len`.
    let mut buf_dat = working_space.as_mut_ptr();
    let mut buf_tmp = unsafe { buf_dat.offset(len as isize) };

    // length `len`.
    let buf_v = v.as_ptr();

    // step 1. sort short runs with insertion sort. This takes the
    // values from `v` and sorts them into `buf_dat`, leaving that
    // with sorted runs of length INSERTION.

    // We could hardcode the sorting comparisons here, and we could
    // manipulate/step the pointers themselves, rather than repeatedly
    // .offset-ing.
    for start in (0..len).step_by(insertion) {
        // start <= i < len;
        for i in start..cmp::min(start + insertion, len) {
            // j satisfies: start <= j <= i;
            let mut j = i as isize;
            unsafe {
                // `i` is in bounds.
                let read_ptr = buf_v.offset(i as isize);

                // find where to insert, we need to do strict <,
                // rather than <=, to maintain stability.

                // start <= j - 1 < len, so .offset(j - 1) is in
                // bounds.
                while j > start as isize && compare(&*read_ptr, &*buf_dat.offset(j - 1)) == Less {
                    j -= 1;
                }

                // shift everything to the right, to make space to
                // insert this value.

                // j + 1 could be `len` (for the last `i`), but in
                // that case, `i == j` so we don't copy. The
                // `.offset(j)` is always in bounds.
                ptr::copy(&*buf_dat.offset(j), buf_dat.offset(j + 1), i - j as usize);
                ptr::copy_nonoverlapping(read_ptr, buf_dat.offset(j), 1);
            }
        }
    }

    // step 2. merge the sorted runs.
    let mut width = insertion;
    while width < len {
        // merge the sorted runs of length `width` in `buf_dat` two at
        // a time, placing the result in `buf_tmp`.

        // 0 <= start <= len.
        for start in (0..len).step_by(2 * width) {
            // manipulate pointers directly for speed (rather than
            // using a `for` loop with `range` and `.offset` inside
            // that loop).
            unsafe {
                // the end of the first run & start of the
                // second. Offset of `len` is defined, since this is
                // precisely one byte past the end of the object.
                let right_start = buf_dat.offset(cmp::min(start + width, len) as isize);
                // end of the second. Similar reasoning to the above re safety.
                let right_end_idx = cmp::min(start + 2 * width, len);
                let right_end = buf_dat.offset(right_end_idx as isize);

                // the pointers to the elements under consideration
                // from the two runs.

                // both of these are in bounds.
                let mut left = buf_dat.offset(start as isize);
                let mut right = right_start;

                // where we're putting the results, it is a run of
                // length `2*width`, so we step it once for each step
                // of either `left` or `right`.  `buf_tmp` has length
                // `len`, so these are in bounds.
                let mut out = buf_tmp.offset(start as isize);
                let out_end = buf_tmp.offset(right_end_idx as isize);

                // If left[last] <= right[0], they are already in order:
                // fast-forward the left side (the right side is handled
                // in the loop).
                // If `right` is not empty then left is not empty, and
                // the offsets are in bounds.
                if right != right_end && compare(&*right.offset(-1), &*right) != Greater {
                    let elems = (right_start as usize - left as usize) / mem::size_of::<T>();
                    ptr::copy_nonoverlapping(&*left, out, elems);
                    out = out.offset(elems as isize);
                    left = right_start;
                }

                while out < out_end {
                    // Either the left or the right run are exhausted,
                    // so just copy the remainder from the other run
                    // and move on; this gives a huge speed-up (order
                    // of 25%) for mostly sorted vectors (the best
                    // case).
                    if left == right_start {
                        // the number remaining in this run.
                        let elems = (right_end as usize - right as usize) / mem::size_of::<T>();
                        ptr::copy_nonoverlapping(&*right, out, elems);
                        break;
                    } else if right == right_end {
                        let elems = (right_start as usize - left as usize) / mem::size_of::<T>();
                        ptr::copy_nonoverlapping(&*left, out, elems);
                        break;
                    }

                    // check which side is smaller, and that's the
                    // next element for the new run.

                    // `left < right_start` and `right < right_end`,
                    // so these are valid.
                    let to_copy = if compare(&*left, &*right) == Greater {
                        step(&mut right)
                    } else {
                        step(&mut left)
                    };
                    ptr::copy_nonoverlapping(&*to_copy, out, 1);
                    step(&mut out);
                }
            }
        }

        mem::swap(&mut buf_dat, &mut buf_tmp);

        width *= 2;
    }

    // write the result to `v` in one go, so that there are never two copies
    // of the same object in `v`.
    unsafe {
        ptr::copy_nonoverlapping(&*buf_dat, v.as_mut_ptr(), len);
    }

    // increment the pointer, returning the old pointer.
    #[inline(always)]
    unsafe fn step<T>(ptr: &mut *mut T) -> *mut T {
        let old = *ptr;
        *ptr = ptr.offset(1);
        old
    }
}
