#![feature(unsafe_no_drop_flag)]
#![feature(dropck_parametricity)]
#![feature(filling_drop)]
#![feature(heap_api, wrapping, unique)]
#![feature(core, alloc)]

// features for mod collections
#![feature(box_syntax)]
#![feature(slice_patterns)]
#![feature(box_patterns)]
#![feature(unicode)]
#![feature(core_intrinsics)]
#![feature(num_bits_bytes)]
#![feature(fmt_internals, fmt_radix)]
#![feature(ptr_as_ref, ref_slice)]
#![feature(clone_from_slice, slice_bytes)]
#![feature(drop_in_place)]

#![cfg_attr(test, feature(test, range_inclusive))]
#![cfg_attr(test, feature(step_trait))]
#![cfg_attr(test, feature(zero_one))]

// features for mod alloc
#![feature(allocator, needs_allocator, lang_items, fundamental, unboxed_closures)]
#![feature(optin_builtin_traits)]
#![feature(box_heap, coerce_unsized, shared, unsize)]
#![feature(core_slice_ext)]

#[cfg(test)]
extern crate test;

// Allow testing mod alloc.

#[cfg(test)]
#[macro_use]
extern crate log;

#[path="std/mod.rs"]
mod std_mod;

extern crate core;
extern crate alloc as core_alloc;
// extern crate collections as core_collections;
extern crate rand;

mod alloc;

#[path="collections/mod.rs"]
mod core_collections;

pub use core_collections::{binary_heap, btree_map, btree_set, vec};
pub use core_collections::{linked_list, enum_set, vec_deque, rustc_unicode, range};
pub use core_collections::{Bound};

// export public functionality
pub use core_collections::{borrow, fmt};
pub use alloc::{boxed, rc};
pub use alloc::raw_vec::RawVec;
pub mod sync { pub use alloc::arc::{Arc, Weak}; }

pub use std::{clone, cmp, default, hash, iter};
pub use std::{marker, mem, num, ops, option, ptr, result};

// slice and str almost certainly cannot be done outside of
// libstd. And its easier to leave string there too.
pub use std::{slice, str, string};

pub use std_mod::collections as collections;

#[cfg(test)]
pub use std::{cell};

#[cfg(test)]
fn range_inclusive<A>(start: A, stop: A) -> ::std::iter::RangeInclusive<A>
    where A: ::std::iter::Step + ::std::num::One + Clone
{
    #![allow(deprecated)]
    ::std::iter::range_inclusive(start, stop)
}
