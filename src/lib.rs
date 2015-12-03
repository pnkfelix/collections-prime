#![feature(unsafe_no_drop_flag)]
#![feature(dropck_parametricity)]
#![feature(filling_drop)]
#![feature(heap_api, wrapping, unique, oom)]
#![feature(core, alloc)]

// features for mod collections
#![feature(box_syntax)]
#![feature(slice_patterns)]
#![feature(box_patterns)]
#![feature(unicode)]
#![feature(core_intrinsics)]
#![feature(num_bits_bytes)]
#![feature(fmt_internals, fmt_radix)]
#![feature(ptr_as_ref, ref_slice, step_by, into_cow)]
#![feature(clone_from_slice, slice_bytes)]
#![feature(drop_in_place)]

#![cfg_attr(test, feature(test, range_inclusive))]

#[cfg(test)]
extern crate test;

#[path="std/mod.rs"]
mod std_mod;

extern crate core;
extern crate alloc;
// extern crate collections as core_collections;
extern crate rand;

#[path="collections/mod.rs"]
mod core_collections;

pub use core_collections::{binary_heap, btree_map, btree_set, vec};
pub use core_collections::{linked_list, enum_set, vec_deque, rustc_unicode, range};
pub use core_collections::{Bound};

pub use std::{borrow, clone, cmp, default, fmt, hash, iter};
pub use std::{marker, mem, num, ops, option, ptr, result};

// slice and str almost certainly cannot be done outside of
// libstd. And its easier to leave string there too.
pub use std::{slice, str, string};

pub use std_mod::collections as collections;

pub use alloc::{boxed};

#[cfg(test)]
pub use std::{cell};

#[test]
fn it_works() {
}
