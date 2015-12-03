#![feature(unsafe_no_drop_flag)]
#![feature(dropck_parametricity)]
#![feature(filling_drop)]
#![feature(collections_bound, heap_api, wrapping, unique, oom)]
#![feature(core, alloc, collections)]

#![cfg_attr(test, feature(test, range_inclusive))]

#[path="std/mod.rs"]
mod std_mod;

extern crate core;
extern crate alloc;
extern crate collections as core_collections;
extern crate rand;

pub use std::{borrow, clone, cmp, default, fmt, hash, iter};
pub use std::{marker, mem, num, ops, option, ptr, result};

pub use std_mod::collections as collections;

#[cfg(test)]
pub use std::{cell};

#[test]
fn it_works() {
}
