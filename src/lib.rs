#![feature(unsafe_no_drop_flag)]
#![feature(dropck_parametricity)]

#[path="std/mod.rs"]
mod std_mod;

extern crate core;
extern crate alloc;
extern crate collections as core_collections;
extern crate rand;

pub use std::{borrow, clone, cmp, default, fmt, hash, iter};
pub use std::{marker, mem, num, ops, option, ptr, result};

pub use std_mod::collections as collections;

#[test]
fn it_works() {
}
