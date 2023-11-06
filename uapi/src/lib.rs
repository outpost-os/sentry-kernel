#![cfg_attr(not(feature = "std"), no_std)]
#![feature(asm_const)]

#[macro_use]
mod arch;

pub mod syscall;
pub mod uapi;

#[cfg(not(feature = "std"))]
mod panic;
