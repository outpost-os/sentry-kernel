#![cfg_attr(not(feature = "std"), no_std)]
#![feature(asm_const)]

use core::panic::PanicInfo;
#[macro_use]
mod arch;

pub mod syscall;
pub mod uapi;

#[cfg(not(feature = "std"))]
#[panic_handler]
fn panic(_: &PanicInfo) -> ! {
    loop {}
}
