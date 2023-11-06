#![no_std]
#![feature(naked_functions)]

pub mod arch;
pub mod gate;
pub mod mocks;

#[cfg(not(feature = "mock"))]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
