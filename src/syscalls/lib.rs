#![no_std]

pub mod arch;
pub mod gate;

#[cfg(not(feature = "mock"))]
pub mod sysimpl;
#[cfg(not(feature = "mock"))]
use sysimpl::*;

#[cfg(feature = "mock")]
pub mod mocks;
#[cfg(feature = "mock")]
use mocks::*;

#[cfg(not(feature = "mock"))]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
