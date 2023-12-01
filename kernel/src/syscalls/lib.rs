#![no_std]

pub mod arch;
pub mod gate;

#[cfg(CONFIG_BUILD_TARGET_DEBUG)]
#[macro_use]
pub mod debug;

pub mod sysimpl;
use sysimpl::*;

#[cfg(feature = "mock")]
pub mod mocks;

#[cfg(not(feature = "mock"))]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    // TODO: use sentry arch's `panic()`
    loop {}
}
