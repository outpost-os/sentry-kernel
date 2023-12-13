#![no_std]

pub mod arch;
pub mod gate;

#[cfg(not(CONFIG_BUILD_TARGET_RELEASE))]
#[macro_use]
pub mod debug;

#[cfg(feature = "mock")]
pub mod mocks;

#[cfg(not(feature = "mock"))]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    // TODO: use sentry arch's `panic()`
    loop {}
}
