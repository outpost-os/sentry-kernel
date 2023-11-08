#[cfg(target_arch = "arm")]
pub mod arm_cortex_m;
#[cfg(target_arch = "arm")]
pub use arm_cortex_m::*;

#[cfg(target_arch = "x86_64")]
pub mod x86_64;
#[cfg(target_arch = "x86_64")]
pub use x86_64::*;
