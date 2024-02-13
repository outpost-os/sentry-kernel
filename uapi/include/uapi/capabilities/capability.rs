#![no_std]

use bitflags::bitflags;

bitflags! {
    /// Capabilities are encoded as a bitmask, with the following register-like structure:
    ///  [ reserved ][ other capa ][ mem ][ sys capa ][ dev capa ]
    ///  31        25,24        20,19  16,15        12,11        0
    ///
    /// this allows dev handle to hold the associated dev capa
    #[repr(C)]
    pub struct Capability: u32 {
        const DEV_BUSES   = 0b0000_0000_0001;
        const DEV_IO      = 0b0000_0000_0010;
        const DEV_DMA     = 0b0000_0000_0100;
        const DEV_ANALOG  = 0b0000_0000_1000;
        const DEV_TIMER   = 0b0000_0001_0000;
        const DEV_STORAGE = 0b0000_0010_0000;
        const DEV_CRYPTO  = 0b0000_0100_0000;
        const DEV_CLOCK   = 0b0000_1000_0000;
        const DEV_POWER   = 0b0001_0000_0000;
        const DEV_NEURAL  = 0b0010_0000_0000;

        const SYS_UPGRADE   = 0b0001_0000_0000_0000;
        const SYS_POWER     = 0b0010_0000_0000_0000;
        const SYS_PROCSTART = 0b0010_0000_0000_0000;

        const MEM_SHM_OWN      = 0b0001_0000_0000_0000_0000;
        const MEM_SHM_USE      = 0b0010_0000_0000_0000_0000;
        const MEM_SHM_TRANSFER = 0b0100_0000_0000_0000_0000;

        const TIM_HP_CHRONO = 0b0001_0000_0000_0000_0000_0000;
        const CRY_KRNG      = 0b0010_0000_0000_0000_0000_0000;
    }
}

impl From<u32> for Capability {
    fn from(inval: u32) -> Capability {
        Capability::from_bits_retain(inval)
    }
}

#[cfg(feature = "cbindgen")]
#[no_mangle]
pub extern "C" fn capabilities_keep_me(a: Capability) {}
