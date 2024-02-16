#![no_std]
#![allow(non_camel_case_types)]


// pub const HANDLE_ID_SHIFT: u32 = 13;
// pub const HANDLE_ID_SIZE: u32 = 16;
// pub const HANDLE_ID_MASK: u32 = ((1 << HANDLE_ID_SIZE) - 1) << HANDLE_ID_SHIFT; // 0x7fff_8000;
// pub const HANDLE_FAMILY_SHIFT: u32 = HANDLE_ID_SIZE + HANDLE_ID_SHIFT;
// pub const HANDLE_FAMILY_SIZE: u32 = 3;
// pub const HANDLE_FAMILY_MASK: u32 = ((1 << HANDLE_FAMILY_SIZE) - 1) << HANDLE_FAMILY_SHIFT; // 0xe000_0000;

pub type devh_t = u32;
pub type taskh_t = u32;
pub type shmh_t = u32;
pub type dmah_t = u32;

#[cfg(feature = "cbindgen")]
#[no_mangle]
pub extern "C" fn handles_keep_me(
    c: devh_t,
    d: taskh_t,
    g: shmh_t,
    h: dmah_t,
) {
}
