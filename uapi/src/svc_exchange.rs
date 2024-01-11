pub const SVC_EXCH_AREA_LEN: usize = 128; // TODO: replace by CONFIG-defined value

/// This SVC exchange area is always defined for all apps, so it is declared
/// here in UAPI.rs. `copy_from_user` and `copy_to_user` functions are provided
/// for easy access to this area.
#[link_section = ".svcexchange"]
pub static mut SVC_EXCHANGE_AREA: [u8; SVC_EXCH_AREA_LEN] = [0u8; SVC_EXCH_AREA_LEN];

/// Copy data to svc_exchange area
///
/// # Safety
///
/// Callers must ensure memory pointed to by `from` up to `from + length` belongs to
/// a valid variable.
#[no_mangle]
pub unsafe extern "C" fn copy_from_user(from: *const u8, length: usize) {
    core::ptr::copy(
        from,
        SVC_EXCHANGE_AREA.as_mut_ptr(),
        length.min(SVC_EXCH_AREA_LEN),
    )
}

/// Copy data from svc_exchange area to user-controlled buffer
///
/// # Safety
///
/// Callers must ensure memory pointed to by `from` up to `from + length` belongs to
/// a valid variable.
#[no_mangle]
pub unsafe extern "C" fn copy_to_user(to: *mut u8, length: usize) {
    core::ptr::copy(
        SVC_EXCHANGE_AREA.as_ptr(),
        to,
        length.min(SVC_EXCH_AREA_LEN),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn back_to_back_copy() {
        let string = [b'z'; 100];
        let mut res = [b'a'; 100];
        unsafe {
            copy_from_user(string.as_ptr(), string.len());
            copy_to_user(res.as_mut_ptr(), string.len());
        }
        assert_eq!(res, string);
    }

    #[test]
    fn truncated_copy() {
        let string = [b'z'; 156];
        let mut res = [b'a'; 128];
        unsafe {
            copy_from_user(string.as_ptr(), string.len());
            copy_to_user(res.as_mut_ptr(), string.len());
        }
        assert_eq!(&res[..], &string[..128]);
    }
}
