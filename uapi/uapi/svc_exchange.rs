use crate::systypes::{EraseMode, EraseType, Status};

pub const SVC_EXCH_AREA_LEN: usize = 128; // TODO: replace by CONFIG-defined value

/// This SVC exchange area is always defined for all apps, so it is declared
/// here in UAPI.rs. `copy_from_user` and `copy_to_user` functions are provided
/// for easy access to this area.
#[cfg_attr(test, no_mangle)]
#[link_section = ".svcexchange"]
pub static mut SVC_EXCHANGE_AREA: [u8; SVC_EXCH_AREA_LEN] = [0u8; SVC_EXCH_AREA_LEN];

unsafe fn check_bounds(pointer: *const u8, length: usize) -> Result<(), ()> {
    let svcexc = SVC_EXCHANGE_AREA.as_ptr();
    let svcexc_end = svcexc.add(SVC_EXCH_AREA_LEN);

    // buffer starts in the middle of the exchange area, abort
    if pointer >= svcexc && pointer <= svcexc_end {
        return Err(());
    }

    // buffer ends in the exchange area, abort
    // Note: this is unlikely to happen if `svc_exchange` is always assumed to be at
    // the beginning of RAM
    let buffer_end = pointer.add(length);
    if buffer_end >= svcexc && buffer_end <= svcexc_end {
        return Err(());
    }

    // exchange area is contained within the buffer, abort
    if pointer <= svcexc && buffer_end >= svcexc_end {
        return Err(());
    }

    Ok(())
}

/// Copy data to svc_exchange area
///
/// # Safety
///
/// Callers must ensure memory pointed to by `from` up to `from + length` belongs to
/// a valid variable.
#[no_mangle]
pub unsafe extern "C" fn copy_from_user(from: *const u8, length: usize) -> Status {
    if check_bounds(from, length).is_err() {
        return Status::Invalid;
    }
    core::ptr::copy_nonoverlapping(
        from,
        SVC_EXCHANGE_AREA.as_mut_ptr(),
        length.min(SVC_EXCH_AREA_LEN),
    );
    Status::Ok
}

/// Copy data from svc_exchange area to user-controlled buffer
///
/// # Safety
///
/// Callers must ensure memory pointed to by `from` up to `from + length` belongs to
/// a valid variable.
/// SVC Exchange area content is not cleared after copy
#[no_mangle]
pub unsafe extern "C" fn copy_to_user(to: *mut u8, length: usize) -> Status {
    if check_bounds(to, length).is_err() {
        return Status::Invalid;
    }
    core::ptr::copy_nonoverlapping(
        SVC_EXCHANGE_AREA.as_ptr(),
        to,
        length.min(SVC_EXCH_AREA_LEN),
    );
    Status::Ok
}

/// SVC Exchange area content is cleared after copy
///
/// The cleaning part can't be done in the copy_to_user impl as
/// userspace may copy svcechange() data with consecutive calls
/// (e.g. when reading the header first, then the overall content)
#[no_mangle]
pub extern "C" fn clean_svcexchange(erasetype: EraseType, mode: EraseMode) -> Status {
    match erasetype {
        EraseType::Zeroify => (),
        _ => return Status::Invalid,
    }
    match mode {
        EraseMode::UserErase => (),
        _ => return Status::Invalid,
    }
    unsafe {
        core::ptr::write_volatile(&mut SVC_EXCHANGE_AREA as *mut [u8; SVC_EXCH_AREA_LEN], [0; SVC_EXCH_AREA_LEN]);
    }
    Status::Ok
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

    #[test]
    fn invalid_src() {
        unsafe {
            assert_eq!(
                copy_from_user(SVC_EXCHANGE_AREA.as_ptr(), 4),
                Status::Invalid
            );
        }
    }

    #[test]
    fn invalid_dest() {
        let string = [b'z'; 4];
        unsafe {
            copy_from_user(string.as_ptr(), string.len());
            assert_eq!(
                copy_to_user(SVC_EXCHANGE_AREA.as_mut_ptr(), string.len()),
                Status::Invalid
            );
        }
    }
}
