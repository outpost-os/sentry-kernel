use managers_bindings as mgr;
use systypes::*;

use crate::arch::*;

fn check_cap(capability: mgr::sentry_capability_t) -> bool {
    let cap;
    unsafe {
        let mut taskmeta: *const mgr::task_meta = core::ptr::null();
        cap = mgr::mgr_task_get_metadata(mgr::sched_get_current(), &mut taskmeta);
    }
    cap & capability != 0
}

pub fn manage_cpu_sleep(mode_in: u32) -> Result<Status, DispatchError> {
    if !check_cap(mgr::sentry_capability_CAP_SYS_POWER) {
        return Err(DispatchError::InsufficientCapabilities);
    }

    match CPUSleep::try_from(mode_in)? {
        CPUSleep::AllowSleep => (),
        CPUSleep::ForbidSleep => (),
        CPUSleep::WaitForEvent => __wfe(),
        CPUSleep::WaitForInterrupt => __wfi(),
    }
    Ok(Status::Ok)
}

#[cfg(debug_assertions)]
/// # Safety
/// We can only make sure this is not a null pointer. We have no way of
/// verifying the presence of a nul terminator within appropriate bounds.
pub unsafe fn log_rs(text: *const i8) -> Result<Status, DispatchError> {
    if !check_cap(mgr::sentry_capability_CAP_DEV_IO) {
        return Err(DispatchError::InsufficientCapabilities);
    }
    if text.is_null() {
        return Err(DispatchError::IllegalValue);
    }

    let cstr_text = core::ffi::CStr::from_ptr(text);
    let checked_text = cstr_text
        .to_str()
        .map_err(|_| DispatchError::IllegalValue)?;
    println!("{}", checked_text);
    Ok(Status::Ok)
}

#[no_mangle]
extern "C" fn exit(_status: i32) -> u32 {
    0
}

#[no_mangle]
extern "C" fn get_process_handle(_process: u32) -> u32 {
    0
}

#[no_mangle]
extern "C" fn r#yield() -> u32 {
    0
}

#[no_mangle]
extern "C" fn sleep(_duration_ms: u32, _sleep_mode: u32) -> u32 {
    0
}

#[no_mangle]
extern "C" fn start(_process: u32) -> u32 {
    0
}

#[no_mangle]
extern "C" fn map(_resource: u32) -> u32 {
    0
}

#[no_mangle]
extern "C" fn unmap(_resource: u32) -> u32 {
    0
}

#[no_mangle]
extern "C" fn shm_set_credential(_resource: u32, _id: u32, _shm_perm: u32) -> u32 {
    0
}

#[no_mangle]
extern "C" fn send_ipc(_resource_type: u32, _length: u8) -> u32 {
    0
}

#[no_mangle]
extern "C" fn send_signal(_resource_type: u32, _signal_type: u32) -> u32 {
    0
}

#[no_mangle]
extern "C" fn wait_for_event(_event_type_mask: u8, _resoucer_handle: u32, _timeout: u32) -> u32 {
    0
}
