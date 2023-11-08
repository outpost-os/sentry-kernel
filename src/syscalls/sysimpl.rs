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
