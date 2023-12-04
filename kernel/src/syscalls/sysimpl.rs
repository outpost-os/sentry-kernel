use managers_bindings as mgr;
use systypes::*;

use crate::arch::*;

#[repr(i32)]
#[allow(dead_code)]
#[allow(clippy::unnecessary_cast)] // TODO: potentially fixed using underlying enums with C23
enum Capability {
    DevBuses = mgr::sentry_capability_CAP_DEV_BUSES as i32,
    DevIO = mgr::sentry_capability_CAP_DEV_IO as i32,
    DevDMA = mgr::sentry_capability_CAP_DEV_DMA as i32,
    DevAnalog = mgr::sentry_capability_CAP_DEV_ANALOG as i32,
    DevTimer = mgr::sentry_capability_CAP_DEV_TIMER as i32,
    DevStorage = mgr::sentry_capability_CAP_DEV_STORAGE as i32,
    DevCrypto = mgr::sentry_capability_CAP_DEV_CRYPTO as i32,
    DevClock = mgr::sentry_capability_CAP_DEV_CLOCK as i32,
    SysUpgrade = mgr::sentry_capability_CAP_SYS_UPGRADE as i32,
    SysPower = mgr::sentry_capability_CAP_SYS_POWER as i32,
    SysProcStart = mgr::sentry_capability_CAP_SYS_PROCSTART as i32,
    MemSHMOwn = mgr::sentry_capability_CAP_MEM_SHM_OWN as i32,
    MemSHMUse = mgr::sentry_capability_CAP_MEM_SHM_USE as i32,
    MemSHMTransfer = mgr::sentry_capability_CAP_MEM_SHM_TRANSFER as i32,
    TimHPChrono = mgr::sentry_capability_CAP_TIM_HP_CHRONO as i32,
    CryKRNG = mgr::sentry_capability_CAP_CRY_KRNG as i32,
}

#[derive(Clone, Copy)]
struct TaskMeta {
    meta: mgr::task_meta_t,
}

impl TaskMeta {
    fn current() -> Result<TaskMeta, DispatchError> {
        let mut taskmeta: *const mgr::task_meta = core::ptr::null();
        if unsafe { mgr::mgr_task_get_metadata(mgr::sched_get_current(), &mut taskmeta) } != 0 {
            return Err(DispatchError::IllegalValue);
        }
        Ok(TaskMeta {
            meta: unsafe { *taskmeta },
        })
    }

    #[allow(dead_code)]
    fn exchange_bytes(&self) -> &[u8] {
        unsafe {
            core::slice::from_raw_parts(
                self.meta.s_svcexchange as *const u8,
                mgr::CONFIG_SVC_EXCHANGE_AREA_LEN as usize,
            )
        }
    }

    fn can(self, capability: Capability) -> Result<TaskMeta, DispatchError> {
        if self.meta.capabilities & capability as u32 == 0 {
            return Err(DispatchError::InsufficientCapabilities);
        }
        Ok(self)
    }
}

pub fn manage_cpu_sleep(mode_in: u32) -> Result<Status, DispatchError> {
    TaskMeta::current()?.can(Capability::SysPower)?;

    match CPUSleep::try_from(mode_in)? {
        CPUSleep::AllowSleep => (),
        CPUSleep::ForbidSleep => (),
        CPUSleep::WaitForEvent => __wfe(),
        CPUSleep::WaitForInterrupt => __wfi(),
    }
    Ok(Status::Ok)
}

#[cfg(not(CONFIG_BUILD_TARGET_RELEASE))]
pub fn log_rs(length: usize) -> Result<Status, DispatchError> {
    let current_task = TaskMeta::current()?;
    let cstr_text = core::ffi::CStr::from_bytes_with_nul(&current_task.exchange_bytes()[..length])
        .map_err(|_| DispatchError::IllegalValue)?;
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
