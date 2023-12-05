use crate::arch::*;
use crate::gate::StackFramePointer;
use managers_bindings as mgr;
use systypes::*;

#[cfg(windows)]
type EnumBinding = i32;
#[cfg(not(windows))]
type EnumBinding = u32;

enum Capability {
    DevBuses,
    DevIO,
    DevDMA,
    DevAnalog,
    DevTimer,
    DevStorage,
    DevCrypto,
    DevClock,
    SysUpgrade,
    SysPower,
    SysProcStart,
    MemSHMOwn,
    MemSHMUse,
    MemSHMTransfer,
    TimHPChrono,
    CryKRNG,
}

impl TryFrom<EnumBinding> for Capability {
    type Error = Status;
    fn try_from(cap: EnumBinding) -> Result<Capability, Self::Error> {
        let capability = match cap {
            mgr::sentry_capability_CAP_DEV_BUSES => Capability::DevBuses,
            mgr::sentry_capability_CAP_DEV_IO => Capability::DevIO,
            mgr::sentry_capability_CAP_DEV_DMA => Capability::DevDMA,
            mgr::sentry_capability_CAP_DEV_ANALOG => Capability::DevAnalog,
            mgr::sentry_capability_CAP_DEV_TIMER => Capability::DevTimer,
            mgr::sentry_capability_CAP_DEV_STORAGE => Capability::DevStorage,
            mgr::sentry_capability_CAP_DEV_CRYPTO => Capability::DevCrypto,
            mgr::sentry_capability_CAP_DEV_CLOCK => Capability::DevClock,
            mgr::sentry_capability_CAP_SYS_UPGRADE => Capability::SysUpgrade,
            mgr::sentry_capability_CAP_SYS_POWER => Capability::SysPower,
            mgr::sentry_capability_CAP_SYS_PROCSTART => Capability::SysProcStart,
            mgr::sentry_capability_CAP_MEM_SHM_OWN => Capability::MemSHMOwn,
            mgr::sentry_capability_CAP_MEM_SHM_USE => Capability::MemSHMUse,
            mgr::sentry_capability_CAP_MEM_SHM_TRANSFER => Capability::MemSHMTransfer,
            mgr::sentry_capability_CAP_TIM_HP_CHRONO => Capability::TimHPChrono,
            mgr::sentry_capability_CAP_CRY_KRNG => Capability::CryKRNG,
            _ => return Err(Status::Invalid),
        };
        Ok(capability)
    }
}

enum JobState {
    NotStarted,
    Ready,
    Sleeping,
    SleepingDeep,
    Fault,
    Security,
    Aborting,
    Finished,
    IPCSendBlocked,
    WaitForEvent,
}

impl TryFrom<EnumBinding> for JobState {
    type Error = Status;
    fn try_from(state: EnumBinding) -> Result<JobState, Self::Error> {
        let thread_state = match state {
            mgr::job_state_JOB_STATE_NOTSTARTED => JobState::NotStarted,
            mgr::job_state_JOB_STATE_READY => JobState::Ready,
            mgr::job_state_JOB_STATE_SLEEPING => JobState::Sleeping,
            mgr::job_state_JOB_STATE_SLEEPING_DEEP => JobState::SleepingDeep,
            mgr::job_state_JOB_STATE_SECURITY => JobState::Security,
            mgr::job_state_JOB_STATE_ABORTING => JobState::Aborting,
            mgr::job_state_JOB_STATE_FAULT => JobState::Fault,
            mgr::job_state_JOB_STATE_FINISHED => JobState::Finished,
            mgr::job_state_JOB_STATE_IPC_SEND_BLOCKED => JobState::IPCSendBlocked,
            mgr::job_state_JOB_STATE_WAITFOREVENT => JobState::WaitForEvent,
            _ => return Err(Status::Invalid),
        };
        Ok(thread_state)
    }
}

#[derive(Clone, Copy)]
struct TaskMeta {
    meta: mgr::task_meta_t,
}

impl TaskMeta {
    fn current() -> Result<TaskMeta, Status> {
        let mut taskmeta: *const mgr::task_meta = core::ptr::null();
        if unsafe { mgr::mgr_task_get_metadata(mgr::sched_get_current(), &mut taskmeta) } != 0 {
            return Err(Status::Invalid);
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

    fn can(self, capability: Capability) -> Result<TaskMeta, Status> {
        if self.meta.capabilities & capability as u32 == 0 {
            return Err(Status::Denied);
        }
        Ok(self)
    }
}

impl JobState {
    fn current() -> Result<JobState, Status> {
        let mut taskstate: mgr::job_state_t = 0;
        if unsafe { mgr::mgr_task_get_state(mgr::sched_get_current(), &mut taskstate) } != 0 {
            return Err(Status::Denied);
        }
        taskstate.try_into()
    }

    fn set(&mut self, new_state: JobState) -> Result<Status, Status> {
        let status =
            unsafe { mgr::mgr_task_set_state(mgr::sched_get_current(), new_state as EnumBinding) };
        if status != 0 {
            return Err((status as u32).into());
        }
        Ok(Status::Ok)
    }
}

pub fn manage_cpu_sleep(mode_in: u32) -> Result<StackFramePointer, Status> {
    TaskMeta::current()?.can(Capability::SysPower)?;

    match CPUSleep::try_from(mode_in)? {
        CPUSleep::AllowSleep => (),
        CPUSleep::ForbidSleep => (),
        CPUSleep::WaitForEvent => __wfe(),
        CPUSleep::WaitForInterrupt => __wfi(),
    }
    Ok(None)
}

#[cfg(not(CONFIG_BUILD_TARGET_RELEASE))]
pub fn log_rs(length: usize) -> Result<StackFramePointer, Status> {
    let current_task = TaskMeta::current()?;
    let cstr_text = core::ffi::CStr::from_bytes_with_nul(&current_task.exchange_bytes()[..length])
        .map_err(|_| Status::Invalid)?;
    let checked_text = cstr_text.to_str().map_err(|_| Status::Invalid)?;
    let status = unsafe { mgr::debug_rawlog(checked_text.as_ptr(), checked_text.len()) };
    if status != 0 {
        return Err(status.into());
    }
    Ok(None)
}


fn sched_elect() -> mgr::task_handle {
    unsafe { mgr::sched_elect() }
}

fn task_get_sp(taskh: mgr::task_handle) -> Result<StackFramePointer, Status> {
    let mut sp: *mut mgr::stack_frame_t = core::ptr::null_mut();
    let status = unsafe { mgr::mgr_task_get_sp(taskh, &mut sp) } as u32;
    if status != 0 {
        return Err(status.into());
    }
    Ok(sp.into())
}

pub fn exit(status: i32) -> Result<StackFramePointer, Status> {
    JobState::current()?.set(if Status::from(status as u32) == Status::Ok {
        JobState::Finished
    } else {
        JobState::Aborting
    })?;
    task_get_sp(sched_elect())
}

pub fn get_process_handle(_process: u32) -> Result<StackFramePointer, Status> {
    Ok(None)
}

pub fn r#yield() -> Result<StackFramePointer, Status> {
    task_get_sp(sched_elect())
}

pub fn sleep(_duration_ms: u32, _sleep_mode: u32) -> Result<StackFramePointer, Status> {
    Ok(None)
}

pub fn start(_process: u32) -> Result<StackFramePointer, Status> {
    Ok(None)
}

pub fn map(_resource: u32) -> Result<StackFramePointer, Status> {
    Ok(None)
}

pub fn unmap(_resource: u32) -> Result<StackFramePointer, Status> {
    Ok(None)
}

pub fn shm_set_credential(
    _resource: u32,
    _id: u32,
    _shm_perm: u32,
) -> Result<StackFramePointer, Status> {
    Ok(None)
}

pub fn send_ipc(_resource_type: u32, _length: u8) -> Result<StackFramePointer, Status> {
    Ok(None)
}

pub fn send_signal(_resource_type: u32, _signal_type: u32) -> Result<StackFramePointer, Status> {
    Ok(None)
}

pub fn wait_for_event(
    _event_type_mask: u8,
    _resoucer_handle: u32,
    _timeout: u32,
) -> Result<StackFramePointer, Status> {
    Ok(None)
}
