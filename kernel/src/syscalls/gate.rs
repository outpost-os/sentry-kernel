use crate::arch::*;
use managers_bindings as mgr;
use systypes::*;

pub type StackFramePointer = Option<*mut mgr::stack_frame_t>;

pub fn syscall_dispatch(syscall_number: u8, args: &[u32]) -> Result<StackFramePointer, Status> {
    match Syscall::try_from(syscall_number)? {
        Syscall::Exit => exit(args[0] as i32),
        Syscall::GetProcessHandle => get_process_handle(args[0]),
        Syscall::Yield => r#yield(),
        Syscall::Sleep => sleep(args[0], args[1]),
        Syscall::Start => start(args[0]),
        Syscall::Map => map(args[0]),
        Syscall::Unmap => unmap(args[0]),
        Syscall::SHMSetCredential => shm_set_credential(args[0], args[1], args[2]),
        Syscall::SendIPC => send_ipc(args[0], args[1] as u8),
        Syscall::SendSignal => send_signal(args[0], args[1]),
        Syscall::WaitForEvent => wait_for_event(args[0] as u8, args[1], args[2]),
        Syscall::ManageCPUSleep => manage_cpu_sleep(args[0]),
        Syscall::Alarm => alarm(args[0]),

        #[cfg(not(CONFIG_BUILD_TARGET_RELEASE))]
        Syscall::Log => log_rs(args[0] as usize),

        #[cfg(CONFIG_BUILD_TARGET_RELEASE)]
        Syscall::Log => Ok(None),
    }
}

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
        if unsafe { mgr::mgr_task_get_metadata(sched_get_current(), &mut taskmeta) } != 0 {
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
        if unsafe { mgr::mgr_task_get_state(sched_get_current(), &mut taskstate) } != 0 {
            return Err(Status::Denied);
        }
        taskstate.try_into()
    }

    fn set(&mut self, new_state: JobState) -> Result<Status, Status> {
        if unsafe { mgr::mgr_task_set_state(sched_get_current(), new_state as EnumBinding) } != 0 {
            return Err(Status::Invalid);
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
    let checked_text = core::str::from_utf8(&current_task.exchange_bytes()[..length])
        .map_err(|_| Status::Invalid)?;
    if unsafe { mgr::debug_rawlog(checked_text.as_ptr(), checked_text.len()) } != 0 {
        return Err(Status::Invalid);
    }
    Ok(None)
}

// Thin wrapper over `sched_get_current`. This function never fails
fn sched_get_current() -> mgr::task_handle {
    unsafe { mgr::sched_get_current() }
}

// Thin wrapper over `sched_elect`. This function never fails
fn sched_elect() -> mgr::task_handle {
    unsafe { mgr::sched_elect() }
}

// Safe wrapper over `mgr_task_get_sp`
fn task_get_sp(taskh: mgr::task_handle) -> Result<StackFramePointer, Status> {
    let mut sp: *mut mgr::stack_frame_t = core::ptr::null_mut();
    if unsafe { mgr::mgr_task_get_sp(taskh, &mut sp) } != 0 {
        return Err(Status::Invalid);
    }
    Ok(sp.into())
}

fn time_delay_add_signal(
    taskh: mgr::task_handle,
    delay_ms: u32,
    signal: mgr::sigh_t,
) -> Result<Status, Status> {
    if unsafe { mgr::mgr_time_delay_add_signal(taskh, delay_ms, signal) } != 0 {
        return Err(Status::Busy);
    }
    Ok(Status::Ok)
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

#[allow(clippy::unnecessary_cast)] // `as u32` only necessary on msvc toolchains
pub fn alarm(timeout_ms: u32) -> Result<StackFramePointer, Status> {
    let current_job = sched_get_current();

    let mut signal = mgr::sigh_t::default();
    signal.set_id(mgr::signal_SIGNAL_ALARM as u32);
    signal.set_family(mgr::HANDLE_SIGNAL);
    signal.set_source(current_job.id());

    time_delay_add_signal(current_job, timeout_ms, signal)?;
    Ok(None)
}
