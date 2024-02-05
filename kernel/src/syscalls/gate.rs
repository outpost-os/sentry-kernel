use crate::arch::*;
use capabilities::*;
use managers_bindings as mgr;
// use mgr::kstatus_K_ERROR_BADENTROPY;
use systypes::*;

pub type StackFramePointer = Option<*mut mgr::stack_frame_t>;

pub fn syscall_dispatch(syscall_number: u8, args: &[u32]) -> Result<StackFramePointer, Status> {
    match Syscall::try_from(syscall_number)? {
        Syscall::Exit => exit(args[0] as i32),
        Syscall::GetProcessHandle => get_process_handle(args[0]),
        Syscall::Yield => r#yield(),
        Syscall::Sleep => sleep(args[0], args[1]),
        Syscall::Start => start(args[0]),
        Syscall::MapDev => map(Resource::Dev(args[0])),
        Syscall::MapShm => map(Resource::Shm(args[0])),
        Syscall::UnmapDev => unmap(Resource::Dev(args[0])),
        Syscall::UnmapShm => unmap(Resource::Shm(args[0])),
        Syscall::SHMSetCredential => shm_set_credential(args[0], args[1], args[2]),
        Syscall::SendIPC => send_ipc(args[0], args[1] as u8),
        Syscall::SendSignal => send_signal(args[0], args[1]),
        Syscall::WaitForEvent => wait_for_event(args[0] as u8, args[1], args[2]),
        Syscall::ManageCPUSleep => manage_cpu_sleep(args[0]),
        Syscall::Alarm => alarm(args[0]),
        Syscall::GetRandom => get_random(),
        Syscall::GetCycle => get_cycle(args[0]),

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

enum Kstatus {
    KStatusOkay,
    KErrorBusy,
    KErrorInvParam,
    KErrorBadState,
    KErrorUnknown,
    KErrorBadClk,
    KErrorBadEntropy,
    KErrorNotReady,
    KErrorNoEnt,
    KErrorMemFail,
    KSecurityInvState,
    KSecurityCorruption,
    KSecurityLockdown,
    KSecurityFIPSCompliance,
    KSecurityIntegrity
}

impl TryFrom<EnumBinding> for Kstatus {
    type Error = Status;
    fn try_from(status: EnumBinding) -> Result<Kstatus, Self::Error> {
        let kstatus: Kstatus = match status {
            mgr::kstatus_K_STATUS_OKAY => Kstatus::KStatusOkay,
            mgr::kstatus_K_ERROR_BADCLK => Kstatus::KErrorBadClk,
            mgr::kstatus_K_ERROR_BADENTROPY => Kstatus::KErrorBadEntropy,
            mgr::kstatus_K_ERROR_BADSTATE => Kstatus::KErrorBadState,
            mgr::kstatus_K_ERROR_BUSY => Kstatus::KErrorBusy,
            mgr::kstatus_K_ERROR_INVPARAM => Kstatus::KErrorInvParam,
            mgr::kstatus_K_ERROR_MEMFAIL => Kstatus::KErrorMemFail,
            mgr::kstatus_K_ERROR_NOENT => Kstatus::KErrorNoEnt,
            mgr::kstatus_K_ERROR_NOTREADY => Kstatus::KErrorNotReady,
            mgr::kstatus_K_ERROR_UNKNOWN => Kstatus::KErrorUnknown,
            mgr::kstatus_K_SECURITY_CORRUPTION => Kstatus::KSecurityCorruption,
            mgr::kstatus_K_SECURITY_FIPSCOMPLIANCE => Kstatus::KSecurityFIPSCompliance,
            mgr::kstatus_K_SECURITY_INTEGRITY => Kstatus::KSecurityIntegrity,
            mgr::kstatus_K_SECURITY_INVSTATE => Kstatus::KSecurityInvState,
            mgr::kstatus_K_SECURITY_LOCKDOWN => Kstatus::KSecurityLockdown,
            _ => return Err(Status::Invalid),
        };
        Ok(kstatus)
    }
}

enum JobState {
    NotStarted,
    Ready,
    Sleeping,
    DeepSleeping,
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
            mgr::job_state_JOB_STATE_SLEEPING_DEEP => JobState::DeepSleeping,
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

struct TaskMeta<'a> {
    meta: &'a mgr::task_meta_t,
}

impl<'a> TaskMeta<'a> {
    fn current() -> Result<TaskMeta<'a>, Status> {
        let mut taskmeta: *const mgr::task_meta = core::ptr::null();
        if unsafe { mgr::mgr_task_get_metadata(sched_get_current(), &mut taskmeta) } != 0 {
            return Err(Status::Invalid);
        }
        Ok(TaskMeta {
            meta: unsafe { &*taskmeta },
        })
    }

    fn get_exchange_bytes(&self) -> &[u8] {
        unsafe {
            core::slice::from_raw_parts(
                self.meta.s_svcexchange as *const u8,
                mgr::CONFIG_SVC_EXCHANGE_AREA_LEN as usize,
            )
        }
    }

    fn get_exchange_bytes_mut(&mut self) -> &mut [u8] {
        unsafe {
            core::slice::from_raw_parts_mut(
                self.meta.s_svcexchange as *mut u8,
                mgr::CONFIG_SVC_EXCHANGE_AREA_LEN as usize,
            )
        }
    }

    /// Verify that a task possess a given capability
    fn can(self, capability: Capability) -> Result<TaskMeta<'a>, Status> {
        if !Capability::from(self.meta.capabilities).contains(capability) {
            return Err(Status::Denied);
        }
        Ok(self)
    }

    fn has_dev(self, dev: handles::devh_t) -> Result<TaskMeta<'a>, Status> {
        let declared_devs = &self.meta.devs[..self.meta.num_devs as usize];
        if !declared_devs.contains(&dev) {
            return Err(Status::Denied);
        }
        Ok(self)
    }

    fn has_shm(self, shm: handles::shmh_t) -> Result<TaskMeta<'a>, Status> {
        let declared_shms = &self.meta.shms[..self.meta.num_shm as usize];
        if !declared_shms.contains(&shm) {
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

impl Status {
    fn current() -> Result<Status, Status> {
        let mut sysret: Status = Status::NoneSense;
        let mut mgr_ret: Kstatus = Kstatus::K_ERROR_INVPARAM;
        if unsafe { mgr::mgr_task_get_sysreturn(sched_get_current(), &mut sysret) } != 0 {
            return Err(Status::Invalid);
        }
        sysret.try_into()
    }
    fn get(&mut self, job: mgr::taskh_t) -> Result<Status, Status> {
        let mut sysret: Status = Status::NoneSense;
        let mut mgr_ret: Kstatus = Kstatus::K_ERROR_INVPARAM;
        if unsafe { mgr::mgr_task_get_sysreturn(job, &mut sysret) } != 0 {
            return Err(Status::Invalid);
        }
        sysret.try_into()
    }

    fn set(&mut self, job: mgr::taskh_t, new_ret: Status) -> Result<Status, Status> {
        if unsafe { mgr::mgr_task_set_sysreturn(job, new_ret as EnumBinding) } != 0 {
            return Err(Status::Invalid);
        }
        Ok(Status::Ok)
    }

    fn clear(&mut self, job: mgr::taskh_t, new_ret: Status) -> Result<Status, Status> {
        if unsafe { mgr::mgr_task_clear_sysreturn(job) } != 0 {
            return Err(Status::Invalid);
        }
        Ok(Status::Ok)
    }
}

pub fn manage_cpu_sleep(mode_in: u32) -> Result<StackFramePointer, Status> {
    TaskMeta::current()?.can(Capability::SYS_POWER)?;

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
    let checked_text = core::str::from_utf8(&current_task.get_exchange_bytes()[..length])
        .map_err(|_| Status::Invalid)?;
    if unsafe { mgr::debug_rawlog(checked_text.as_ptr(), checked_text.len()) } != 0 {
        return Err(Status::Invalid);
    }
    Ok(None)
}

// Thin wrapper over `sched_get_current`. This function never fails
fn sched_get_current() -> handles::taskh_t {
    unsafe { mgr::sched_get_current() }
}

// Thin wrapper over `sched_elect`. This function never fails
fn sched_elect() -> handles::taskh_t {
    unsafe { mgr::sched_elect() }
}

// Safe wrapper over `mgr_task_get_sp`
fn task_get_sp(taskh: handles::taskh_t) -> Result<StackFramePointer, Status> {
    let mut sp: *mut mgr::stack_frame_t = core::ptr::null_mut();
    if unsafe { mgr::mgr_task_get_sp(taskh, &mut sp) } != 0 {
        return Err(Status::Invalid);
    }
    Ok(sp.into())
}

fn time_delay_add_signal(
    taskh: handles::taskh_t,
    delay_ms: u32,
    signal: handles::sigh_t,
) -> Result<Status, Status> {
    if unsafe { mgr::mgr_time_delay_add_signal(taskh, delay_ms, signal) } != 0 {
        return Err(Status::Busy);
    }
    Ok(Status::Ok)
}

fn time_delay_add_job(taskh: handles::taskh_t, duration_ms: u32) -> Result<Status, Status> {
    if unsafe { mgr::mgr_time_delay_add_job(taskh, duration_ms) } != 0 {
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

pub fn sleep(duration_ms: u32, sleep_mode: u32) -> Result<StackFramePointer, Status> {
    let mode = match SleepMode::try_from(sleep_mode)? {
        SleepMode::Shallow => JobState::Sleeping,
        SleepMode::Deep => JobState::DeepSleeping,
    };
    JobState::current()?.set(mode)?;
    time_delay_add_job(sched_get_current(), duration_ms)?;
    task_get_sp(sched_elect())
}

pub fn start(_process: u32) -> Result<StackFramePointer, Status> {
    Ok(None)
}

pub enum Resource {
    Dev(u32),
    Shm(u32),
}

pub fn map(resource: Resource) -> Result<StackFramePointer, Status> {
    let meta = TaskMeta::current()?;
    // Check:
    // - the requested device/shm was declared in the current task
    // - the device/shm's capabilities match the current task's capabilities
    match resource {
        Resource::Dev(devu) => {
            let dev = handles::devh_t::from(devu);
            meta.has_dev(dev)?.can(dev.get_dev_cap().into())?;

            // FIXME: check whether device is already mapped
            if unsafe { mgr::mgr_mm_map_device(dev) } != 0 {
                return Err(Status::Invalid);
            }
        }
        Resource::Shm(shmu) => {
            let shm = handles::shmh_t::from(shmu);
            meta.has_shm(shm)?.can(Capability::MEM_SHM_USE)?;
            // if unsafe { mgr::mgr_mm_map_shm(shm) } != 0 {
            //     return Err(Status::Invalid);
            // }
            todo!()
        }
    }
    Ok(None)
}

pub fn unmap(resource: Resource) -> Result<StackFramePointer, Status> {
    match resource {
        Resource::Dev(devu) => {
            let dev = handles::devh_t::from(devu);
            if unsafe { mgr::mgr_mm_unmap_device(dev) } != 0 {
                return Err(Status::Invalid);
            }
        }
        Resource::Shm(_shmu) => {
            return Err(Status::Invalid);
        }
    }
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

pub fn alarm(timeout_ms: u32) -> Result<StackFramePointer, Status> {
    let current_job = sched_get_current();

    let mut signal = handles::sigh_t::default();
    signal.set_id(Signal::Alarm as u32);
    signal.set_family(mgr::HANDLE_SIGNAL);
    signal.set_source(current_job.get_id());

    time_delay_add_signal(current_job, timeout_ms, signal)?;
    Ok(None)
}

fn get_random() -> Result<StackFramePointer, Status> {
    let mut current_task = TaskMeta::current()?.can(Capability::CRY_KRNG)?;

    let mut rand = 0u32;
    if unsafe { mgr::mgr_security_entropy_generate(&mut rand) } != 0 {
        return Err(Status::Invalid);
    }
    current_task.get_exchange_bytes_mut()[..4].copy_from_slice(&rand.to_ne_bytes());
    Ok(None)
}

fn get_cycle(precision: u32) -> Result<StackFramePointer, Status> {
    let mut current_task = TaskMeta::current()?;
    let precision = Precision::try_from(precision)?;

    let cycles = match precision {
        Precision::Cycle => {
            current_task = current_task.can(Capability::TIM_HP_CHRONO)?;
            unsafe { mgr::mgr_time_get_cycle() }
        }
        Precision::Nanoseconds => unsafe { mgr::mgr_time_get_nanoseconds() },
        Precision::Microseconds => unsafe { mgr::mgr_time_get_microseconds() },
        Precision::Milliseconds => unsafe { mgr::mgr_time_get_milliseconds() },
    };
    current_task.get_exchange_bytes_mut()[..8].copy_from_slice(&cycles.to_ne_bytes());
    Ok(None)
}
