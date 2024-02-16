#[cfg(not(target_arch = "x86_64"))]
use core::arch::asm;
use handles::*;
use systypes::*;

/// Exiting the process.
///
/// POSIX upper layers (libshield): void _exit(int status);
#[no_mangle]
pub extern "C" fn sys_exit(status: i32) -> Status {
    syscall!(Syscall::Exit, status as u32).into()
}

/// Get global identifier for a given process label
///
/// This mechanism allows respawn detection, as the label is fixed but the resource identifier
/// is regenerated.
/// A process is a resource like any other and communicating with it requires to get
/// back its resource handle from its label.
///
/// POSIX upper layer(s): N/A
#[no_mangle]
pub extern "C" fn sys_get_process_handle(process: ProcessLabel) -> Status {
    syscall!(Syscall::GetProcessHandle, u32::from(process)).into()
}

/// Release the processor before the end of the current quantum.
/// Allows triggering a schedule() even if not in the process's central blocking point
///
/// POSIX upper layer(s): N/A
#[no_mangle]
pub extern "C" fn sys_yield() -> Status {
    syscall!(Syscall::Yield).into()
}

/// Sleep for a given amount of time
///
/// POSIX upper layer(s): sleep(3), usleep(3)
#[no_mangle]
pub extern "C" fn sys_sleep(duration_ms: SleepDuration, mode: SleepMode) -> Status {
    syscall!(Syscall::Sleep, u32::from(duration_ms), u32::from(mode)).into()
}

/// Start another task, if capability added and other process allowed to be started by us
///
/// - POSIX upper layer(s): execv()
#[no_mangle]
pub extern "C" fn sys_start(process: ProcessLabel) -> Status {
    syscall!(Syscall::Start, u32::from(process)).into()
}

///  Map a mappable device.
///
/// POSIX upper layer(s): mmap(2)
///   * addr can be null or set to ressource addr
///   * fd must be equal to ressource handle
///   * prot, offset and flags are ignored for now
#[no_mangle]
pub extern "C" fn sys_map_dev(dev: devh_t) -> Status {
    syscall!(Syscall::MapDev, dev).into()
}

///  Map a mappable SHM.
///
/// POSIX upper layer(s): shmget(2) (key == handle)
#[no_mangle]
pub extern "C" fn sys_map_shm(shm: shmh_t) -> Status {
    syscall!(Syscall::MapShm, shm).into()
}

/// Unmap a mapped device.
///
/// POSIX upper layer(s): munmap(2)
///   addr must match the ressource addr (ressource handle to be found in userspace from the addr?)
///   length must match the ressource size
#[no_mangle]
pub extern "C" fn sys_unmap_dev(dev: devh_t) -> Status {
    syscall!(Syscall::UnmapDev, dev).into()
}

/// Unmap a mapped device.
///
/// POSIX upper layer(s): TBD
#[no_mangle]
pub extern "C" fn sys_unmap_shm(shm: shmh_t) -> Status {
    syscall!(Syscall::UnmapShm, shm).into()
}

/// Set SHM permissions. shm_open() is considered automatic as declared in dtsi, handle is generated.
///
/// POSIX upper layer(s): shmctl(3),
#[no_mangle]
pub extern "C" fn sys_shm_set_credential(
    resource: u32,
    id: ProcessID,
    shm_perm: SHMPermission,
) -> Status {
    syscall!(
        Syscall::SHMSetCredential,
        resource,
        id,
        u32::from(shm_perm)
    )
    .into()
}

/// Send events to another process
#[no_mangle]
pub extern "C" fn sys_send_ipc(resource_type: ResourceType, length: u8) -> Status {
    syscall!(Syscall::SendIPC, resource_type as u32, length as u32).into()
}

/// Send a signal to another process
#[no_mangle]
pub extern "C" fn sys_send_signal(resource_type: ResourceType, signal_type: Signal) -> Status {
    syscall!(
        Syscall::SendSignal,
        resource_type as u32,
        signal_type as u32
    )
    .into()
}

/// Wait for input event. Single active blocking syscall.
///
/// This syscall holds the current thread as long as none of the event requested
/// in the given event mask is received.
///
/// The event source (a device for an interrupt, a PID for an IPC or signal) can be set.
/// Setting the source to 0 means that any source is allowed.
///
/// If received, event informations are set in the task SVC data
/// structure and the function returns `Status::Ok`.
///
/// This function must be the single blocking point of the function (excepting
/// sleep() case)
///
/// POSIX upper layer(s): select(2), poll(2)
#[no_mangle]
pub extern "C" fn sys_wait_for_event(
    event_type_mask: u8,
    resource_handle: u32,
    timeout: u32,
) -> Status {
    syscall!(
        Syscall::WaitForEvent,
        u32::from(event_type_mask),
        resource_handle,
        timeout
    )
    .into()
}

/// Configure the CPU's sleep behaviour.
///
/// The `mode` parameters toggles between the two traditional wake-up
/// modes for ARM CPUs:
/// - wait for interrupt (`wfi`)
/// - wait for event (`wfe`)
///
/// it also accepts two other mode values that enable or prevent the
/// CPU from sleeping.
#[no_mangle]
pub extern "C" fn sys_manage_cpu_sleep(mode: CPUSleep) -> Status {
    syscall!(Syscall::ManageCPUSleep, u32::from(mode)).into()
}

/// Send a SIGALRM signal to the task after `timeout_ms` milliseconds.
#[no_mangle]
pub extern "C" fn sys_alarm(timeout_ms: u32) -> Status {
    syscall!(Syscall::Alarm, timeout_ms).into()
}

/// Send a message from the current task's 'svc_exchange area' through
/// the UART.
#[no_mangle]
pub extern "C" fn sys_log(length: usize) -> Status {
    syscall!(Syscall::Log, length as u32).into()
}

/// Retrieve a random number (u32)
#[no_mangle]
pub extern "C" fn sys_get_random() -> Status {
    syscall!(Syscall::GetRandom).into()
}

/// Retrieve number of cycles since boot (u64)
#[no_mangle]
pub extern "C" fn sys_get_cycle(precision: Precision) -> Status {
    syscall!(Syscall::GetCycle, precision as u32).into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn syscall_enum() {
        for syscall_num in 0..32 {
            match Syscall::try_from(syscall_num) {
                Ok(sysn) => {
                    assert_eq!(sysn as u8, syscall_num); // ensure roundtrip loops
                }
                Err(_) => (),
            }
        }
    }

    #[test]
    fn basic_sleep() {
        assert_eq!(
            sys_sleep(SleepDuration::D1ms, SleepMode::Shallow),
            Status::Ok
        );
    }

    #[test]
    fn basic_start() {
        assert_eq!(sys_start(ProcessLabel::Label0), Status::Ok);
    }

    #[test]
    fn basic_yield() {
        assert_eq!(sys_yield(), Status::Ok);
    }

    #[test]
    fn basic_exit() {
        assert_eq!(sys_exit(1), Status::Ok);
    }

    #[test]
    #[should_panic]
    fn invalid_status() {
        assert_eq!(sys_exit(0xaaaa), Status::Ok);
    }
}
