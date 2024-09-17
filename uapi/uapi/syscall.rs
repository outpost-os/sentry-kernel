// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#[cfg(not(target_arch = "x86_64"))]
use core::arch::asm;
use crate::systypes::*;

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
    syscall!(Syscall::GetProcessHandle, process).into()
}

/// Get global identifier for a given shm label
///
/// This mechanism allows respawn detection, as the label is fixed but the resource identifier
/// is regenerated.
/// A shm is a resource like any other and manipulating it requires to get
/// back its resource handle from its label.
///
/// POSIX upper layer(s): N/A
#[no_mangle]
pub extern "C" fn sys_get_shm_handle(shm: ShmLabel) -> Status {
    syscall!(Syscall::GetShmHandle, shm).into()
}

/// Get global identifier for a given shm label
///
/// This mechanism allows respawn detection, as the label is fixed but the resource identifier
/// is regenerated.
/// A shm is a resource like any other and manipulating it requires to get
/// back its resource handle from its label.
///
/// POSIX upper layer(s): N/A
#[no_mangle]
pub extern "C" fn sys_get_dma_stream_handle(stream: StreamLabel) -> Status {
    syscall!(Syscall::GetDmaStreamHandle, stream).into()
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
    syscall!(Syscall::Start, process).into()
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
    shm: shmh_t,
    id: taskh_t,
    shm_perm: u32,
) -> Status {
    syscall!(Syscall::SHMSetCredential, shm, id, shm_perm).into()
}

/// Send events to another process
///
/// # description
///
/// `sys_send_ipc()` is a blocking syscall. The current job is blocked and will
/// be eligible again only if:
///
///    * the targetted task job reads the IPC content
///    * the targetted task job terminates (even without reading the IPC content)
///
/// In the later case, the syscall return code is STATUS_BROKENPIPE.
/// There is no timeout notion in IPC emission.
///
/// # examples
///
/// C implementation usage:
/// ```
/// if (sys_send_ipc(target_taskh, ipc_len) == STATUS_BROKENPIPE) {
///   // react to target failure
/// }
/// ```
///
/// Rust implementation usage:
/// ```
/// uapi::send_ipc(TargetTaskh, IpcLen)?continue_here;
/// ```
#[no_mangle]
pub extern "C" fn sys_send_ipc(resource: u32, length: u8) -> Status {
    syscall!(Syscall::SendIPC, resource, length as u32).into()
}

/// Send a signal to another process
#[no_mangle]
pub extern "C" fn sys_send_signal(resource: u32, signal_type: Signal) -> Status {
    syscall!(Syscall::SendSignal, resource, signal_type as u32).into()
}

/// get value of given GPIO associated to given  device ressource
#[no_mangle]
pub extern "C" fn sys_gpio_get(resource: u32, io: u8) -> Status {
    syscall!(Syscall::GpioGet, resource, io as u32).into()
}

/// set value of given GPIO associated to given  device ressource
#[no_mangle]
pub extern "C" fn sys_gpio_set(resource: u32, io: u8, val: bool) -> Status {
    syscall!(Syscall::GpioSet, resource, io as u32, val as u32).into()
}

/// reset value of given GPIO associated to given  device ressource
#[no_mangle]
pub extern "C" fn sys_gpio_reset(resource: u32, io: u8) -> Status {
    syscall!(Syscall::GpioReset, resource, io as u32).into()
}

/// toggle value of given GPIO associated to given  device ressource
#[no_mangle]
pub extern "C" fn sys_gpio_toggle(resource: u32, io: u8) -> Status {
    syscall!(Syscall::GpioToggle, resource, io as u32).into()
}

/// configure value of given GPIO associated to given  device ressource
#[no_mangle]
pub extern "C" fn sys_gpio_configure(resource: u32, io: u8) -> Status {
    syscall!(Syscall::GpioConfigure, resource, io as u32).into()
}

/// configure value of given GPIO associated to given  device ressource
#[no_mangle]
pub extern "C" fn sys_get_device_handle(devlabel: u8) -> Status {
    syscall!(Syscall::GetDeviceHandle, devlabel as u32).into()
}

/// acknowledge at interrupt controller level the given interrupt
#[no_mangle]
pub extern "C" fn sys_irq_acknowledge(irq: u16) -> Status {
    syscall!(Syscall::IrqAcknowledge, irq as u32).into()
}

/// enable (unmask) at interrupt controller level the given interrupt
#[no_mangle]
pub extern "C" fn sys_irq_enable(irq: u16) -> Status {
    syscall!(Syscall::IrqEnable, irq as u32).into()
}

/// disable (mask) at interrupt controller level the given interrupt
#[no_mangle]
pub extern "C" fn sys_irq_disable(irq: u16) -> Status {
    syscall!(Syscall::IrqDisable, irq as u32).into()
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
pub extern "C" fn sys_wait_for_event(mask: u8, timeout: i32) -> Status {
    match syscall!(Syscall::WaitForEvent, u32::from(mask), timeout).into() {
        Status::Intr => syscall!(Syscall::WaitForEvent, u32::from(mask), timeout).into(),
        any => return any,
    }
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
pub extern "C" fn sys_pm_manage(mode: CPUSleep) -> Status {
    syscall!(Syscall::PmManage, u32::from(mode)).into()
}

/// Send a SIGALRM signal to the task after `timeout_ms` milliseconds.
#[no_mangle]
pub extern "C" fn sys_alarm(timeout_ms: u32, flag: AlarmFlag) -> Status {
    syscall!(Syscall::Alarm, timeout_ms, u32::from(flag)).into()
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

/// Set a given explicit clock config
///
/// Required for complex devices that need to make clock configuration vary.
/// Requires the CAP_SYS_POWER capability
///
/// TODO: using dts instead
#[no_mangle]
pub extern "C" fn sys_pm_set_clock(clk_reg: u32, clkmsk: u32, val: u32) -> Status {
    syscall!(Syscall::PmSetClock, clk_reg, clkmsk, val).into()
}

#[no_mangle]
pub extern "C" fn sys_dma_start_stream(dmah: dmah_t) -> Status {
    syscall!(Syscall::DmaStartStream, dmah).into()
}

#[no_mangle]
pub extern "C" fn sys_dma_stop_stream(dmah: dmah_t) -> Status {
    syscall!(Syscall::DmaStopStream, dmah).into()
}

#[no_mangle]
pub extern "C" fn sys_dma_get_stream_status(dmah: dmah_t) -> Status {
    syscall!(Syscall::DmaGetStreamStatus, dmah).into()
}

#[no_mangle]
pub extern "C" fn sys_shm_get_infos(shm: shmh_t) -> Status {
    syscall!(Syscall::ShmGetInfos, shm).into()
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
