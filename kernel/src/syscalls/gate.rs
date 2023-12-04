use super::*;
use systypes::{DispatchError, Status, Syscall};

extern "C" {
    fn exit(status: i32) -> u32;
    fn get_process_handle(process: u32) -> u32;
    fn r#yield() -> u32;
    fn sleep(duration_ms: u32, sleep_mode: u32) -> u32;
    fn start(process: u32) -> u32;
    fn map(resource: u32) -> u32;
    fn unmap(resource: u32) -> u32;
    fn shm_set_credential(resource: u32, id: u32, shm_perm: u32) -> u32;
    fn send_ipc(resource_type: u32, length: u8) -> u32;
    fn send_signal(resource_type: u32, signal_type: u32) -> u32;
    fn wait_for_event(event_type_mask: u8, resoucer_handle: u32, timeout: u32) -> u32;
}

pub fn syscall_dispatch(syscall_number: u8, args: &[u32]) -> Result<Status, DispatchError> {
    let status = match Syscall::try_from(syscall_number)? {
        Syscall::Exit => unsafe { exit(args[0] as i32) },
        Syscall::GetProcessHandle => unsafe { get_process_handle(args[0]) },
        Syscall::Yield => unsafe { r#yield() },
        Syscall::Sleep => unsafe { sleep(args[0], args[1]) },
        Syscall::Start => unsafe { start(args[0]) },
        Syscall::Map => unsafe { map(args[0]) },
        Syscall::Unmap => unsafe { unmap(args[0]) },
        Syscall::SHMSetCredential => unsafe { shm_set_credential(args[0], args[1], args[2]) },
        Syscall::SendIPC => unsafe { send_ipc(args[0], args[1] as u8) },
        Syscall::SendSignal => unsafe { send_signal(args[0], args[1]) },
        Syscall::WaitForEvent => unsafe { wait_for_event(args[0] as u8, args[1], args[2]) },
        Syscall::ManageCPUSleep => return manage_cpu_sleep(args[0]),
        Syscall::Log => {
            #[cfg(not(CONFIG_BUILD_TARGET_RELEASE))]
            return log_rs(args[0] as usize);

            #[cfg(CONFIG_BUILD_TARGET_RELEASE)]
            0
        }
    };
    Ok(status.into())
}
