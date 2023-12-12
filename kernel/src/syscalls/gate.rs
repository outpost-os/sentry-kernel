use super::*;
use managers_bindings::stack_frame_t;
use systypes::{Status, Syscall};

pub type StackFramePointer = Option<*mut stack_frame_t>;

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

        #[cfg(not(CONFIG_BUILD_TARGET_RELEASE))]
        Syscall::Log => log_rs(args[0] as usize),

        #[cfg(CONFIG_BUILD_TARGET_RELEASE)]
        Syscall::Log => Ok(None),
    }
}
