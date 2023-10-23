use systypes::*;

pub fn fake_syscall(syscall_number: u32, args: &[u32]) -> u32 {
    match Syscall::try_from(syscall_number) {
        Ok(sysc) => {
            eprintln!("[{:?}({})] called with ({:?})", sysc, syscall_number, args);
        }
        _ => todo!(),
    }
    Status::Ok as u32
}

macro_rules! syscall {
    ($id:expr) => {
        fake_syscall($id as u32, &[])
    };
    ($id:expr, $arg0:expr) => {
        fake_syscall($id as u32, &[$arg0])
    };
    ($id:expr, $arg0:expr, $arg1:expr) => {
        fake_syscall($id as u32, &[$arg0, $arg1])
    };
    ($id:expr, $arg0:expr, $arg1:expr, $arg2:expr) => {
        fake_syscall($id as u32, &[$arg0, $arg1, $arg2])
    };
}
