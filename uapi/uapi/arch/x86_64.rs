#![allow(unused_variables)]

use crate::systypes::*;

#[cfg(test)]
use sysgate::gate;

pub fn debug_syscall_handler(syscall_number: u8, args: &[u32]) -> u32 {
    #[cfg(not(test))]
    match Syscall::try_from(syscall_number) {
        Ok(sysc) => {
            #[cfg(feature = "std")]
            eprintln!("[{:?}({})] called with ({:?})", sysc, syscall_number, args);
            Status::Ok as u32
        }
        Err(_) => {
            #[cfg(feature = "std")]
            eprintln!("! {syscall_number} is not a syscall number");
            Status::Invalid as u32
        }
    }

    #[cfg(test)]
    match gate::syscall_dispatch(syscall_number, args) {
        Ok(_) => Status::Ok as u32,
        Err(x) => x as u32,
    }
}

macro_rules! syscall {
    ($id:expr) => {{
        use crate::arch::x86_64::debug_syscall_handler;
        debug_syscall_handler($id as u8, &[])
    }};
    ($id:expr, $arg0:expr) => {{
        use crate::arch::x86_64::debug_syscall_handler;
        debug_syscall_handler($id as u8, &[$arg0])
    }};
    ($id:expr, $arg0:expr, $arg1:expr) => {{
        use crate::arch::x86_64::debug_syscall_handler;
        debug_syscall_handler($id as u8, &[$arg0, $arg1])
    }};
    ($id:expr, $arg0:expr, $arg1:expr, $arg2:expr) => {{
        use crate::arch::x86_64::debug_syscall_handler;
        debug_syscall_handler($id as u8, &[$arg0, $arg1, $arg2])
    }};
}
