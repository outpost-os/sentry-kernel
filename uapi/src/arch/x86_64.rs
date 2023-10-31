#![allow(unused_variables)]

use systypes::*;

#[cfg(test)]
use sysgate::sysgate;

pub fn debug_syscall_handler(syscall_number: u32, args: &[u32]) -> u32 {
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
    match sysgate::syscall_dispatch(syscall_number, args) {
        Ok(x) => x as u32,
        Err(_) => Status::Invalid as u32,
    }
}

macro_rules! syscall {
    ($id:expr) => {{
        use crate::arch::x86_64::debug_syscall_handler;
        debug_syscall_handler($id as u32, &[])
    }};
    ($id:expr, $arg0:expr) => {{
        use crate::arch::x86_64::debug_syscall_handler;
        debug_syscall_handler($id as u32, &[$arg0])
    }};
    ($id:expr, $arg0:expr, $arg1:expr) => {{
        use crate::arch::x86_64::debug_syscall_handler;
        debug_syscall_handler($id as u32, &[$arg0, $arg1])
    }};
    ($id:expr, $arg0:expr, $arg1:expr, $arg2:expr) => {{
        use crate::arch::x86_64::debug_syscall_handler;
        debug_syscall_handler($id as u32, &[$arg0, $arg1, $arg2])
    }};
}
