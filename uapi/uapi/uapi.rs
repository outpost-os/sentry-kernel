// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

use crate::svc_exchange::*;
use crate::syscall;
use core::fmt;
use crate::systypes::*;

struct DebugPrint;

impl fmt::Write for DebugPrint {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        log(s);
        Ok(())
    }
}

pub fn _print(args: fmt::Arguments) {
    use core::fmt::Write;
    DebugPrint.write_fmt(args).expect("Print failed");
}

#[macro_export]
macro_rules! print {
    ($($arg:tt)*) => {
        ($crate::uapi::_print(format_args!($($arg)*)))
    }
}

#[macro_export]
macro_rules! println {
    () => ($crate::print!("\n"));
    ($($arg:tt)*) => ($crate::print!("{}\n", format_args!($($arg)*)))
}

/// Emit an already formatted string through the Sentry kernel std log output
///
/// # Usage
///
/// If the kernel is configured with logging output activated, the given string
/// is transmitted through the kernel loggin system.
///
/// There is no string formatting at this level, leaving the formating to upper
/// layers.
/// If the string length is bigger than the maximum size of the SVC_EXCHANGE area,
/// it is truncated silently.
/// If the log output is deactivated, the kernel silently drop the emitted
/// content, to avoid any behavior variation at userspace level if the logging
/// system is deactivated.
///
/// This function always success.
///
/// # Example
///
/// ```rust
/// log("hello worold!");
/// ```
pub fn log(s: &str) -> Status {
    let max_length = s.len().min(SVC_EXCH_AREA_LEN);
    unsafe { copy_from_user(s.as_ptr(), max_length) };
    syscall::sys_log(max_length);
    Status::Ok
}


/// Get random seed from the Sentry kernel RNG backend
///
/// # Usage
///
/// The random seed received is 32 bits length. If the caller needs to
/// forge a longer seeds without using an application hosted derivation, the
/// syscall need to be called multiple-time.
///
/// This syscall requires the caller to hold the CAP_CRY_KRNG capability.
/// Without this capability, Status::Denied is returned.
///
/// The syscall may fail if the kernel RNG source fails to properly delivers
/// a FIPS compliant random value. In that case, the syscall returns
/// Status::Critical.
///
/// # Example
///
/// ```rust
/// let seed = get_random();
/// match seed {
///   u32 => (),
///   any_err => Err(any_err),
/// };
/// ```
///
pub fn get_random() -> Result<u32, Status> {
    match syscall::sys_get_random() {
        Status::Ok => (),
        any_err => return Err(any_err),
    };
    // FIXME: we might use copy_to_user here
    let exch_area = unsafe { &mut SVC_EXCHANGE_AREA[..4] };
    let result = u32::from_ne_bytes(exch_area.try_into().map_err(|_| Status::Invalid)?);
    Ok(result)
}

/// Get back the elapsed time since startup, in various units
///
/// # Usage
///
/// The kernel store the elapsed time since its startup so that it is possible
/// to get basic time measurement, being from startup or between two call to
/// this API, in various format.
///
/// The precision required is passed in the unit argument, as defined in the
/// [`Precision`] type.
///
/// Whatever the precision is, the unit type is always `u64`.
///
/// While [`Precision::Milliseconds`] and [`Precision::Microseconds`] do not
/// require specific capability, [`Precision::Nanoseconds`] and [`Precision::Cycle`]
/// require the CAP_TIM_HP_CHRONO capability. This avoid any hability to
/// get high precision measurements that may leed to side channel analysis on
/// another task's behavior without having the corresponding capability.
///
/// Most of the time, this capability is not required.
///
/// # Example
///
/// ```
/// let unit = Precision::Cycle;
/// let time_cycl = get_elapsed_time(unit);
/// match time_cycl {
///   u64 => (),
///   any_err => Err(any_err),
/// };
/// ```
///
pub fn get_elapsed_time(unit: Precision) -> Result<u64, Status> {
    match syscall::sys_get_cycle(unit) {
        Status::Ok => (),
        any_err => return Err(any_err),
    };
    // FIXME: we might use copy_to_user here
    let exch_area = unsafe { &mut SVC_EXCHANGE_AREA[..8] };
    let result = u64::from_ne_bytes(exch_area.try_into().map_err(|_| Status::Invalid)?);
    Ok(result)
}


/// Get back the task handle associated to the input task label
///
/// FIXME: to be moved up to a dedicated crate (shield-rs) out of Sentry kernel repo
///
/// # Usage
///
/// While task labels are compile-time fixed and known by tasks that communicate
/// with each other, the label can't be used at runtime in order to use the
/// Sentry communication API.
///
/// Instead, at each job creation (including recreation when a job exists and restart),
/// a job handle is forged dynamically. This API allows any tasks that know
/// the corresponding task label to get back the associated handle.
///
/// # Example
///
/// ```rust
/// let label = 0xbabe;
/// let handle = get_process_handle(label);
/// match handle {
///   taskh_t => (),
///   any_err => Err(any_err),
/// };
/// ```
///
/// # See also
///
/// backend syscall: [`syscall::sys_get_process_handle`]
///
pub fn get_process_handle(process: ProcessLabel, _handle: *mut taskh_t) -> Result<taskh_t,Status> {
    match syscall::sys_get_process_handle(process) {
        Status::Ok => (),
        any_err => return Err(any_err),
    };
    // FIXME: we might use copy_to_user here
    let exch_area = unsafe { &mut SVC_EXCHANGE_AREA[..4] };
    let result = u32::from_ne_bytes(exch_area.try_into().map_err(|_| Status::Invalid)?);
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn logging() {
        let text = "plorp";
        print!("{}", text);
        assert_eq!(unsafe { &SVC_EXCHANGE_AREA[..text.len()] }, text.as_bytes());
    }

    #[test]
    fn bad_logging() {
        let text = "more than 128 characters long string aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        print!("{}", text);
        assert_eq!(unsafe { &SVC_EXCHANGE_AREA }, &text.as_bytes()[..128]);
    }

    #[test]
    fn random() {
        assert_eq!(get_random(), Ok(0xaabbccdd));
    }

    #[test]
    fn cycles() {
        let unit = Precision::Cycle;
        assert_eq!(get_elapsed_time(unit), Ok(111));
    }
}
