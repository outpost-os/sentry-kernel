use crate::svc_exchange::*;
use crate::syscall::*;
use core::fmt;
use systypes::*;

struct DebugPrint;

impl fmt::Write for DebugPrint {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let max_length = s.len().min(SVC_EXCH_AREA_LEN);
        unsafe { copy_from_user(s.as_ptr(), max_length) };
        sys_log(max_length);
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

pub fn get_random() -> Result<u32, Status> {
    match sys_get_random() {
        Status::Ok => (),
        any_err => return Err(any_err),
    };
    // FIXME: we might use copy_to_user here
    let exch_area = unsafe { &mut SVC_EXCHANGE_AREA[..4] };
    let result = u32::from_ne_bytes(exch_area.try_into().map_err(|_| Status::Invalid)?);
    Ok(result)
}

pub fn get_cycles() -> Result<u64, Status> {
    match sys_get_cycle(Precision::Cycle) {
        Status::Ok => (),
        any_err => return Err(any_err),
    };
    // FIXME: we might use copy_to_user here
    let exch_area = unsafe { &mut SVC_EXCHANGE_AREA[..8] };
    let result = u64::from_ne_bytes(exch_area.try_into().map_err(|_| Status::Invalid)?);
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
        assert_eq!(get_cycles(), Ok(111));
    }
}
