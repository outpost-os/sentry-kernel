use core::fmt;
use managers_bindings::debug_rawlog;

struct DebugPrint;

impl fmt::Write for DebugPrint {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        unsafe { debug_rawlog(s.as_ptr(), s.len()) };
        Ok(())
    }
}

pub fn _print(args: fmt::Arguments) {
    use core::fmt::Write;
    DebugPrint.write_fmt(args).unwrap();
}

#[macro_export]
macro_rules! print {
    ($($arg:tt)*) => {
        ($crate::debug::_print(format_args!($($arg)*)))
    }
}

#[macro_export]
macro_rules! println {
    () => ($crate::print!("\n"));
    ($($arg:tt)*) => ($crate::print!("{}\n", format_args!($($arg)*)))
}
