use crate::svc_exchange::*;
use crate::syscall::*;
use bitflags::bitflags;
use core::fmt;
use systypes::*;

bitflags! {
    pub struct ResourceHandleBits: u32 {
        const RESOURCE_TYPE = 0b0000_0000_0000_0000_0000_0000_1111;
        const TASK_NS       = 0b0000_0000_0000_1111_1111_1111_0000;
        const RESOURCE_ID   = 0b1111_1111_1111_0000_0000_0000_0000;
    }
}

impl From<ResourceHandleBits> for ResourceHandle {
    fn from(rh: ResourceHandleBits) -> ResourceHandle {
        rh.bits()
    }
}

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
    use core::mem::transmute;
    use sysgate::mocks::*;

    const FAKE_TASK_HANDLE: task_handle = unsafe { transmute(0) };
    static mut FAKE_TASK_META: task_meta = task_meta {
        magic: 0xc2ab,
        version: 0,
        handle: FAKE_TASK_HANDLE,
        priority: 0,
        quantum: 0,
        capabilities: 0xffffffff,
        flags: unsafe { transmute(0u32) },
        s_text: 0,
        text_size: 0,
        s_got: 0,
        got_size: 0,
        rodata_size: 0,
        data_size: 0,
        bss_size: 0,
        heap_size: 0,
        s_svcexchange: 0,
        stack_size: 0,
        entrypoint_offset: 0,
        finalize_offset: 0,
        num_shm: 0,
        shms: [unsafe { transmute(0) }],
        num_devs: 0,
        devs: [unsafe { transmute(0) }],
        num_dmas: 0,
        dmas: [unsafe { transmute(0) }],
        domain: 0,
        task_hmac: [0; 32],
        metadata_hmac: [0; 32],
    };

    struct FakeTask {
        _handle: task_handle,
        _metadata: &'static task_meta,
        #[cfg(windows)]
        state: i32,
        #[cfg(unix)]
        state: u32,
    }

    static mut FAKE_TASK: FakeTask = FakeTask {
        _handle: FAKE_TASK_HANDLE,
        _metadata: unsafe { &FAKE_TASK_META },
        state: 0,
    };

    #[no_mangle]
    extern "C" fn sched_get_current() -> task_handle {
        FAKE_TASK_HANDLE
    }

    #[no_mangle]
    extern "C" fn mgr_task_get_metadata(
        _task_handle: task_handle,
        taskm: *mut *const task_meta,
    ) -> kstatus_t {
        // force task_meta's parameters
        unsafe {
            FAKE_TASK_META.s_svcexchange = SVC_EXCHANGE_AREA.as_mut_ptr() as usize;
            *taskm = &FAKE_TASK_META as *const task_meta;
        }
        0
    }

    #[no_mangle]
    extern "C" fn mgr_task_get_state(
        _task_handle: task_handle,
        _state: *mut job_state_t,
    ) -> kstatus_t {
        0
    }

    #[no_mangle]
    extern "C" fn mgr_task_set_state(_task_handle: task_handle, state: job_state_t) -> kstatus_t {
        unsafe {
            FAKE_TASK.state = state;
        }
        0
    }

    #[no_mangle]
    extern "C" fn mgr_task_get_sp(
        _task_handle: task_handle,
        _stack_frame: *mut *mut stack_frame_t,
    ) -> kstatus_t {
        0
    }

    #[no_mangle]
    extern "C" fn sched_elect() -> task_handle {
        FAKE_TASK_HANDLE
    }

    #[no_mangle]
    extern "C" fn mgr_time_delay_add_signal(
        _job: task_handle,
        _delay_ms: u32,
        _sig: sigh_t,
    ) -> kstatus_t {
        0
    }

    #[no_mangle]
    extern "C" fn mgr_time_delay_add_job(_job: task_handle, _duration_ms: u32) -> kstatus_t {
        0
    }

    #[no_mangle]
    extern "C" fn mgr_security_entropy_generate(seed: *mut u32) -> kstatus_t {
        unsafe {
            *seed = 0xaabbccdd;
        }
        0
    }

    #[no_mangle]
    extern "C" fn mgr_time_get_cycle() -> u64 {
        111
    }

    #[no_mangle]
    extern "C" fn mgr_time_get_nanoseconds() -> u64 {
        222
    }

    #[no_mangle]
    extern "C" fn mgr_time_get_microseconds() -> u64 {
        333
    }

    #[no_mangle]
    extern "C" fn mgr_time_get_milliseconds() -> u64 {
        444
    }

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
