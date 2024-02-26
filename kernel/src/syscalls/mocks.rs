use managers_bindings::{job_state_t, kstatus_t, stack_frame_t, task_meta};

use core::mem::transmute;
use handles::*;
use systypes::*;

extern crate std;

#[no_mangle]
extern "C" fn debug_rawlog(s: *const u8, length: usize) -> kstatus_t {
    std::print!("[debug_rawlog]: ");
    let string_ = unsafe { core::slice::from_raw_parts(s, length) };
    let string_ = unsafe { core::str::from_utf8_unchecked(string_) };
    std::println!("{}", string_);
    0
}

extern "C" {
    static mut SVC_EXCHANGE_AREA: [u8; 128];
}

const FAKE_TASK_HANDLE: taskh_t = unsafe { transmute(0) };
const FAKE_TASK_LABEL: u32 = 0;

static mut FAKE_TASK_META: task_meta = task_meta {
    magic: 0xc2ab,
    version: 0,
    label: FAKE_TASK_LABEL,
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
    _handle: taskh_t,
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
extern "C" fn sched_get_current() -> taskh_t {
    FAKE_TASK_HANDLE
}

#[no_mangle]
extern "C" fn mgr_task_get_metadata(
    _task_handle: taskh_t,
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
extern "C" fn mgr_task_get_state(_task_handle: taskh_t, _state: *mut job_state_t) -> kstatus_t {
    0
}

#[no_mangle]
extern "C" fn mgr_task_set_state(_task_handle: taskh_t, state: job_state_t) -> kstatus_t {
    unsafe {
        FAKE_TASK.state = state;
    }
    0
}

#[no_mangle]
extern "C" fn mgr_task_get_sp(
    _task_handle: taskh_t,
    _stack_frame: *mut *mut stack_frame_t,
) -> kstatus_t {
    0
}

#[no_mangle]
extern "C" fn sched_elect() -> taskh_t {
    FAKE_TASK_HANDLE
}

#[no_mangle]
extern "C" fn mgr_time_delay_add_signal(_job: taskh_t, _delay_ms: u32, _sig: u32) -> kstatus_t {
    0
}

#[no_mangle]
extern "C" fn mgr_time_delay_add_job(_job: taskh_t, _duration_ms: u32) -> kstatus_t {
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
extern "C" fn mgr_mm_map_device(_devh: devh_t) -> kstatus_t {
    0
}

#[no_mangle]
extern "C" fn mgr_mm_unmap_device(_devh: devh_t) -> kstatus_t {
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

#[no_mangle]
extern "C" fn mgr_device_get_capa(_d: devh_t) -> u32 {
    0
}

#[no_mangle]
extern "C" fn mgr_task_set_sysreturn(_t: taskh_t, _sysret: Status) -> kstatus_t {
    0
}

#[no_mangle]
extern "C" fn mgr_task_get_sysreturn(_task: taskh_t, _status: *const Status) -> kstatus_t {
    0
}

#[no_mangle]
extern "C" fn mgr_task_clear_sysreturn(_task: taskh_t) -> kstatus_t {
    0
}
