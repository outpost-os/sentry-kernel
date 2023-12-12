pub use managers_bindings::{
    devh_t, job_state_t, kstatus_t, stack_frame_t, task_handle, task_meta,
};

extern crate std;

#[no_mangle]
extern "C" fn debug_rawlog(s: *const u8, length: usize) -> kstatus_t {
    std::print!("[debug_rawlog]: ");
    let string_ = unsafe { core::slice::from_raw_parts(s, length) };
    let string_ = unsafe { core::str::from_utf8_unchecked(string_) };
    std::println!("{}", string_);
    0
}
