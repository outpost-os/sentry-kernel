use managers_bindings::{task_meta, taskh_t};

#[no_mangle]
fn debug_rawlog(_s: *const u8, _length: usize) {}

#[no_mangle]
extern "C" fn sched_get_current() -> taskh_t {
    taskh_t {
        _bitfield_align_1: [0u8; 0],
        _bitfield_1: taskh_t::new_bitfield_1(0, 0, 0),
    }
}

#[no_mangle]
extern "C" fn mgr_task_get_metadata(_task_handle: taskh_t, _taskm: *mut *const task_meta) {}
