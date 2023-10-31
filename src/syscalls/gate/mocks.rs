#[no_mangle]
extern "C" fn exit(_status: i32) -> u32 {
    0
}

#[no_mangle]
extern "C" fn get_process_handle(_process: u32) -> u32 {
    0
}

#[no_mangle]
extern "C" fn r#yield() -> u32 {
    0
}

#[no_mangle]
extern "C" fn sleep(_duration_ms: u32, _sleep_mode: u32) -> u32 {
    0
}

#[no_mangle]
extern "C" fn start(_process: u32) -> u32 {
    0
}

#[no_mangle]
extern "C" fn map(_resource: u32) -> u32 {
    0
}

#[no_mangle]
extern "C" fn unmap(_resource: u32) -> u32 {
    0
}

#[no_mangle]
extern "C" fn shm_set_credential(_resource: u32, _id: u32, _shm_perm: u32) -> u32 {
    0
}

#[no_mangle]
extern "C" fn send_ipc(_resource_type: u32, _length: u8) -> u32 {
    0
}

#[no_mangle]
extern "C" fn send_signal(_resource_type: u32, _signal_type: u32) -> u32 {
    0
}

#[no_mangle]
extern "C" fn wait_for_event(_event_type_mask: u8, _resoucer_handle: u32, _timeout: u32) -> u32 {
    0
}
