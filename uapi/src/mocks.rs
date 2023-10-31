#![allow(unused_variables)]

#[no_mangle]
pub fn exit(status: i32) -> u32 {
    0
}

#[no_mangle]
pub fn get_process_handle(process: u32) -> u32 {
    0
}

#[no_mangle]
pub fn r#yield() -> u32 {
    0
}

#[no_mangle]
pub fn sleep(duration_ms: u32, sleep_mode: u32) -> u32 {
    0
}

#[no_mangle]
pub fn start(process: u32) -> u32 {
    0
}

#[no_mangle]
pub fn map(resource: u32) -> u32 {
    0
}

#[no_mangle]
pub fn unmap(resource: u32) -> u32 {
    0
}

#[no_mangle]
pub fn shm_set_credential(resource: u32, id: u32, shm_perm: u32) -> u32 {
    0
}

#[no_mangle]
pub fn send_ipc(resource_type: u32, length: u8) -> u32 {
    0
}

#[no_mangle]
pub fn send_signal(resource_type: u32, signal_type: u32) -> u32 {
    0
}

#[no_mangle]
pub fn wait_for_event(event_type_mask: u8, resoucer_handle: u32, timeout: u32) -> u32 {
    0
}
