// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

use crate::systypes::*;

#[no_mangle]
pub extern "C" fn __sys_get_process_handle(process: TaskLabel) -> Status {
    crate::syscall::get_process_handle(process)
}

#[no_mangle]
pub extern "C" fn __sys_exit(status: i32) -> Status {
    crate::syscall::exit(status)
}

#[no_mangle]
pub extern "C" fn __sys_get_shm_handle(shm: ShmLabel) -> Status {
    crate::syscall::get_shm_handle(shm)
}

#[no_mangle]
pub extern "C" fn __sys_get_dma_stream_handle(stream: StreamLabel) -> Status {
    crate::syscall::get_dma_stream_handle(stream)
}

#[no_mangle]
pub extern "C" fn __sys_sched_yield() -> Status {
    crate::syscall::sched_yield()
}

#[no_mangle]
pub extern "C" fn __sys_sleep(duration_ms: SleepDuration, mode: SleepMode) -> Status {
    crate::syscall::sleep(duration_ms, mode)
}

#[no_mangle]
pub extern "C" fn __sys_start(process: TaskLabel) -> Status {
    crate::syscall::start(process)
}

#[no_mangle]
pub extern "C" fn __sys_map_dev(dev: DeviceHandle) -> Status {
    crate::syscall::map_dev(dev as DeviceHandle)
}

#[no_mangle]
pub extern "C" fn __sys_map_shm(shm: ShmHandle) -> Status {
    crate::syscall::map_shm(shm as ShmHandle)
}

#[no_mangle]
pub extern "C" fn __sys_unmap_dev(dev: DeviceHandle) -> Status {
    crate::syscall::unmap_dev(dev as DeviceHandle)
}

#[no_mangle]
pub extern "C" fn __sys_unmap_shm(shm: ShmHandle) -> Status {
    crate::syscall::unmap_shm(shm as ShmHandle)
}

#[no_mangle]
pub extern "C" fn __sys_shm_set_credential(
    shm: ShmHandle,
    id: TaskHandle,
    shm_perm: u32,
) -> Status {
    crate::syscall::shm_set_credential(shm, id, shm_perm)
}

#[no_mangle]
pub extern "C" fn __sys_send_ipc(target: TaskHandle, length: u8) -> Status {
    crate::syscall::send_ipc(target, length)
}

#[no_mangle]
pub extern "C" fn __sys_send_signal(resource: u32, signal_type: Signal) -> Status {
    crate::syscall::send_signal(resource, signal_type)
}

#[no_mangle]
pub extern "C" fn __sys_gpio_get(resource: u32, io: u8) -> Status {
    crate::syscall::gpio_get(resource, io)
}

#[no_mangle]
pub extern "C" fn __sys_gpio_set(resource: u32, io: u8, val: bool) -> Status {
    crate::syscall::gpio_set(resource, io, val)
}

#[no_mangle]
pub extern "C" fn __sys_gpio_reset(resource: u32, io: u8) -> Status {
    crate::syscall::gpio_reset(resource, io)
}

#[no_mangle]
pub extern "C" fn __sys_gpio_toggle(resource: u32, io: u8) -> Status {
    crate::syscall::gpio_toggle(resource, io)
}

#[no_mangle]
pub extern "C" fn __sys_gpio_configure(resource: u32, io: u8) -> Status {
    crate::syscall::gpio_configure(resource, io)
}

#[no_mangle]
pub extern "C" fn __sys_get_device_handle(devlabel: u8) -> Status {
    crate::syscall::get_device_handle(devlabel)
}

#[no_mangle]
pub extern "C" fn __sys_irq_acknowledge(irq: u16) -> Status {
    crate::syscall::irq_acknowledge(irq)
}

#[no_mangle]
pub extern "C" fn __sys_irq_enable(irq: u16) -> Status {
    crate::syscall::irq_enable(irq)
}

#[no_mangle]
pub extern "C" fn __sys_irq_disable(irq: u16) -> Status {
    crate::syscall::irq_disable(irq)
}

#[no_mangle]
pub extern "C" fn __sys_wait_for_event(mask: u8, timeout: i32) -> Status {
    crate::syscall::wait_for_event(mask, timeout)
}

#[no_mangle]
pub extern "C" fn __sys_pm_manage(mode: CPUSleep) -> Status {
    crate::syscall::pm_manage(mode)
}

#[no_mangle]
pub extern "C" fn __sys_alarm(timeout_ms: u32, flag: AlarmFlag) -> Status {
    crate::syscall::alarm(timeout_ms, flag)
}

#[no_mangle]
pub extern "C" fn __sys_log(length: usize) -> Status {
    crate::syscall::log(length)
}

#[no_mangle]
pub extern "C" fn __sys_get_random() -> Status {
    crate::syscall::get_random()
}

#[no_mangle]
pub extern "C" fn __sys_get_cycle(precision: Precision) -> Status {
    crate::syscall::get_cycle(precision)
}

#[no_mangle]
pub extern "C" fn __sys_pm_set_clock(clk_reg: u32, clkmsk: u32, val: u32) -> Status {
    crate::syscall::pm_set_clock(clk_reg, clkmsk, val)
}

#[no_mangle]
pub extern "C" fn __sys_dma_start_stream(dmah: StreamHandle) -> Status {
    crate::syscall::dma_start_stream(dmah)
}

#[no_mangle]
pub extern "C" fn __sys_dma_suspend_stream(dmah: StreamHandle) -> Status {
    crate::syscall::dma_suspend_stream(dmah)
}

#[no_mangle]
pub extern "C" fn __sys_dma_get_stream_status(dmah: StreamHandle) -> Status {
    crate::syscall::dma_get_stream_status(dmah)
}

#[no_mangle]
pub extern "C" fn __sys_shm_get_infos(shm: ShmHandle) -> Status {
    crate::syscall::shm_get_infos(shm)
}

#[no_mangle]
pub extern "C" fn __sys_dma_assign_stream(dmah: StreamHandle) -> Status {
    crate::syscall::dma_assign_stream(dmah)
}

#[no_mangle]
pub extern "C" fn __sys_dma_unassign_stream(dmah: StreamHandle) -> Status {
    crate::syscall::dma_unassign_stream(dmah)
}

#[no_mangle]
pub extern "C" fn __sys_dma_get_stream_info(dmah: StreamHandle) -> Status {
    crate::syscall::dma_get_stream_info(dmah)
}

#[no_mangle]
pub extern "C" fn __sys_dma_resume_stream(dmah: StreamHandle) -> Status {
    crate::syscall::dma_resume_stream(dmah)
}
