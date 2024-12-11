// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

use crate::systypes::*;

#[no_mangle]
pub extern "C" fn __sys_get_process_handle(process: ProcessLabel) -> Status {
    crate::syscall::get_process_handle(process).into()
}

#[no_mangle]
pub extern "C" fn __sys_exit(status: i32) -> Status {
    crate::syscall::exit(status).into()
}

#[no_mangle]
pub extern "C" fn __sys_get_shm_handle(shm: ShmLabel) -> Status {
    crate::syscall::get_shm_handle(shm).into()
}

#[no_mangle]
pub extern "C" fn __sys_get_dma_stream_handle(stream: StreamLabel) -> Status {
    crate::syscall::get_dma_stream_handle(stream).into()
}

#[no_mangle]
pub extern "C" fn __sys_sched_yield() -> Status {
    crate::syscall::sched_yield().into()
}

#[no_mangle]
pub extern "C" fn __sys_sleep(duration_ms: SleepDuration, mode: SleepMode) -> Status {
    crate::syscall::sleep(duration_ms, mode).into()
}

#[no_mangle]
pub extern "C" fn __sys_start(process: ProcessLabel) -> Status {
    crate::syscall::start(process).into()
}

#[no_mangle]
pub extern "C" fn __sys_map_dev(dev: devh_t) -> Status {
    crate::syscall::map_dev(dev as devh_t).into()
}

#[no_mangle]
pub extern "C" fn __sys_map_shm(shm: shmh_t) -> Status {
    crate::syscall::map_shm(shm as shmh_t).into()
}

#[no_mangle]
pub extern "C" fn __sys_unmap_dev(dev: devh_t) -> Status {
    crate::syscall::unmap_dev(dev as devh_t).into()
}

#[no_mangle]
pub extern "C" fn __sys_unmap_shm(shm: shmh_t) -> Status {
    crate::syscall::unmap_shm(shm as shmh_t).into()
}

#[no_mangle]
pub extern "C" fn __sys_shm_set_credential(shm: shmh_t, id: taskh_t, shm_perm: u32) -> Status {
    crate::syscall::shm_set_credential(shm, id, shm_perm).into()
}

#[no_mangle]
pub extern "C" fn __sys_send_ipc(target: taskh_t, length: u8) -> Status {
    crate::syscall::send_ipc(target as u32, length as u8).into()
}

#[no_mangle]
pub extern "C" fn __sys_send_signal(resource: u32, signal_type: Signal) -> Status {
    crate::syscall::send_signal(resource, signal_type).into()
}

#[no_mangle]
pub extern "C" fn __sys_gpio_get(resource: u32, io: u8) -> Status {
    crate::syscall::gpio_get(resource, io).into()
}

#[no_mangle]
pub extern "C" fn __sys_gpio_set(resource: u32, io: u8, val: bool) -> Status {
    crate::syscall::gpio_set(resource, io, val).into()
}

#[no_mangle]
pub extern "C" fn __sys_gpio_reset(resource: u32, io: u8) -> Status {
    crate::syscall::gpio_reset(resource, io).into()
}

#[no_mangle]
pub extern "C" fn __sys_gpio_toggle(resource: u32, io: u8) -> Status {
    crate::syscall::gpio_toggle(resource, io).into()
}

#[no_mangle]
pub extern "C" fn __sys_gpio_configure(resource: u32, io: u8) -> Status {
    crate::syscall::gpio_configure(resource, io).into()
}

#[no_mangle]
pub extern "C" fn __sys_get_device_handle(devlabel: u8) -> Status {
    crate::syscall::get_device_handle(devlabel).into()
}

#[no_mangle]
pub extern "C" fn __sys_irq_acknowledge(irq: u16) -> Status {
    crate::syscall::irq_acknowledge(irq).into()
}

#[no_mangle]
pub extern "C" fn __sys_irq_enable(irq: u16) -> Status {
    crate::syscall::irq_enable(irq).into()
}

#[no_mangle]
pub extern "C" fn __sys_irq_disable(irq: u16) -> Status {
    crate::syscall::irq_disable(irq).into()
}

#[no_mangle]
pub extern "C" fn __sys_wait_for_event(mask: u8, timeout: i32) -> Status {
    crate::syscall::wait_for_event(mask, timeout).into()
}

#[no_mangle]
pub extern "C" fn __sys_pm_manage(mode: CPUSleep) -> Status {
    crate::syscall::pm_manage(mode).into()
}

#[no_mangle]
pub extern "C" fn __sys_alarm(timeout_ms: u32, flag: AlarmFlag) -> Status {
    crate::syscall::alarm(timeout_ms, flag).into()
}

#[no_mangle]
pub extern "C" fn __sys_log(length: usize) -> Status {
    crate::syscall::log(length).into()
}

#[no_mangle]
pub extern "C" fn __sys_get_random() -> Status {
    crate::syscall::get_random().into()
}

#[no_mangle]
pub extern "C" fn __sys_get_cycle(precision: Precision) -> Status {
    crate::syscall::get_cycle(precision).into()
}

#[no_mangle]
pub extern "C" fn __sys_pm_set_clock(clk_reg: u32, clkmsk: u32, val: u32) -> Status {
    crate::syscall::pm_set_clock(clk_reg, clkmsk, val).into()
}

#[no_mangle]
pub extern "C" fn __sys_dma_start_stream(dmah: dmah_t) -> Status {
    crate::syscall::dma_start_stream(dmah).into()
}

#[no_mangle]
pub extern "C" fn __sys_dma_suspend_stream(dmah: dmah_t) -> Status {
    crate::syscall::dma_suspend_stream(dmah).into()
}

#[no_mangle]
pub extern "C" fn __sys_dma_get_stream_status(dmah: dmah_t) -> Status {
    crate::syscall::dma_get_stream_status(dmah).into()
}

#[no_mangle]
pub extern "C" fn __sys_shm_get_infos(shm: shmh_t) -> Status {
    crate::syscall::shm_get_infos(shm).into()
}

#[no_mangle]
pub extern "C" fn __sys_dma_assign_stream(dmah: dmah_t) -> Status {
    crate::syscall::dma_assign_stream(dmah).into()
}

#[no_mangle]
pub extern "C" fn __sys_dma_unassign_stream(dmah: dmah_t) -> Status {
    crate::syscall::dma_unassign_stream(dmah).into()
}

#[no_mangle]
pub extern "C" fn __sys_dma_get_stream_info(dmah: dmah_t) -> Status {
    crate::syscall::dma_get_stream_info(dmah).into()
}

#[no_mangle]
pub extern "C" fn __sys_dma_resume_stream(dmah: dmah_t) -> Status {
    crate::syscall::dma_resume_stream(dmah).into()
}
