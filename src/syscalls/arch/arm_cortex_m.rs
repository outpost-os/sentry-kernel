use crate::gate::syscall_dispatch;
use core::arch::asm;

#[repr(C)]
pub struct StackFrame {
    r4: u32,
    r5: u32,
    r6: u32,
    r7: u32,
    r8: u32,
    r9: u32,
    r10: u32,
    r11: u32,
    lr: u32,
    r0: u32,
    r1: u32,
    r2: u32,
    r3: u32,
    r12: u32,
    prev_lr: u32,
    pc: u32,
    xpsr: u32,
}

#[no_mangle]
pub unsafe fn svc_handler_rs(stack_frame: *const StackFrame) -> *mut StackFrame {
    let syscall_num = *((*stack_frame).pc as *const u8).offset(-2);
    let args = [
        (*stack_frame).r0,
        (*stack_frame).r1,
        (*stack_frame).r2,
        (*stack_frame).r3,
    ];
    let _ = syscall_dispatch(syscall_num, &args);
    stack_frame as *mut StackFrame
}

pub fn __wfe() {
    unsafe {
        asm!("wfe");
    }
}

pub fn __wfi() {
    unsafe {
        asm!("wfi");
    }
}

// /// SVC interrupt handler for ARMv7 cores
// /// Currently unused
// #[no_mangle]
// #[naked]
// extern "C" fn SVC_Handler() {
//     unsafe {
//         asm!(
//             "tst   lr, #4",
//             "ite   eq",
//             "mrseq r0, msp",
//             "mrsne r0, psp",
//             "b     svc_handler_rs",
//             "b     =0xfffffffd",
//             options(noreturn)
//         );
//     }
// }
