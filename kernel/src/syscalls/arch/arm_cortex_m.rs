use crate::gate::syscall_dispatch;
use core::arch::asm;
use managers_bindings::stack_frame_t;
use systypes::Syscall;

#[no_mangle]
/// # Safety
/// This function is always unsafe because it has to dereference
/// raw pointers coming from C/ASM. Caller should make sure the
/// input stack_frame is valid according to the StackFrame struct
/// above
pub unsafe fn svc_handler_rs(stack_frame: *mut stack_frame_t) -> *mut stack_frame_t {
    let syscall_num = *((*stack_frame).pc as *const u8).offset(-2);
    let args = [
        (*stack_frame).r0,
        (*stack_frame).r1,
        (*stack_frame).r2,
        (*stack_frame).r3,
    ];
    let new_stack_frame = syscall_dispatch(syscall_num, &args);
    match new_stack_frame {
        Err(e) => {
            stack_frame
        }
        Ok(None) => {
            stack_frame
        }
        Ok(Some(x)) => {
            x
        }
    }
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
