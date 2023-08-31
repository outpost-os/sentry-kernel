.syntax unified
.cpu cortex-m4
.thumb

.global VTOR_address
/* handling interrupt dispatch in a C function */
.extern Default_SubHandler
.extern HardFaultHandler

/* start address for the initialization values of the .data
   section. defined in linker script */
.word   _sidata
/* start address for the .data section. defined in linker script */
.word   _sdata
/* end address for the .data section. defined in linker script */
.word   _edata
/* start address for the .bss section. defined in linker script */
.word   _sbss
/* end address for the .bss section. defined in linker script */
.word   _ebss
.word   _sigot
.word   _sgot
.word   _egot


.section .data

/* FIXME: use per SoC VTOR address and size (extern) */
VTOR_address: .word 0


/*
 * Very first code executed after a reset event
 */
.section .text.Reset_Handler
    .weak  Reset_Handler
    .type  Reset_Handler, %function
Reset_Handler:
    bl  _start                  /* Entry point address */

_start:
    cpsid   i

    /* Retrieve Reset_Handler address */
    movs    r5, lr
    /* In thumb mode LR is pointing to PC + 4 bytes + 1 (odd aligned) */
    sub     r5, #5

    /* Here, VTOR addr is 0x0 (fixed for companion core) */
    movs    r2, #0

    /* Note: we can't store VTOR address in VTOR_address variable
    here because .data section will be zeroed */

    ldr     r2, [r2]
    /* Reset stack address to default 0x20001000. DTCM is 0x20000000 */
    /* this means we have 4K stack by now */
    msr     msp, r2
    movs  r1, #0
    b       LoopCopyDataInit

    /* Copy the data segment initializers from flash to SRAM */
CopyDataInit:
    ldr     r3, =_sidata        /* start address for the initialization values of the .data section. */
    ldr     r3, [r3, r1]
    str     r3, [r0, r1]
    adds    r1, r1, #4

LoopCopyDataInit:
    ldr     r0, =_sdata         /* start address for the .data section */
    ldr     r3, =_edata         /* end address for the .data section */
    adds    r2, r0, r1
    cmp     r2, r3
    bcc     CopyDataInit
    ldr     r2, =_sbss          /* start address for the .bss section */
    b       LoopFillZerobss

FillZerobss:                     /* Zero fill the bss segment. */
    movs    r3, #0
    str     r3, [r2], #4

LoopFillZerobss:
    ldr     r3, = _ebss          /* end address for the .bss section */
    cmp     r2, r3
    bcc     FillZerobss

    /* Store computed VTOR address (in r5) in VTOR_address */
    ldr     r1, = VTOR_address
    str     r5, [r1]

    bl      _entrypoint   /* baremetal code entrypoint. data accessible  */
    /* we snould not reach this point */
    bx      lr


.size  Reset_Handler, .-Reset_Handler

/* FIXME: should be C implementation here */
.section .text.Default_Handler
    .weak  Default_Handler
    .type  Default_Handler, %function
Default_Handler:
    cpsid   i

    /*
     * The NVIC has already saved R0-R3, R12, LR, PC and xPSR registers on the
     * stack. We save the remaining registers (R4-R11) and LR (with the new
     * value) on that previously used stack.
     */

    /* 1) Which stack was previously used ? (MSP vs PSP support. Only
          interrupts should use MSP) */

    tst     lr, #4      /* bit 2: (0) MSP (1) PSP stack      */
    ite     eq          /* if equal 0                        */
    mrseq   r0, msp     /* r0 <- MSP                         */
    mrsne   r0, psp     /* r0 <- PSP (process stack)         */

    /*
     * 2) Save registers on the previously used stack.
     *    R0 points to the saved registers:
     *        LR, R4-R11, R0-R3, R12, previous LR, PC, xPSR
     */

    stmfd   r0!, {r4-r11, lr}

    /* 3) Adjusting the previously used stack pointer (might be PSP or MSP) */

    tst     lr, #4      /* bit 2: (0) MSP (1) PSP stack      */
    ite     eq          /* if equal 0                        */
    msreq   msp, r0     /* MSP <- r0                         */
    msrne   psp, r0     /* PSP <- r0                         */

    /*
     * R0 is passed as a parameter. It still points to the saved registers.
     * In case of task switching, R0 returned by `Default_SubHandler' might be
     * different.
     * R1 is returned by `Default_SubHandler' and it contains the task type.
     * Valid R1 values are privileged (0) or unprivileged (1).
     */

    /* calling default subhandler (C small code, which is a dispatcher) */
    bl      Default_SubHandler

    /* Registers LR, R4-R11 are restored */
    ldmfd   r0!, {r4-r11, lr}

    /*
     * Adjusting PSP/MSP so that the NVIC can restore the remaining registers
     * and setting the execution mode (privileged or unprivileged)
     */

    tst     lr, #4      /* bit 2: (0) MSP (1) PSP stack      */
    bne     psp_use     /* if not equal 0                    */

msp_use:
    /* That branch should never be executed as every task use the PSP */
    msr     msp, r0     /* MSP <- r0 */
    isb
    cpsie   i
    bx      lr

psp_use:
    msr     psp, r0     /* PSP <- r0 */

/*
// handling user mode task not supported by now, stays in supervisor
    cmp     r1, #1
    bne     kern_mode
user_mode:
    mov     r0, #3
    msr     control, r0
    isb
    cpsie   i
    bx      lr
*/

kern_mode:
    mov     r0, #2
    msr     control, r0
    isb
    cpsie   i
    bx      lr
.size Default_Handler, .-Default_Handler
