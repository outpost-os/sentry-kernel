
#ifndef __PLATFORM_H_
#define __PLATFORM_H_

#ifndef PLATFORM_H
#error "arch specific header must not be included directly!"
#endif

static inline void __platform_spawn_kworker(void) {
    /*
     * Initial context switches to main core thread (idle_thread).
     */
	asm volatile
       ("mov r0, %[SP]      \n\t"   \
        "msr psp, r0        \n\t"   \
        "mov r0, 2          \n\t"   \
        "msr control, r0    \n\t"   \
	    "mov r1, %[PC]      \n\t"   \
	    "bx r1              \n\t"   \
        :
        : [PC] "r" (kworker_thread),
          [SP] "r" (kworker_stack_pointer)
        : "r0", "r1");
}

#endif/*!__PLATFORM_H_*/
