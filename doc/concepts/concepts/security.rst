Security requirements
---------------------

Multiple security considerations have been taken into account at design time.
These considerations are the consequence of a security study with respect for
the core usage of the Outpost OS and the Sentry kernel, which targets small embedded
systems.

The consideration are the following:

   1. As much as possible properties must be a build-time information that can be
      verified before flashing the target. To achieve that, Sentry kernel consider
      a lot of information as being build-time produced. Typically:

      * task list
      * each task capabilities
      * each task memory mapping
      * each task list of allowed devices
      * each task list of allowed shared memory
      * each task list of allowed DMA streams
      * each task integrity signature (HMAC generation)
      * each task metadata integrity signature (HMAC generation)
      * device tree configuration (for both kernel and userspace driver)
      * IPC communication channel allowance between tasks

   2. Exchanges between tasks are controlled, as such, the following restrictions exists:
      * no broadcast IPC emission
      * no broadcast signal emission
      * a device (as declared in the device tree) is strictly dedicated to a given task (including pinmuxes for LEDs for e.g.)
      * a shared-memory can be mapped at most in two task at a time
      * shared memory ownership is always kept under the control of the initial SHM declarator

   3. Exchange between tasks and Sentry kernel

      * No pointer is ever transmitted between userspace tasks and Sentry kernel. Instead tasks are
        using :ref:`handles <handles>` and a dedicated small memory region denoted `svc_block` for
        non-scalar data transmission and syscall data return (see
        :ref:`userspace / kernelspace data transmission <_copyfromtouser>` chapter).

   4. memory mapping is fully restricted
      * except SHM, task memory mapping are strictly separated (check at build time)
      * Sentry kernel is a monitor, not god: it do not have access to task memory map, excepting
        the task `svc_block`. Only handler entrypoint manipulate the task stack for saving/restoring
        the task context, just before demapping the task region
      * All mapped regions respect the `W^X` principle

   5. security events consideration
      * Security related events are considered in Sentry, through the usage of the `sigabort`
        post-mortem service. Any abnormal event that generate an invalid task termination
        generate a call to this runtime post-mortem service in the task context with a fresh
        stask. If the task developer implement a sigabort hook, it will be executed
      * In release mode, any security level return code (abnormal return code considered as
        a security exception) generates a panic call which lead to a full reset
      * *TBD*: any abnormal event that generate a board reset aim to be stored in a dedicated,
        encrypted, flash memory dedicated area, in a specific binary formatted structure for
        post-mortem analysis after dump and decryption
      * Sentry kernel include various security whatchdogs that are proactively executed regulary
        (at syscall time or schedule time) to check kernel-related content state (MPU configuration,
        hardware registers states, etc.) Any fail lead to a security `panic()`.

   6. bootup and modes
      * Sentry build natively supports two modes: `debug` and `release`
         * **debug**: debug manager is compiled and linked, adding usart and other debug features.
           Some debug-related feature that may reduce security can be activated. The build system
           inform the developer that the kernel is built in debug mode and MUST NOT be used in production
         * **release**: all debug are deactivated, all enforcement are activated and can't be deactivated
           even through the configuration GUI. This include overall bootup integrity checks (task HMACs),
           MPU hardening and various periodic security watchdogs
