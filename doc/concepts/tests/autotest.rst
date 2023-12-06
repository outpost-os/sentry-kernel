Sentry Autotest mode
--------------------

.. index::
    single: autotest; model
    single: test; autotest test model
    single: autotest API; model
    single: autotest API; definition

About Autotest
""""""""""""""

Autotest is a test methodology using a dedicated task built in order
to requires various Sentry kernel autotest methods execution.

The goal of the autotest mode is to validate various kernel subsystems, mostly
managers, in order to validate runtime-related


To control the autotest mode from the autotest application, the Sentry kernel include,
in autotest mode exclusively, a dedicated syscall denoted `sys_autotest()`, with the following API:

.. code-block:: C

    typedef enum autotest_request {
    SENTRY_AUTOTEST_ENTER  = 1,             /**< enter autotest mode */
    SENTRY_AUTOTEST_LEAVE,                  /**< leave autotest mode */
    SENTRY_AUTOTEST_CALL_MGR_CLOCK,         /**< ask for clock mgr autotest */
    SENTRY_AUTOTEST_CALL_CHECK_MGR_DEBUG,   /**< ask for debug mgr autotest */
    SENTRY_AUTOTEST_CALL_MGR_DEVICE,        /**< ask for device mgr autotest */
    SENTRY_AUTOTEST_CALL_MGR_INTERRUPT,     /**< ask for interrupt mgr autotest */
    SENTRY_AUTOTEST_CALL_MGR_IO,            /**< ask for IO manager autotest */
    SENTRY_AUTOTEST_CALL_MGR_MEMORY,        /**< ask for IO memory autotest */
    SENTRY_AUTOTEST_CALL_MGR_SECURITY,      /**< ask for security manager autotest */
    SENTRY_AUTOTEST_CALL_MGR_TASK,          /**< ask for task manager autotest */
    SENTRY_AUTOTEST_CALL_SCHED,             /**< ask for scheduler autotest */
    } autotest_request_t;

    sys_return_t sys_autotest(autotest_request_t command);

Runtime kernel testing
""""""""""""""""""""""

Autotest is built for two main usages:

   * testing manager behavior and performances in nominal usage. The goal is
     to get back test measurements of various Sentry kernel components directly
     on board (or on the targetting SoC), to get back some measurements on various
     testable values that need to be executed on target
     this is done through the usage of the `call` command set of the API, that ask
     a kernel module to execute its own autotest and return the result

   * testing invalid behavior kernel response, ensuring kernel hardening triggering
     to various userspace based invalid transmission. That later case verify that
     the various security triggers are being executed as expected.
     This is done using the enter/leave commands, that change the kernel behavior
     when executing all sanitation and security related functions starting at the
     `ENTER` command, and upto the `LEAVE` command.

To support both these usage, the Sentry kernel autotest API has been designed, in
association with the autotest application, for a flexible autotest activation/deactivation
model.

When being autotested, the kernel communicate with the autotest application
using specially crafted signals that only exist in autotest mode. These signals
are emitted by the kernel to the autotest application, which can receive them in the
very same way it receives all signals: through the sys_waitevent syscall.

The lonely difference here is that the signal source is the kernel (source id being `0`),
and the signal value is not a standard signal but one of the autotest specific signals,
as defined in the UAPI signal header:

.. literalinclude:: ../../../uapi/include/uapi/signal.h
   :language: c
   :lines: 24-42
   :caption: List of autotest-specific signals

Autotesting kernel components
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Autotesting Sentry module is as easy as a syscall pair:

.. figure:: ../_static/figures/autotest_mgr.png
  :width: 80%
  :alt: testing Sentry modules
  :align: center

A typical usage of such an autotest is, for example, a performance measurement of
the kernel random source:

.. code-block:: c
  :linenos:
  :caption: Entropy performance measurement through autotest

  kstatus_t mgr_security_autotest(void)
  {
    // [...]
    pr_autotest("START execute 256 entropy generation from entropy source");
    /* executing 256 random seed requests */
    for (uint32_t i=0; i < 256; ++i) {
        start = systime_get_cycle();
        if (unlikely(mgr_security_entropy_generate(&seed) != K_STATUS_OKAY)) {
            failures++;
        }
        stop = systime_get_cycle();
        uint64_t duration = stop - start;
        if (duration > max) {
            max = duration;
        }
        if ((min == 0) || (duration < min)) {
            min = duration;
        }
        average += duration;
    }
    /* average div 256 */
    average >> 8;
    pr_autotest("entropy_generate min time: %llu", min);
    pr_autotest("entropy_generate max time: %llu", max);
    pr_autotest("entropy_generate average time: %llu", average);
    pr_autotest("entropy_generate failures: %llu", failures);
    pr_autotest("END");

    return status;
  }

Kernel autotests logging
^^^^^^^^^^^^^^^^^^^^^^^^

As shown is the previous code sample, Sentry kernel autotest function use a
specially crafted log output for test execution, in order to allow kernel
logging post-processing.

The kernel autotest dediacated logging is using the `pr_autotest()` API, which
work in a very similar way to other `pr_` API of the debug manager:

.. literalinclude:: ../../../kernel/include/sentry/managers/debug.h
   :language: c
   :lines: 119-133
   :caption: Autotest dedicated kernel logging API

With such an API, test output formatting is automatically generated.

.. warning::

  The usage of autotest logging is acceptable in handler mode for autotest use case only,
  when IRQ events are under control of the test suite. huge autotest logging highly increase
  uninterruptible kernel sequence and must be considered at test design time

.. note::

  The Sentry kernel logging is voluntary IRQless and can be called in handler mode. Although,
  it should not be used in the middle of performances measurement loop without impacting it
