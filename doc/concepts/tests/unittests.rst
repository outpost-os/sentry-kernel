Unit testing Sentry
-------------------

.. _unittest:

.. index::
    single: unit test; model
    single: unit test; test suites
    single: gtest; tests design

Unit testing framework
""""""""""""""""""""""

Even if the Sentry kernel is built for embedded, it is not, even for drivers testing,
a problem to execute unit testing in order to validate C-level (or Rust level)
behavior analysis.
The global test model is that any peace of code in Sentry can be extracted, compiled for
x86_64, and linked to a test source that implement the potential missing blocs and
validate the behavior of the code under test in various cases. This peace of code,
when being tested, *system under test* (SUT).

.. note::
    SUT (System under test) is a test terminology defined by the
    `International Software Testing Qualifications Board <https://www.istqb.org/#welcome>`_,
    for software-related testing

To do that, the gtest framework delivers multiple useful components such as
mocks, to trigger execution of test fixtures when the source code calls external
symbols. In the same time, the usage of C++ allows templated testing, that
permit to forge a great amount of inputs and stimulii to various Sentry modules.

The Sentry tests suites are natively integrated into meson and are the following:

   * ut-managers: test suite targetting managers
   * ut-bsp: test suite targetting drivers
   * ut-utils: test suite targetting generic kernel utilities and core library


The Sentry test support is integrated into the build system, and associated to the
Sentry static analyser to ensure coverage metrics.

.. index::
    single: unit test; development constraint
    single: unit test; architectural model

Building and testing modules on build host
""""""""""""""""""""""""""""""""""""""""""

Each subcomponent of Sentry is made to use a controlled, clearly defined, external
API, so that it is easy to unit test each Sentry subcomponent separately by
mocking the used external API symbols.

Mocking symbols also allows multiple interesting test-level measurements such as:

   * validating the behavior of the tested module when the mocked symbol returns
     various test-controlled values using test scenarios.
   * checking mocked symbols input values given by the tested module
   * count the number of execution of the mocked symbol

All unit tests are compiled natively, meaning that the kernel code is built for
the build machine, which is, most of the time, a x86_64 device. This requires the
Sentry kernel code to be **portable**, and thus respects the usual coding
best practices.

.. index::
    single: gmock; usage
    single: gmock; example

Mocking externals, checking behaviors
"""""""""""""""""""""""""""""""""""""

With such a framework model, we can write unit tests that check multiple behaviors
of the SUT, including temporal behavior if needed.

As an example, th following describes a little subset of the Sentry unit test framework,
targetting the task manager as SUT:

.. code-block:: cpp
    :linenos:

    struct TaskMock {
        MOCK_METHOD(void, on_task_schedule, ());
    };

    [...]
    // Mocking sched_schedule() API
    kstatus_t sched_schedule(taskh_t t __attribute__((unused))) {
        taskMock->on_task_schedule();
        /* only idle is scheduled */
        return K_STATUS_OKAY;
    }

This block of code emulates one the kernel function, `sched_schedule()`, which is
called by the task manager for all discovered task that can be started at boot time.

We can then consider the following test:

.. code-block:: c
    :linenos:

    TEST_F(TaskTest, TestForgeEmptyTable) {
        kstatus_t res;
        /* assign empty task table as input */
        self.assign(task_basic_context);
        /* 1. defining the expected results */
    #ifdef CONFIG_BUILD_TARGET_AUTOTEST
        /* only autotest is scheduled */
        EXPECT_CALL(*taskMock, on_task_schedule).Times(1);
    #else
        /* empty table, no task should be scheduled */
        EXPECT_CALL(*taskMock, on_task_schedule).Times(0);
    #endif
        /* 2. executing the code under test */
        res = mgr_task_init();
        /* 3. checking that the code under test returns OKAY */
        ASSERT_EQ(res, K_STATUS_OKAY);
    }

This test verify that given an empty task list context, the scheduler is never
called in nominal mode, and call once in autotest mode.

Each unit test should be kept as simple as possible to simplify the debugging
step on test failure. It also reduces the risk of test-related bugs.

.. note::
    As each Sentry module is clearly defined and its behavior being documented,
    the unit test suite associated to each module can be written separately from
    the module itself, even by someone else, ensuring the test suite efficiency
