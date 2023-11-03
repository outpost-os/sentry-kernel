// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <random>
#include <iostream>
#include <stdarg.h>
#include <stdio.h>
#include <sentry/ktypes.h>
#include <gtest/gtest.h>
#include <gmock/gmock.h>
#include <sentry/managers/task.h>
#include <uapi/handle.h>
/* needed to get back private struct task_t for anaysis */
#include "../../../src/managers/task/task_core.h"

struct TaskMock {
    MOCK_METHOD(void, on_task_schedule, ());
};

/* list of contexts*/
task_meta_t task_basic_context[CONFIG_MAX_TASKS];

task_meta_t task_full_context[CONFIG_MAX_TASKS];

/* manager private tab (extern). Used for post-exec checks */
extern task_t task_table[CONFIG_MAX_TASKS+1];

static std::unique_ptr<TaskMock> taskMock;
/* because thse variables are global static (because
  they are used in extern 'C'), tests can't be executed in
  parallel */
static std::unique_ptr<task_meta_t*> taskCtx;
static std::unique_ptr<uint32_t> taskNum;

class TaskTest : public testing::Test {
    void SetUp() override {
        if (std::getenv("CI")) {
            GTEST_SKIP() << "Skipping in CI mode (OOM problem)";
        }
        taskMock = std::make_unique<TaskMock>();
    }

    void TearDown() override {
        taskMock.reset();
        taskCtx.reset();
        taskNum.reset();
    }
protected:
    void assign(task_meta_t* ctx, uint32_t num) {
        taskCtx = std::make_unique<task_meta_t*>(ctx);
        taskNum = std::make_unique<uint32_t>(num);
    }
    uint16_t gen_label(void) {
        std::random_device rd;
        std::mt19937 gen(rd());
        uint16_t max = std::numeric_limits<uint16_t>::max();

        std::uniform_int_distribution<> distrib(1, max);
        return distrib(gen);
    };

    bool is_ordered(task_t *tab) {
        bool res = true;
        for (uint8_t i = 0; i < CONFIG_MAX_TASKS; ++i) {
            if (tab[i+1].metadata == NULL) {
                break;
            }
            if (tab[i].metadata->handle.id > tab[i+1].metadata->handle.id) {
                res = false;
            }
        }
        return res;
    }
};


/**
 * This part contains all the stack manager glue.
 * This include ldscript variable mocks, including numtask
 * and metadata table, replaced by a dynamic forge through the
 * taskTest object
 */
extern "C" {

    /* sample stack area used to let task manager forge a stack */
    uint64_t _idlestack[64];
    /* we emulate _idletask ld label, although, this label
       is manipulated using its address as stack top, meaning that
       we need some space **bellow** as if the label was properly
       positioned in memory to let the task manager manipulating the
       memory. This is done with some _otherstack spacing just
       after, so that &_idlestack usage in sp configuration will store
       content in _shadowstack */
    uint64_t _shadowstack[64];

    /* sample idle function and associated infos */
    extern void __attribute__((noreturn)) idle(void);

    size_t _sidle = (size_t)idle;
    size_t _eidle = (size_t)idle + 4;

    /*
     * numtask var is replaced by a dyn call to this function,
     *  in TEST_MODE, so that each test can use separated values for
     */
    uint32_t ut_get_numtask(void) {
        uint32_t *num = taskNum.get();
        return *num;
    }

    /*
     * task metadata table is replaced by a dynamic pointer reference
     * so that various tables can be used in various tests
     */
    const task_meta_t *ut_get_task_meta_table(void) {
        const task_meta_t **t = (const task_meta_t**)taskCtx.get();
        return *t;
    }

    /*
     * scheduler mocking. Associated to mocking mechanism so that
     * we can detect how many call are made to the sheduler in each
     * test (autostart flag check)
     */
    kstatus_t sched_schedule(taskh_t t __attribute__((unused))) {
        taskMock->on_task_schedule();
        /* only idle is scheduled */
        return K_STATUS_OKAY;
    }

    /*
     * overloading printk() with standard printf
     */
    kstatus_t printk(const char *fmt __attribute__((unused)), ...) {
#if 0
        /* do this to reenable logging, if needed */
        va_list args;
        va_start(args, fmt);
        vprintf(fmt, args);
        va_end(args);
#endif
        return K_STATUS_OKAY;
    }

}


/*
 * basic testing: empty table, should only result in idle sched
 */
TEST_F(TaskTest, TestForgeEmptyTable) {
    kstatus_t res;
    assign(task_basic_context, 0);
    EXPECT_CALL(*taskMock, on_task_schedule).Times(1);
    res = mgr_task_init();
    ASSERT_EQ(res, K_STATUS_OKAY);
}

/*
 * invalid table (invalid magic field), should fail with security flag
 */
TEST_F(TaskTest, TestForgeInvalidFullTable) {
    kstatus_t res;
    assign(task_basic_context, CONFIG_MAX_TASKS);
    EXPECT_CALL(*taskMock, on_task_schedule).Times(0);
    res = mgr_task_init();
    ASSERT_EQ(res, K_SECURITY_INTEGRITY);
}

/*
 * valid, ordered label, full table, should forge a complete table
 */
TEST_F(TaskTest, TestForgeValidFullTable) {
    kstatus_t res;
    memset(task_full_context, 0x0, sizeof(task_full_context));
    uint16_t base_id = 0x1000;
    for (uint8_t i = 0; i < CONFIG_MAX_TASKS; ++i) {
        task_full_context[i].handle.id = base_id++;
        task_full_context[i].handle.familly = HANDLE_TASKID;
        task_full_context[i].magic = CONFIG_TASK_MAGIC_VALUE;
        task_full_context[i].flags = THREAD_FLAG_AUTOSTART; /* implies sched_schedule() */
        task_full_context[i].stack_top = (size_t)&_idlestack;
        task_full_context[i].stack_size = 256;
    }
    assign(task_full_context, CONFIG_MAX_TASKS);
    EXPECT_CALL(*taskMock, on_task_schedule).Times(CONFIG_MAX_TASKS+1);
    res = mgr_task_init();
    ASSERT_EQ(res, K_STATUS_OKAY);
    ASSERT_EQ(is_ordered(task_table), true);
}

/*
 * valid, unordered labels, full table, should forge a complete table
 * check that ordering by label works (for runtime tree check optimization)
 */
TEST_F(TaskTest, TestForgeValidUnorderedLabelsTable) {
    kstatus_t res;

    memset(task_full_context, 0x0, sizeof(task_full_context));
    for (uint8_t i = 0; i < CONFIG_MAX_TASKS; ++i) {
        task_full_context[i].handle.id = gen_label();
        task_full_context[i].handle.familly = HANDLE_TASKID;
        task_full_context[i].magic = CONFIG_TASK_MAGIC_VALUE;
        task_full_context[i].flags = THREAD_FLAG_AUTOSTART; /* implies sched_schedule() */
        task_full_context[i].stack_top = (size_t)&_idlestack;
        task_full_context[i].stack_size = 256;
    }
    assign(task_full_context, CONFIG_MAX_TASKS);
    EXPECT_CALL(*taskMock, on_task_schedule).Times(CONFIG_MAX_TASKS+1);
    res = mgr_task_init();
    ASSERT_EQ(res, K_STATUS_OKAY);
    ASSERT_EQ(is_ordered(task_table), true);
}
