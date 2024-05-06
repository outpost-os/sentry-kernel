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
#include <sentry/managers/memory.h>
#include <uapi/handle.h>
/* needed to get back private struct task_t for analysis */
#include "../../../src/managers/task/task_core.h"

struct TaskMock {
    MOCK_METHOD(void, on_task_schedule, ());
};

/* manager private tab (extern). Used for post-exec checks */
extern task_t task_table[CONFIG_MAX_TASKS+1];

static std::weak_ptr<TaskMock> taskMock_weak;

/* because thse variables are global static (because
  they are used in extern 'C'), tests can't be executed in
  parallel */
static task_meta_t* taskCtx = nullptr;

class TaskTest : public testing::Test {

    void SetUp() override {
        taskMock = std::make_shared<TaskMock>();
        taskMock_weak = taskMock;
        taskCtx = task_meta;
    }

protected:
    uint32_t gen_label(void) {
        std::random_device rd;
        std::mt19937 gen(rd());
        uint16_t max = std::numeric_limits<uint16_t>::max();

        std::uniform_int_distribution<> distrib(1, max);
        return (uint32_t)(distrib(gen));
    };

    std::shared_ptr<TaskMock> taskMock;
    // List initialization (a.k.a. curly braces initialization) uses default ctor foreach struct member
    task_meta_t task_meta[CONFIG_MAX_TASKS]{};
};


/**
 * This part contains all the stack manager glue.
 * This include ldscript variable mocks, including
 * and metadata table, replaced by a dynamic forge through the
 * taskTest object
 */
extern "C" {

    /* sample stack area used to let task manager forge a stack */
    uint8_t task_data_section[1024];
    size_t _idle_svcexchange;
    size_t _autotest_svcexchange;

    /* sample idle function and associated infos */
    [[noreturn]] void ut_idle(void) {
        while (1) { asm volatile ("nop" ::: "memory"); }
    }

    [[noreturn]] void ut_autotest(void) {
        while (1) { asm volatile ("nop" ::: "memory"); }
    }

    size_t _sidle = (size_t)ut_idle;
    size_t _eidle = (size_t)ut_idle + 0x400;
    size_t _sautotest = (size_t)ut_autotest;
    size_t _eautotest = (size_t)ut_autotest + 0x400;

    /*
     * task metadata table is replaced by a dynamic pointer reference
     * so that various tables can be used in various tests
     */
    const task_meta_t *ut_get_task_meta_table(void) {
        return taskCtx;
    }

    kstatus_t mgr_mm_forge_empty_table(layout_resource_t *ressource_tab)
    {
        for (uint8_t i = 0; i < TASK_MAX_RESSOURCES_NUM; i++) {
            memset(&ressource_tab[i], 0x0, sizeof(layout_resource_t));
        }
        return K_STATUS_OKAY;
    }
    kstatus_t mgr_mm_map_svcexchange(taskh_t t [[maybe_unused]])
    {
        return K_STATUS_OKAY;
    }

/* fast implementation of task mapping.
   map all task currently mapped ressources. all empty user regions are cleared
*/
    kstatus_t mgr_mm_map_task(taskh_t t __attribute__((unused)))
    {
        return K_STATUS_OKAY;
    }

    kstatus_t mgr_security_entropy_generate(uint32_t*rng)
    {
        *rng = 0x1e51UL;
        return K_STATUS_OKAY;
    }

    kstatus_t mgr_mm_forge_ressource(mm_region_t reg_type __attribute__((unused)),
                                     taskh_t t __attribute__((unused)),
                                     layout_resource_t *ressource __attribute__((unused)))
    {
        return K_STATUS_OKAY;
    }
    /*
     * scheduler mocking. Associated to mocking mechanism so that
     * we can detect how many call are made to the sheduler in each
     * test (autostart flag check)
     */
    kstatus_t sched_schedule(taskh_t t __attribute__((unused))) {
        auto taskMock = taskMock_weak.lock();
        if (taskMock != nullptr) {
            taskMock->on_task_schedule();
        }
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

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
    /* only autotest is scheduled */
    EXPECT_CALL(*taskMock, on_task_schedule).Times(1);
#else
    EXPECT_CALL(*taskMock, on_task_schedule).Times(0);
#endif
    res = mgr_task_init();
    ASSERT_EQ(res, K_STATUS_OKAY);
}

/*
 * invalid table (invalid magic field), should fail with security flag
 */
TEST_F(TaskTest, TestForgeInvalidFullTable) {
    kstatus_t res;

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
    /* only autotest is scheduled */
    EXPECT_CALL(*taskMock, on_task_schedule).Times(1);
#else
    EXPECT_CALL(*taskMock, on_task_schedule).Times(0);
#endif
    res = mgr_task_init();
    /* no user task found, only idle (and potentially autotest)*/
    ASSERT_EQ(res, K_STATUS_OKAY);
}

/*
 * valid, ordered label, full table, should forge a complete table
 */
TEST_F(TaskTest, TestForgeValidFullTable) {
    kstatus_t res;
    uint16_t base_id = 0x1000;
    for (uint8_t i = 0; i < CONFIG_MAX_TASKS; ++i) {
        task_meta[i].label = (uint32_t)(base_id << 13);
        task_meta[i].magic = CONFIG_TASK_MAGIC_VALUE;
        task_meta[i].flags.start_mode = JOB_FLAG_START_AUTO; /* implies sched_schedule() */
        task_meta[i].flags.exit_mode = JOB_FLAG_EXIT_NORESTART;
        task_meta[i].s_svcexchange = (size_t)&task_data_section[0];
        task_meta[i].stack_size = 256;
        task_meta[i].data_size = 0;
        task_meta[i].bss_size = 0;
        task_meta[i].heap_size = 0;
        task_meta[i].rodata_size = 0;
    }

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
    /* only autotest is scheduled */
    EXPECT_CALL(*taskMock, on_task_schedule).Times(1);
#else
    EXPECT_CALL(*taskMock, on_task_schedule).Times(CONFIG_MAX_TASKS);
#endif
    res = mgr_task_init();
    ASSERT_EQ(res, K_STATUS_OKAY);
}

/*
 * valid, unordered labels, full table, should forge a complete table
 * check that ordering by label works (for runtime tree check optimization)
 */
TEST_F(TaskTest, TestForgeValidUnorderedLabelsTable) {
    kstatus_t res;

    for (uint8_t i = 0; i < CONFIG_MAX_TASKS; ++i) {
        task_meta[i].label = gen_label();
        task_meta[i].magic = CONFIG_TASK_MAGIC_VALUE;
        task_meta[i].flags.start_mode = JOB_FLAG_START_AUTO; /* implies sched_schedule() */
        task_meta[i].flags.exit_mode = JOB_FLAG_EXIT_NORESTART;
        task_meta[i].s_svcexchange = (size_t)&task_data_section[0];
        task_meta[i].stack_size = 256;
        task_meta[i].data_size = 0;
        task_meta[i].bss_size = 0;
        task_meta[i].heap_size = 0;
        task_meta[i].rodata_size = 0;
    }

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
    /* only autotest is scheduled */
    EXPECT_CALL(*taskMock, on_task_schedule).Times(1);
#else
    EXPECT_CALL(*taskMock, on_task_schedule).Times(CONFIG_MAX_TASKS);
#endif
    res = mgr_task_init();
    ASSERT_EQ(res, K_STATUS_OKAY);
}
