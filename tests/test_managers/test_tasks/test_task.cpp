// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <iostream>
#include <sentry/ktypes.h>
#include <gtest/gtest.h>
#include <gmock/gmock.h>
#include <sentry/managers/task.h>
#include <uapi/handle.h>

struct TaskMock {
    MOCK_METHOD(void, on_task_schedule, ());
};

/* list of contexts*/
task_meta_t task_basic_context[CONFIG_MAX_TASKS];

task_meta_t task_full_context[CONFIG_MAX_TASKS];

static std::unique_ptr<TaskMock> taskMock;
/* because thse variables are global static (because
  they are used in extern 'C'), tests can't be executed in
  parallel */
static std::unique_ptr<task_meta_t*> taskCtx;
static std::unique_ptr<uint32_t> taskNum;

class TaskTest : public testing::Test {
    void SetUp() override {
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
};

extern "C" {

    uint32_t stack[256];

    extern void __attribute__((noreturn)) idle(void);
    size_t _idlestack  = (size_t)&stack;
    size_t _sidle = (size_t)idle;
    /* hardcoded by now */
    size_t _eidle = (size_t)idle + 4;

    uint32_t ut_get_numtask(void) {
        uint32_t *num = taskNum.get();
        return *num;
    }

    const task_meta_t *ut_get_task_meta_table(void) {
        const task_meta_t **t = (const task_meta_t**)taskCtx.get();
        return *t;
    }

    kstatus_t sched_schedule(taskh_t t __attribute__((unused))) {
        taskMock->on_task_schedule();
        /* only idle is scheduled */
        return K_STATUS_OKAY;
    }
}

TEST_F(TaskTest, TestForgeEmptyTable) {
    kstatus_t res;
    assign(task_basic_context, 0);
    EXPECT_CALL(*taskMock, on_task_schedule).Times(1);
    res = mgr_task_init();
    ASSERT_EQ(res, K_STATUS_OKAY);
}

TEST_F(TaskTest, TestForgeInvalidFullTable) {
    kstatus_t res;
    assign(task_basic_context, CONFIG_MAX_TASKS);
    EXPECT_CALL(*taskMock, on_task_schedule).Times(0);
    res = mgr_task_init();
    ASSERT_EQ(res, K_SECURITY_INTEGRITY);
}


TEST_F(TaskTest, TestForgeValidFullTable) {
    kstatus_t res;
    memset(task_full_context, 0x0, sizeof(task_full_context));
    uint16_t base_id = 0x1000;
    for (uint8_t i = 0; i < CONFIG_MAX_TASKS; ++i) {
        task_full_context[i].handle.id = base_id++;
        task_full_context[i].handle.familly = HANDLE_TASKID;
        task_full_context[i].magic = CONFIG_TASK_MAGIC_VALUE;
        task_full_context[i].flags = THREAD_FLAG_AUTOSTART; /* implies sched_schedule() */
        task_full_context[i].stack_top = (size_t)&stack;
        task_full_context[i].stack_size = 256;
    }
    assign(task_full_context, CONFIG_MAX_TASKS);
    EXPECT_CALL(*taskMock, on_task_schedule).Times(CONFIG_MAX_TASKS+1);
    res = mgr_task_init();
    ASSERT_EQ(res, K_STATUS_OKAY);
}
