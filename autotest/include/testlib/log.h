#ifndef LIBTEST_LOG_H
#define LIBTEST_LOG_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <stdarg.h>
#include <stddef.h>
#include <uapi/uapi.h>

#define USER_AUTOTEST "[AT]"
#define USER_AUTOTEST_INFO    "[INFO      ]"
#define USER_AUTOTEST_EXEC    "[EXE       ]"
#define USER_AUTOTEST_START   "[START     ]"
#define USER_AUTOTEST_END     "[END       ]"
#define USER_AUTOTEST_FAIL    "[KO        ]"
#define USER_AUTOTEST_SUCCESS "[SUCCESS   ]"
#define USER_AUTOTEST_START_SUITE   "[STARTSUITE]"
#define USER_AUTOTEST_END_SUITE     "[ENDSUITE  ]"

#define pr_autotest_fmt(func, line, fmt) "%s:%d: " fmt "\n", func, line

/**
 * @def autotest messages
 */
#define pr_autotest(type, func, line, fmt, ...) \
	printf(USER_AUTOTEST type " " pr_autotest_fmt(func, line, fmt), ##__VA_ARGS__)

#define TEST_START() do { \
    pr_autotest(USER_AUTOTEST_START, __func__, __LINE__, ""); \
} while (0)

#define TEST_END() do { \
    pr_autotest(USER_AUTOTEST_END, __func__, __LINE__, ""); \
} while (0)

#define TEST_SUITE_START(suitename) do { \
    pr_autotest(USER_AUTOTEST_START_SUITE, __func__, __LINE__, suitename); \
} while (0)

#define TEST_SUITE_END(suitename) do { \
    pr_autotest(USER_AUTOTEST_END_SUITE, __func__, __LINE__, suitename); \
} while (0)


static inline void failure_u32(const char *func, int line, const char*failure, uint32_t a, uint32_t b) {
    pr_autotest(USER_AUTOTEST_FAIL, func, line, "%lu %s %lu", a, failure, b);
}

static inline void success_u32(const char *func, int line, const char*success, uint32_t a, uint32_t b) {
    pr_autotest(USER_AUTOTEST_SUCCESS, func, line, "%lu %s %lu", a, success, b);
}

static inline void failure_u64(const char *func, int line, const char*failure, uint64_t a, uint64_t b) {
    pr_autotest(USER_AUTOTEST_FAIL, func, line, "%llu %s %llu", a, failure, b);
}

static inline void success_u64(const char *func, int line, const char*success, uint64_t a, uint64_t b) {
    pr_autotest(USER_AUTOTEST_SUCCESS, func, line, "%llu %s %llu", a, success, b);
}

static inline void failure_int(const char *func, int line, const char*failure, int a, int b) {
    pr_autotest(USER_AUTOTEST_FAIL, func, line, "%d %s %d", a, failure, b);
}


static inline void success_int(const char *func, int line, const char*success, int a, int b) {
    pr_autotest(USER_AUTOTEST_SUCCESS, func, line, "%d %s %d", a, success, b);
}


#define success(f, l, msg, T,U) _Generic((T),   \
    uint32_t: _Generic((U),                     \
        uint32_t: success_u32,                  \
        int: success_u32,                       \
        uint64_t: success_u64,                  \
        Status: success_u32                     \
    )(f,l,msg,T,U),                             \
    uint64_t: _Generic((U),                     \
        uint32_t: success_u64,                  \
        uint64_t: success_u64,                  \
        Status: success_u64,                    \
        int: success_u64                        \
    )(f,l,msg,T,U),                             \
    int: _Generic((U),                          \
        int: success_int,                       \
        uint32_t: failure_u64,                  \
        uint64_t: failure_u64,                  \
        Status: success_int                     \
    )(f,l,msg,T,U),                             \
    Status: _Generic((U),                       \
        uint32_t: success_u32,                  \
        uint64_t: success_u64,                  \
        int: success_u32,                       \
        Status: success_u32                     \
    )(f,l,msg,T,U)                              \
)

#define failure(f, l, msg, T,U) _Generic((T),   \
    uint32_t: _Generic((U),                     \
        uint32_t: failure_u32,                  \
        uint64_t: failure_u64,                  \
        Status: failure_u32,                    \
        int: success_u32                        \
    )(f,l,msg,T,U),                             \
    uint64_t: _Generic((U),                     \
        uint32_t: failure_u64,                  \
        uint64_t: failure_u64,                  \
        Status: failure_u64,                    \
        int: success_u64                        \
    )(f,l,msg,T,U),                             \
    int: _Generic((U),                          \
        uint32_t: failure_u32,                  \
        uint64_t: failure_u64,                  \
        int: success_int,                       \
        Status: success_int                     \
    )(f,l,msg,T,U),                             \
    Status: _Generic((U),                       \
        uint32_t: failure_u32,                  \
        uint64_t: failure_u64,                  \
        int: success_u32,                       \
        Status: failure_u32                     \
    )(f,l,msg,T,U)                              \
)

#define LOG(fmt, ...) \
    printf(USER_AUTOTEST USER_AUTOTEST_INFO " " pr_autotest_fmt(__func__, __LINE__, fmt), ##__VA_ARGS__)

#ifdef __cplusplus
}
#endif

#endif
