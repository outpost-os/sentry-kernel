#ifndef LIBTEST_ASSERT_H
#define LIBTEST_ASSERT_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <testlib/log.h>

static inline void failure(char *file, int line, const char*failure) {
    pr_autotest("FAIL: %s", failure);
}

#define ASSERT(expr,failmsg) ({do { \
    if (!(expr)) \
        failure(__FILE__, __LINE__, failmsg); \
} while (0);})

#define ASSERT_EQ(a,b) (ASSERT((a) == (b), "not equal"))

#define ASSERT_NE(a,b) (ASSERT((a) != (b), "equal"))

#define ASSERT_GT(a,b) (ASSERT((a) > (b), "a not greater than b"))

#define ASSERT_GE(a,b) (ASSERT((a) >= (b), "b greater than a"))

#define ASSERT_LT(a,b) (ASSERT((a) < (b), "b not greater than a"))

#define ASSERT_LE(a,b) (ASSERT((a) <= (b), "a greater than b"))

#ifdef __cplusplus
}
#endif

#endif
