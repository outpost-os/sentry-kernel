#ifndef LIBTEST_ASSERT_H
#define LIBTEST_ASSERT_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <testlib/log.h>


#define ASSERT(expr,failcmp, successcmp, a, b) ({do {   \
    if (!(expr))                                        \
        failure(__func__, __LINE__, failcmp, a, b);     \
    else                                                \
        success(__func__, __LINE__, successcmp, a, b);  \
} while (0);})

/**
 * Only for integer based type (uint, int, long, size_t, etc.)
 */
#define ASSERT_EQ(a,b) (ASSERT((a) == (b), "!=", "==", a, (typeof(a))b))

#define ASSERT_NE(a,b) (ASSERT((a) != (b), "==", "!=", a, (typeof(a))b))

#define ASSERT_GT(a,b) (ASSERT((a) > (b), "<=", ">", a, (typeof(a))b))

#define ASSERT_GE(a,b) (ASSERT((a) >= (b), "<", ">=", a, (typeof(a))b))

#define ASSERT_LT(a,b) (ASSERT((a) < (b), ">=", "<", a, (typeof(a))b))

#define ASSERT_LE(a,b) (ASSERT((a) <= (b), ">", "<=", a, (typeof(a))b))

#ifdef __cplusplus
}
#endif

#endif
