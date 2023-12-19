#include <uapi.h>

void __stack_chk_fail(void)
{
    sys_exit(STATUS_CRITICAL);
    while (1) {
    };
}
