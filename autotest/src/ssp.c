#include <uapi.h>

void __stack_chk_fail(void)
{
    /* End of task. NOTE: stack corruption is a serious security issue */
    sys_exit(STATUS_CRITICAL);
    while (1) {
    };
}
