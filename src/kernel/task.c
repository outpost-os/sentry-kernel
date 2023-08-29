#include <inttypes.h>
#include <thread.h>

#include <task.h>

/*
 * Forge a stack context
 */
void initialize_stack_context(size_t sp, size_t pc)
{
    __thread_init_stack_context(sp, pc);
    return;
}
