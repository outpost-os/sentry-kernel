#include "sync.h"

void mutex_init(uint32_t * mutex)
{
    set_u32_with_membarrier(mutex, 1);
}

/*
 * Try to lock the current semaphore
 */
bool mutex_trylock(uint32_t * mutex)
{
    return _semaphore_trylock(mutex);
}

void mutex_lock(uint32_t * mutex)
{
    bool    is_locked = false;

    do {
        is_locked = _semaphore_trylock(mutex);
    } while (!is_locked);
}


void mutex_unlock(uint32_t * mutex)
{
    bool    ret;

    do {
        ret = _semaphore_release(mutex);
    } while (ret == false);
}

bool mutex_tryunlock(uint32_t * mutex)
{
    return _semaphore_release(mutex);
}
