/* Wrappers that make the unity memory functions thread-safe. Implemented for
 * POSIX systems. */

#include "unity_fixture_malloc_overrides.h"
#include <pthread.h>

pthread_mutex_t CriticalSectionMutex = PTHREAD_MUTEX_INITIALIZER;

extern void* unity_malloc(size_t size);
extern void* unity_calloc(size_t num, size_t size);
extern void* unity_realloc(void* oldMem, size_t size);
extern void unity_free_mt(void* mem);

void* unity_malloc_mt(size_t size)
{
    void* mem = NULL;

    if (pthread_mutex_lock(&CriticalSectionMutex) != 0) return NULL;

    mem = unity_malloc(size);

    if (pthread_mutex_unlock(&CriticalSectionMutex) != 0)
    {
        unity_free(mem);
        mem = NULL;
    }

    return mem;
}

void* unity_calloc_mt(size_t num, size_t size)
{
    void* mem = NULL;

    if (pthread_mutex_lock(&CriticalSectionMutex) != 0) return NULL;

    mem = unity_calloc(num, size);

    if (pthread_mutex_unlock(&CriticalSectionMutex) != 0)
    {
        unity_free(mem);
        mem = NULL;
    }

    return mem;
}

void* unity_realloc_mt(void * oldMem, size_t size)
{
    void* mem = NULL;

    if (pthread_mutex_lock(&CriticalSectionMutex) != 0) return NULL;

    mem = unity_realloc(oldMem, size);

    if (pthread_mutex_unlock(&CriticalSectionMutex) != 0)
    {
        unity_free(mem);
        mem = NULL;
    }

    return mem;
}

void unity_free_mt(void * mem)
{
    pthread_mutex_lock(&CriticalSectionMutex);

    unity_free(mem);

    pthread_mutex_unlock(&CriticalSectionMutex);
}
