/* Wrappers that make the unity memory functions thread-safe. */

#include "iot_config.h"
#include "platform/iot_threads.h"

IotMutex_t UnityMallocMutex;

extern void* unity_malloc(size_t size);
extern void* unity_calloc(size_t num, size_t size);
extern void* unity_realloc(void* oldMem, size_t size);
extern void unity_free_mt(void* mem);

void* unity_malloc_mt(size_t size)
{
    void* mem = NULL;

    IotMutex_Lock(&UnityMallocMutex);

    mem = unity_malloc(size);

    IotMutex_Unlock(&UnityMallocMutex);

    return mem;
}

void* unity_calloc_mt(size_t num, size_t size)
{
    void* mem = NULL;

    IotMutex_Lock(&UnityMallocMutex);

    mem = unity_calloc(num, size);

    IotMutex_Unlock(&UnityMallocMutex);

    return mem;
}

void* unity_realloc_mt(void * oldMem, size_t size)
{
    void* mem = NULL;

    IotMutex_Lock(&UnityMallocMutex);

    mem = unity_realloc(oldMem, size);

    IotMutex_Unlock(&UnityMallocMutex);

    return mem;
}

void unity_free_mt(void * mem)
{
    IotMutex_Lock(&UnityMallocMutex);

    unity_free(mem);

    IotMutex_Unlock(&UnityMallocMutex);
}
