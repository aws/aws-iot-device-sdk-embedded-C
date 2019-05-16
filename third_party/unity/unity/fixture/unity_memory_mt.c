/* Wrappers that make the unity memory functions thread-safe. */

#include <stddef.h>

/* unity memory functions. */
extern void* unity_malloc(size_t size);
extern void* unity_calloc(size_t num, size_t size);
extern void* unity_realloc(void* oldMem, size_t size);
extern void unity_free_mt(void* mem);

/* Function pointers to begin/end critical section functions. */
static void(*unity_critical_section_start)(void) = NULL;
static void(*unity_critical_section_end)(void) = NULL;

void unity_provide_critical_section(void(*start)(void), void(*end)(void))
{
    unity_critical_section_start = start;
    unity_critical_section_end = end;
}

void unity_enter_critical_section(void)
{
    if(unity_critical_section_start != NULL)
    {
        unity_critical_section_start();
    }
}

void unity_exit_critical_section(void)
{
    if(unity_critical_section_end != NULL)
    {
        unity_critical_section_end();
    }
}

void* unity_malloc_mt(size_t size)
{
    void* mem = NULL;

    unity_enter_critical_section();

    mem = unity_malloc(size);

    unity_exit_critical_section();

    return mem;
}

void* unity_calloc_mt(size_t num, size_t size)
{
    void* mem = NULL;

    unity_enter_critical_section();

    mem = unity_calloc(num, size);

    unity_exit_critical_section();

    return mem;
}

void* unity_realloc_mt(void * oldMem, size_t size)
{
    void* mem = NULL;

    unity_enter_critical_section();

    mem = unity_realloc(oldMem, size);

    unity_exit_critical_section();

    return mem;
}

void unity_free_mt(void * mem)
{
    unity_enter_critical_section();

    unity_free(mem);

    unity_exit_critical_section();
}
