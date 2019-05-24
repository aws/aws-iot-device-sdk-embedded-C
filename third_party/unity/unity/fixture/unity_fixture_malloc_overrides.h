/* Copyright (c) 2010 James Grenning and Contributed to Unity Project
 * ==========================================
 *  Unity Project - A Test Framework for C
 *  Copyright (c) 2007 Mike Karlesky, Mark VanderVoord, Greg Williams
 *  [Released under MIT License. Please refer to license.txt for details]
 * ========================================== */

#ifndef UNITY_FIXTURE_MALLOC_OVERRIDES_H_
#define UNITY_FIXTURE_MALLOC_OVERRIDES_H_

#include <stdbool.h>
#include <stddef.h>

#ifdef UNITY_EXCLUDE_STDLIB_MALLOC
/* Define this macro to remove the use of stdlib.h, malloc, and free.
 * Many embedded systems do not have a heap or malloc/free by default.
 * This internal unity_malloc() provides allocated memory deterministically from
 * the end of an array only, unity_free() only releases from end-of-array,
 * blocks are not coalesced, and memory not freed in LIFO order is stranded. */
    #ifndef UNITY_INTERNAL_HEAP_SIZE_BYTES
    #define UNITY_INTERNAL_HEAP_SIZE_BYTES 4096
    #endif
#endif

/* These functions are used by the Unity Fixture to allocate and release memory
 * on the heap and can be overridden with platform-specific implementations.
 * For example, when using FreeRTOS UNITY_FIXTURE_MALLOC becomes pvPortMalloc()
 * and UNITY_FIXTURE_FREE becomes vPortFree(). */
#if !defined(UNITY_FIXTURE_MALLOC) || !defined(UNITY_FIXTURE_FREE)
    #include <stdlib.h>
    #define UNITY_FIXTURE_MALLOC(size) malloc(size)
    #define UNITY_FIXTURE_FREE(ptr)    free(ptr)
#else
    extern void* UNITY_FIXTURE_MALLOC(size_t size);
    extern void UNITY_FIXTURE_FREE(void* ptr);
#endif

#define malloc  unity_malloc_mt
#define calloc  unity_calloc_mt
#define realloc unity_realloc_mt
#define free    unity_free_mt

bool UnityMalloc_AllocateResource(void);
void UnityMalloc_FreeResource(void);

void unity_provide_critical_section(void(*start)(void), void(*end)(void));
void unity_enter_critical_section(void);
void unity_exit_critical_section(void);

void* unity_malloc_mt(size_t size);
void* unity_calloc_mt(size_t num, size_t size);
void* unity_realloc_mt(void * oldMem, size_t size);
void unity_free_mt(void * mem);

#endif /* UNITY_FIXTURE_MALLOC_OVERRIDES_H_ */
