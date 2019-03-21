/*
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file atomic_user_override.h
 * @brief Provides a method for user to override atomic implementation.
 */

#include <stdint.h>
#include <stdbool.h>

/**
 * GCC flatten/always_inline equivalent.
 *
 * @todo Define this macro, refer to compiler specific docs.
 *       Please note that, Atomic_*() functions in atomic.h are calling
 *       into user defined functions in this header file. Please make
 *       sure atomic nested function calls are "flattened" and "inlined",
 *       from caller's perspective.
 */
#define FORCE_INLINE

/**
 * GCC always_inline equivalent.
 *
 * @todo Define this macro, refer to compiler specific docs.
 *       This, in combine with FORCE_INLINE, should guarantee the atomic
 *       functions are always inlined even without compiler  optimization.
 *       The behavior can be checked with compiler objdump disassembly.
 */
#define FORCE_INLINE_NESTED

/**
 * GCC __asm__ __volatile__ equivalent.
 *
 * @todo Optionally define this macro, refer to compiler specific docs.
 */
#define COMPILER_ASM_VOLATILE

/**
 * Atomic user defined implementations.
 *
 * @todo Implement ALL below functions.
 *
 * @note Here, we are mearly providing extension points for user to
 *       supply their own atomic implementation. It's solely up to user
 *       to validate whether the implementation is correct.
 *
 *       Though, two suggested approaches --
 *       (1) (always works) Emulate atomic with critical section.
 *       (2) (recommended) ISA supported atomic instruction(s).
 *
 * <b> Example -- Emulating atomic with critical section</b>
 * @code{.c}
 * static FORCE_INLINE int32_t Atomic_Add_i32_User_Override(int32_t volatile * pAddend, int32_t lCount)
 * {
 *     int32_t lCurrent;
 *     CriticalSectionType_t temp;
 *
 *     // Platform specific definition of enter/exit critical section.
 *     // The return value from enter critical section function call
 *     // could be previous interrupt mask or priority.
 *     temp = ENTER_CRITICAL_SECTION( );
 *     lCurrent = *pAddend;
 *     *pAddend += lCount;
 *     EXIT_CRITICAL_SECTION( temp );
 *
 *     return lCurrent;
 * }
 * @endcode
 *
 * <b> Example -- ISA supported atomic instruction(s), with compiler support.</b>
 * @code{.c}
 * // A compiler has atomic built-in extension.
 * // Include atomic header in app code.
 *
 * static FORCE_INLINE int32_t Atomic_Add_i32_User_Override(int32_t volatile * pAddend, int32_t lCount)
 * {
 *     // Assume atomic_fetch_add() does something similar to GCC __atomic_fetch_add()
 *     // with memory order __ATOMIC_SEQ_CST.
 *     return atomic_fetch_add(pAddend, lCount);
 * }
 * @endcode
 *
 * <b> Example -- ISA supported atomic instructions(s), without compiler built-in function.</b>
 * @code{.c}
 * static FORCE_INLINE int32_t Atomic_Add_i32_User_Override(int32_t volatile * pAddend, int32_t lCount)
 * {
 *     // assembly, if you have to.
 *     __asm__ __volatile__(......);
 * }
 * @endcode
 *
 */

/*----------------------------- Swap && CAS ------------------------------*/
static FORCE_INLINE_NESTED uint32_t Atomic_CompareAndSwap_u32_User_Override( uint32_t volatile * pDestination,
                                                                             uint32_t ulExchange,
                                                                             uint32_t ulComparand );
static FORCE_INLINE_NESTED void * Atomic_SwapPointers_p32_User_Override( void * volatile * ppDestination,
                                                                         void * pExchange );
static FORCE_INLINE_NESTED uint32_t Atomic_CompareAndSwapPointers_p32_User_Override( void * volatile * ppDestination,
                                                                                     void * pExchange,
                                                                                     void * pComparand );

/*----------------------------- Arithmetic ------------------------------*/
static FORCE_INLINE_NESTED uint32_t Atomic_Add_u32_User_Override( uint32_t volatile * pAddend,
                                                                  uint32_t lCount );
static FORCE_INLINE_NESTED uint32_t Atomic_Subtract_u32_User_Override( uint32_t volatile * pAddend,
                                                                       uint32_t lCount );
static FORCE_INLINE_NESTED uint32_t Atomic_Increment_u32_User_Override( uint32_t volatile * pAddend );
static FORCE_INLINE_NESTED uint32_t Atomic_Decrement_u32_User_Override( uint32_t volatile * pAddend );

/*----------------------------- Bitwise Logical ------------------------------*/
static FORCE_INLINE_NESTED uint32_t Atomic_OR_u32_User_Override( uint32_t volatile * pDestination,
                                                                 uint32_t ulValue );
static FORCE_INLINE_NESTED uint32_t Atomic_AND_u32_User_Override( uint32_t volatile * pDestination,
                                                                  uint32_t ulValue );
static FORCE_INLINE_NESTED uint32_t Atomic_NAND_u32_User_Override( uint32_t volatile * pDestination,
                                                                   uint32_t ulValue );
static FORCE_INLINE_NESTED uint32_t Atomic_XOR_u32_User_Override( uint32_t volatile * pDestination,
                                                                  uint32_t ulValue );
