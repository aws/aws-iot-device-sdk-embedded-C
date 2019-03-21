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
 * @file atomic.h
 * @brief Atomic operations.
 */

#ifndef ATOMIC_H
#define ATOMIC_H

/* Standard includes. */
#include <stdint.h>

/* Compiler specific implementation. */
#if ( COMPILER_OPTION_GCC_ATOMIC_BUILTIN == 1 )

/* Standard boolean for CAS "strong". */
    #include <stdbool.h>

/* Default GCC compiler.
 * If GCC is used && the target architecture supports atomic instructions,
 * (e.g. ARM, Xtensa, ... )
 * there's no reason to not use GCC built-in atomics.
 * Thus, no user extension is provided in this branch.
 *
 * If you believe atomic built-in is not compiled correctly by GCC for your target,
 * please use the other branch and provide your own implementation for atomic.
 *
 * attribute flatten is not needed in this branch.
 */
    #define FORCE_INLINE    inline __attribute__( ( always_inline ) )

/* GCC asm volatile.
 * This can be helpful when user wants to observe how atomic inline function is
 * compiled. Simply add a tag (or no-op) before and after atomic inline function
 * call, and observe objdump disassembly. Though, it is not suggested to call this
 * macro in user application code.
 */
    #define COMPILER_ASM_VOLATILE( x )    __asm__ __volatile__ ( x )

#else  /* if ( COMPILER_OPTION_GCC_ATOMIC_BUILTIN == 1 ) */

/* Using none GCC compiler || user customization
 * User needs to figure out compiler specific syntax for always-inline and flatten.*/
    #include "atomic/atomic_user_override_template.h"

#endif /* COMPILER_OPTION_GCC_ATOMIC_BUILTIN */

/*----------------------------- Swap && CAS ------------------------------*/

/**
 * Atomic compare-and-swap
 *
 * @brief Performs an atomic compare-and-swap operation on the specified values.
 *
 * @param[in, out] pDestination  Pointer to memory location from where value is to be loaded and checked.
 * @param[in] ulExchange         If condition meets, write this value to memory.
 * @param[in] ulComparand        Swap condition, checks and waits for *pDestination to be equal to ulComparand.
 *
 * @return unsigned integer of value 1 or 0. 1 for swapped, 0 for not swapped.
 *
 * @note This function only swaps *pDestination with ulExchange, if previous *pDestination value equals ulComparand.
 */
static FORCE_INLINE uint32_t Atomic_CompareAndSwap_u32( uint32_t volatile * pDestination,
                                                        uint32_t ulExchange,
                                                        uint32_t ulComparand )
{
    uint32_t ulReturnValue = 0;

    #if ( COMPILER_OPTION_GCC_ATOMIC_BUILTIN == 1 )
        if( __atomic_compare_exchange( pDestination, &ulComparand, &ulExchange, false, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST ) )
        {
            ulReturnValue = 1;
        }
    #else
        ulReturnValue = Atomic_CompareAndSwap_u32_User_Override( pDestination, ulExchange, ulComparand );
    #endif /* COMPILER_OPTION_GCC_ATOMIC_BUILTIN */

    return ulReturnValue;
}

/**
 * Atomic swap (pointers)
 *
 * @brief Atomically sets the address pointed to by *ppDestination to the value of *pExchange.
 *
 * @param[in, out] ppDestination  Pointer to memory location from where a pointer value is to be loaded and writen back to.
 * @param[in] pExchange           Pointer value to be written to *ppDestination.
 *
 * @return The initial value of *ppDestination.
 */
static FORCE_INLINE void * Atomic_SwapPointers_p32( void * volatile * ppDestination,
                                                    void * pExchange )
{
    #if ( COMPILER_OPTION_GCC_ATOMIC_BUILTIN == 1 )
        void * pReturnValue;
        __atomic_exchange( ppDestination, &pExchange, &pReturnValue, __ATOMIC_SEQ_CST );

        return pReturnValue;
    #else
        return Atomic_SwapPointers_p32_User_Override( ppDestination, pExchange );
    #endif /* COMPILER_OPTION_GCC_ATOMIC_BUILTIN */
}

/**
 * Atomic compare-and-swap (pointers)
 *
 * @brief Performs an atomic compare-and-swap operation on the specified pointer values.
 *
 * @param[in, out] ppDestination Pointer to memory location from where a pointer value is to be loaded and checked.
 * @param[in] pExchange          If condition meets, write this value to memory.
 * @param[in] pComparand         Swap condition, checks and waits for *ppDestination to be equal to *pComparand.
 *
 * @return unsigned integer of value 1 or 0. 1 for swapped, 0 for not swapped.
 *
 * @note This function only swaps *ppDestination with pExchange, if previous *ppDestination value equals pComparand.
 */
static FORCE_INLINE uint32_t Atomic_CompareAndSwapPointers_p32( void * volatile * ppDestination,
                                                                void * pExchange,
                                                                void * pComparand )
{
    uint32_t ulReturnValue = 0;

    #if ( COMPILER_OPTION_GCC_ATOMIC_BUILTIN == 1 )
        if( __atomic_compare_exchange( ppDestination, &pComparand, &pExchange, false, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST ) )
        {
            ulReturnValue = 1;
        }
    #else
        ulReturnValue = Atomic_CompareAndSwapPointers_p32_User_Override( ppDestination, pExchange, pComparand );
    #endif /* COMPILER_OPTION_GCC_ATOMIC_BUILTIN */

    return ulReturnValue;
}


/*----------------------------- Arithmetic ------------------------------*/

/**
 * Atomic add
 *
 * @brief Adds count to the value of the specified 32-bit variable as an atomic operation.
 *
 * @param[in,out] pAddend  Pointer to memory location from where value is to be loaded and written back to.
 * @param[in] lCount       Value to be added to *pAddend.
 *
 * @return previous *pAddend value.
 */
static FORCE_INLINE uint32_t Atomic_Add_u32( uint32_t volatile * pAddend,
                                             uint32_t lCount )
{
    #if ( COMPILER_OPTION_GCC_ATOMIC_BUILTIN == 1 )
        return __atomic_fetch_add( pAddend, lCount, __ATOMIC_SEQ_CST );
    #else
        return Atomic_Add_u32_User_Override( pAddend, lCount );
    #endif /* COMPILER_OPTION_GCC_ATOMIC_BUILTIN */
}

/**
 * Atomic sub
 *
 * @brief Subtracts count from the value of the specified 32-bit variable as an atomic operation.
 *
 * @param[in,out] pAddend  Pointer to memory location from where value is to be loaded and written back to.
 * @param[in] lCount       Value to be subtract from *pAddend.
 *
 * @return previous *pAddend value.
 */
static FORCE_INLINE uint32_t Atomic_Subtract_u32( uint32_t volatile * pAddend,
                                                  uint32_t lCount )
{
    #if ( COMPILER_OPTION_GCC_ATOMIC_BUILTIN == 1 )
        return __atomic_fetch_sub( pAddend, lCount, __ATOMIC_SEQ_CST );
    #else
        return Atomic_Subtract_u32_User_Override( pAddend, lCount );
    #endif /* COMPILER_OPTION_GCC_ATOMIC_BUILTIN */
}

/**
 * Atomic increment
 *
 * @brief Increments the value of the specified 32-bit variable as an atomic operation.
 *
 * @param[in,out] pAddend  Pointer to memory location from where value is to be loaded and written back to.
 *
 * @return *pAddend value before increment.
 */
static FORCE_INLINE uint32_t Atomic_Increment_u32( uint32_t volatile * pAddend )
{
    #if ( COMPILER_OPTION_GCC_ATOMIC_BUILTIN == 1 )
        return __atomic_fetch_add( pAddend, 1, __ATOMIC_SEQ_CST );
    #else
        return Atomic_Increment_u32_User_Override( pAddend );
    #endif /* COMPILER_OPTION_GCC_ATOMIC_BUILTIN */
}

/**
 * Atomic decrement
 *
 * @brief Decrements the value of the specified 32-bit variable as an atomic operation.
 *
 * @param[in,out] pAddend  Pointer to memory location from where value is to be loaded and written back to.
 *
 * @return *pAddend value before decrement.
 */
static FORCE_INLINE uint32_t Atomic_Decrement_u32( uint32_t volatile * pAddend )
{
    #if ( COMPILER_OPTION_GCC_ATOMIC_BUILTIN == 1 )
        return __atomic_fetch_sub( pAddend, 1, __ATOMIC_SEQ_CST );
    #else
        return Atomic_Decrement_u32_User_Override( pAddend );
    #endif /* COMPILER_OPTION_GCC_ATOMIC_BUILTIN */
}

/*----------------------------- Bitwise Logical ------------------------------*/

/**
 * Atomic OR
 *
 * @brief Performs an atomic OR operation on the specified values.
 *
 * @param [in, out] pDestination Pointer to memory location from where value is to be loaded and written back to.
 * @param [in] ulValue           Value to be ORed with *pDestination.
 *
 * @return The original value of *pDestination.
 */
static FORCE_INLINE uint32_t Atomic_OR_u32( uint32_t volatile * pDestination,
                                            uint32_t ulValue )
{
    #if ( COMPILER_OPTION_GCC_ATOMIC_BUILTIN == 1 )
        return __atomic_fetch_or( pDestination, ulValue, __ATOMIC_SEQ_CST );
    #else
        return Atomic_OR_u32_User_Override( pDestination, ulValue );
    #endif /* COMPILER_OPTION_GCC_ATOMIC_BUILTIN */
}

/**
 * Atomic AND
 *
 * @brief Performs an atomic AND operation on the specified values.
 *
 * @param [in, out] pDestination Pointer to memory location from where value is to be loaded and written back to.
 * @param [in] ulValue           Value to be ANDed with *pDestination.
 *
 * @return The original value of *pDestination.
 */
static FORCE_INLINE uint32_t Atomic_AND_u32( uint32_t volatile * pDestination,
                                             uint32_t ulValue )
{
    #if ( COMPILER_OPTION_GCC_ATOMIC_BUILTIN == 1 )
        return __atomic_fetch_and( pDestination, ulValue, __ATOMIC_SEQ_CST );
    #else
        return Atomic_AND_u32_User_Override( pDestination, ulValue );
    #endif /* COMPILER_OPTION_GCC_ATOMIC_BUILTIN */
}

/**
 * Atomic NAND
 *
 * @brief Performs an atomic NAND operation on the specified values.
 *
 * @param [in, out] pDestination Pointer to memory location from where value is to be loaded and written back to.
 * @param [in] ulValue           Value to be NANDed with *pDestination.
 *
 * @return The original value of *pDestination.
 */
static FORCE_INLINE uint32_t Atomic_NAND_u32( uint32_t volatile * pDestination,
                                              uint32_t ulValue )
{
    #if ( COMPILER_OPTION_GCC_ATOMIC_BUILTIN == 1 )
        return __atomic_fetch_nand( pDestination, ulValue, __ATOMIC_SEQ_CST );
    #else
        return Atomic_NAND_u32_User_Override( pDestination, ulValue );
    #endif /* COMPILER_OPTION_GCC_ATOMIC_BUILTIN */
}

/**
 * Atomic XOR
 * @brief Performs an atomic XOR operation on the specified values.
 *
 * @param [in, out] pDestination Pointer to memory location from where value is to be loaded and written back to.
 * @param [in] ulValue           Value to be XORed with *pDestination.
 *
 * @return The original value of *pDestination.
 */
static FORCE_INLINE uint32_t Atomic_XOR_u32( uint32_t volatile * pDestination,
                                             uint32_t ulValue )
{
    #if ( COMPILER_OPTION_GCC_ATOMIC_BUILTIN == 1 )
        return __atomic_fetch_xor( pDestination, ulValue, __ATOMIC_SEQ_CST );
    #else
        return Atomic_XOR_u32_User_Override( pDestination, ulValue );
    #endif /* COMPILER_OPTION_GCC_ATOMIC_BUILTIN */
}

#endif /* ATOMIC_H */
