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
 * @file iot_atomic_gcc.h
 * @brief Atomic operations implemented on GCC extensions.
 *
 * Compatible with GCC and clang.
 */

#ifndef IOT_ATOMIC_GCC_H
#define IOT_ATOMIC_GCC_H

/* Standard includes. */
#include <stdbool.h>
#include <stdint.h>

/**
 * @brief GCC function attribute to always inline a function.
 */
#define FORCE_INLINE    inline __attribute__( ( always_inline ) )

/*----------------------- Swap and Compare-and-Swap -------------------------*/

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

    if( __atomic_compare_exchange( pDestination, &ulComparand, &ulExchange, false, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST ) )
    {
        ulReturnValue = 1;
    }

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
    void * pReturnValue;

    __atomic_exchange( ppDestination, &pExchange, &pReturnValue, __ATOMIC_SEQ_CST );

    return pReturnValue;
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

    if( __atomic_compare_exchange( ppDestination, &pComparand, &pExchange, false, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST ) )
    {
        ulReturnValue = 1;
    }

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
    return __atomic_fetch_add( pAddend, lCount, __ATOMIC_SEQ_CST );
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
    return __atomic_fetch_sub( pAddend, lCount, __ATOMIC_SEQ_CST );
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
    return __atomic_fetch_add( pAddend, 1, __ATOMIC_SEQ_CST );
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
    return __atomic_fetch_sub( pAddend, 1, __ATOMIC_SEQ_CST );
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
    return __atomic_fetch_or( pDestination, ulValue, __ATOMIC_SEQ_CST );
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
    return __atomic_fetch_and( pDestination, ulValue, __ATOMIC_SEQ_CST );
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
    return __atomic_fetch_nand( pDestination, ulValue, __ATOMIC_SEQ_CST );
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
    return __atomic_fetch_xor( pDestination, ulValue, __ATOMIC_SEQ_CST );
}

#endif /* IOT_ATOMIC_GCC_H */
