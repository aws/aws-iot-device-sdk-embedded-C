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
 * @file iot_atomic_generic.h
 * @brief Generic implementation of atomic operations.
 *
 * This implementation is less efficient than the specific atomic implementations,
 * but should work on all platforms.
 */

#ifndef IOT_ATOMIC_GENERIC_H_
#define IOT_ATOMIC_GENERIC_H_

/* Standard includes. */
#include <stdint.h>

/* Atomic include. */
#include "iot_atomic.h"

/* Platform threads include. */
#include "platform/iot_threads.h"

/* Ensure that this header is only included when generic atomics are enabled. */
#if IOT_ATOMIC_GENERIC != 1
    #error "Generic atomic implementation is not enabled."
#endif

/**
 * @functionspage{platform_atomic,platform atomics component,Atomics}
 * - @functionname{platform_atomic_function_compareandswap_u32}
 * - @functionname{platform_atomic_function_swap_pointer}
 * - @functionname{platform_atomic_function_compareandswap_pointer}
 * - @functionname{platform_atomic_function_add_u32}
 * - @functionname{platform_atomic_function_subtract_u32}
 * - @functionname{platform_atomic_function_increment_u32}
 * - @functionname{platform_atomic_function_decrement_u32}
 * - @functionname{platform_atomic_function_or_u32}
 * - @functionname{platform_atomic_function_xor_u32}
 * - @functionname{platform_atomic_function_and_u32}
 * - @functionname{platform_atomic_function_nand_u32}
 */

/**
 * @functionpage{Atomic_CompareAndSwap_u32,platform_atomic,compareandswap_u32}
 * @functionpage{Atomic_Swap_Pointer,platform_atomic,swap_pointer}
 * @functionpage{Atomic_CompareAndSwap_Pointer,platform_atomic,compareandswap_pointer}
 * @functionpage{Atomic_Add_u32,platform_atomic,add_u32}
 * @functionpage{Atomic_Subtract_u32,platform_atomic,subtract_u32}
 * @functionpage{Atomic_Increment_u32,platform_atomic,increment_u32}
 * @functionpage{Atomic_Decrement_u32,platform_atomic,decrement_u32}
 * @functionpage{Atomic_OR_u32,platform_atomic,or_u32}
 * @functionpage{Atomic_XOR_u32,platform_atomic,xor_u32}
 * @functionpage{Atomic_AND_u32,platform_atomic,and_u32}
 * @functionpage{Atomic_NAND_u32,platform_atomic,nand_u32}
 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 */
extern IotMutex_t IotAtomicMutex;
/** @endcond */

/*---------------- Swap and compare-and-swap ------------------*/

/**
 * @brief Performs an atomic compare-and-swap operation on the given values.
 *
 * @param[in,out] pDestination Pointer to memory location from where value is to
 * be loaded and checked.
 * @param[in] newValue This value will be written to memory if the comparand matches
 * the value at `pDestination`.
 * @param[in] comparand This value is compared to the value at `pDestination`.
 *
 * @return `1` if the `newValue` was written to `pDestination`; `0` otherwise.
 */
/* @[declare_platform_atomic_compareandswap_u32] */
static inline uint32_t Atomic_CompareAndSwap_u32( uint32_t volatile * pDestination,
                                                  uint32_t newValue,
                                                  uint32_t comparand )
/* @[declare_platform_atomic_compareandswap_u32] */
{
    uint32_t swapped = 0;

    IotMutex_Lock( &IotAtomicMutex );

    if( *pDestination == comparand )
    {
        *pDestination = newValue;
        swapped = 1;
    }

    IotMutex_Unlock( &IotAtomicMutex );

    return swapped;
}

/*-----------------------------------------------------------*/

/**
 * @brief Atomically writes a pointer value to memory.
 *
 * @param[in,out] pDestination Where `pNewValue` will be written.
 * @param[in] pNewValue The value to write to `pDestination`.
 *
 * @return The initial value at `pDestination`.
 */
/* @[declare_platform_atomic_swap_pointer] */
static inline void * Atomic_Swap_Pointer( void * volatile * pDestination,
                                          void * pNewValue )
/* @[declare_platform_atomic_swap_pointer] */
{
    void * pOldValue = NULL;

    IotMutex_Lock( &IotAtomicMutex );
    pOldValue = *pDestination;
    *pDestination = pNewValue;
    IotMutex_Unlock( &IotAtomicMutex );

    return pOldValue;
}

/*-----------------------------------------------------------*/

/**
 * @brief Performs an atomic compare-and-swap operation on the given pointers.
 *
 * @param[in,out] pDestination Pointer to the memory location to
 * be loaded and checked.
 * @param[in] pNewValue This value will be written to memory if the comparand matches
 * the value at `pDestination`.
 * @param[in] pComparand This value is compared to the value at `pDestination`.
 *
 * @return `1` if the `newValue` was written to `pDestination`; `0` otherwise.
 */
/* @[declare_platform_atomic_compareandswap_pointer] */
static inline uint32_t Atomic_CompareAndSwap_Pointer( void * volatile * pDestination,
                                                      void * pNewValue,
                                                      void * pComparand )
/* @[declare_platform_atomic_compareandswap_pointer] */
{
    uint32_t swapped = 0;

    IotMutex_Lock( &IotAtomicMutex );

    if( *pDestination == pComparand )
    {
        *pDestination = pNewValue;
        swapped = 1;
    }

    IotMutex_Unlock( &IotAtomicMutex );

    return swapped;
}

/*----------------------- Arithmetic --------------------------*/

/**
 * @brief Performs an atomic addition of the given values.
 *
 * @param[in,out] pAugend Pointer to the augend and where the sum is stored.
 * @param[in] addend Value to add to the augend.
 *
 * @return The initial value at `pAugend`.
 */
/* @[declare_platform_atomic_add_u32] */
static inline uint32_t Atomic_Add_u32( uint32_t volatile * pAugend,
                                       uint32_t addend )
/* @[declare_platform_atomic_add_u32] */
{
    uint32_t oldValue = 0;

    IotMutex_Lock( &IotAtomicMutex );
    oldValue = *pAugend;
    *pAugend = oldValue + addend;
    IotMutex_Unlock( &IotAtomicMutex );

    return oldValue;
}

/*-----------------------------------------------------------*/

/**
 * @brief Performs an atomic subtraction of the given values.
 *
 * @param[in,out] pMinuend Pointer to the minuend and where the difference is stored.
 * @param[in] subtrahend Value to subtract from the minuend.
 *
 * @return The initial value at `pMinuend`.
 */
/* @[declare_platform_atomic_subtract_u32] */
static inline uint32_t Atomic_Subtract_u32( uint32_t volatile * pMinuend,
                                            uint32_t subtrahend )
/* @[declare_platform_atomic_subtract_u32] */
{
    uint32_t oldValue = 0;

    IotMutex_Lock( &IotAtomicMutex );
    oldValue = *pMinuend;
    *pMinuend = oldValue + subtrahend;
    IotMutex_Unlock( &IotAtomicMutex );

    return oldValue;
}

/*-----------------------------------------------------------*/

/**
 * @brief Atomically adds 1 to the given value.
 *
 * @param[in,out] pAugend Pointer to the augend and where the sum is stored.
 *
 * @return The initial value at `pAugend`.
 */
/* @[declare_platform_atomic_increment_u32] */
static inline uint32_t Atomic_Increment_u32( uint32_t volatile * pAugend )
/* @[declare_platform_atomic_increment_u32] */
{
    return Atomic_Add_u32( pAugend, 1 );
}

/*-----------------------------------------------------------*/

/**
 * @brief Atomically subtracts 1 from the given value.
 *
 * @param[in,out] pMinuend Pointer to the minuend and where the difference is stored.
 *
 * @return The initial value at `pMinuend`.
 */
/* @[declare_platform_atomic_decrement_u32] */
static inline uint32_t Atomic_Decrement_u32( uint32_t volatile * pMinuend )
/* @[declare_platform_atomic_decrement_u32] */
{
    return Atomic_Subtract_u32( pMinuend, 1 );
}

/*--------------------- Bitwise logic -------------------------*/

/**
 * @brief Performs an atomic bitwise OR of the given values.
 *
 * @param[in,out] pOperand Pointer to operand and where the result is stored.
 * @param[in] mask Mask to OR with the operand.
 *
 * @return The initial value at `pOperand`.
 */
/* @[declare_platform_atomic_or_u32] */
static inline uint32_t Atomic_OR_u32( uint32_t volatile * pOperand,
                                      uint32_t mask )
/* @[declare_platform_atomic_or_u32] */
{
    uint32_t oldValue = 0;

    IotMutex_Lock( &IotAtomicMutex );
    oldValue = *pOperand;
    *pOperand = ( oldValue | mask );
    IotMutex_Unlock( &IotAtomicMutex );

    return oldValue;
}

/*-----------------------------------------------------------*/

/**
 * @brief Performs an atomic bitwise XOR of the given values.
 *
 * @param[in,out] pOperand Pointer to operand and where the result is stored.
 * @param[in] mask Mask to XOR with the operand.
 *
 * @return The initial value at `pOperand`.
 */
/* @[declare_platform_atomic_xor_u32] */
static inline uint32_t Atomic_XOR_u32( uint32_t volatile * pOperand,
                                       uint32_t mask )
/* @[declare_platform_atomic_xor_u32] */
{
    uint32_t oldValue = 0;

    IotMutex_Lock( &IotAtomicMutex );
    oldValue = *pOperand;
    *pOperand = ( oldValue ^ mask );
    IotMutex_Unlock( &IotAtomicMutex );

    return oldValue;
}

/*-----------------------------------------------------------*/

/**
 * @brief Performs an atomic bitwise AND of the given values.
 *
 * @param[in,out] pOperand Pointer to operand and where the result is stored.
 * @param[in] mask Mask to AND with the operand.
 *
 * @return The initial value at `pOperand`.
 */
/* @[declare_platform_atomic_and_u32] */
static inline uint32_t Atomic_AND_u32( uint32_t volatile * pOperand,
                                       uint32_t mask )
/* @[declare_platform_atomic_and_u32] */
{
    uint32_t oldValue = 0;

    IotMutex_Lock( &IotAtomicMutex );
    oldValue = *pOperand;
    *pOperand = ( oldValue & mask );
    IotMutex_Unlock( &IotAtomicMutex );

    return oldValue;
}

/*-----------------------------------------------------------*/

/**
 * @brief Performs an atomic bitwise NAND of the given values.
 *
 * @param[in,out] pOperand Pointer to operand and where the result is stored.
 * @param[in] mask Mask to NAND with the operand.
 *
 * @return The initial value at `pOperand`.
 */
/* @[declare_platform_atomic_nand_u32] */
static inline uint32_t Atomic_NAND_u32( uint32_t volatile * pOperand,
                                        uint32_t mask )
/* @[declare_platform_atomic_nand_u32] */
{
    uint32_t oldValue = 0;

    IotMutex_Lock( &IotAtomicMutex );
    oldValue = *pOperand;
    *pOperand = ~( oldValue & mask );
    IotMutex_Unlock( &IotAtomicMutex );

    return oldValue;
}

#endif /* ifndef IOT_ATOMIC_GENERIC_H_ */
