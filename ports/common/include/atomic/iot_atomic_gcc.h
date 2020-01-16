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

#ifndef IOT_ATOMIC_GCC_H_
#define IOT_ATOMIC_GCC_H_

/* Standard includes. */
#include <stdbool.h>
#include <stdint.h>

/**
 * @brief GCC function attribute to always inline a function.
 */
#define FORCE_INLINE    inline __attribute__( ( always_inline ) )

/*---------------- Swap and compare-and-swap ------------------*/

/**
 * @brief Implementation of atomic compare-and-swap for gcc.
 */
static FORCE_INLINE uint32_t Atomic_CompareAndSwap_u32( uint32_t volatile * pDestination,
                                                        uint32_t newValue,
                                                        uint32_t comparand )
{
    uint32_t swapped = 0;

    /* This header file is used with only the gcc compiler which 
     * requires an int parameter for this routine. */ 
    /* coverity[misra_c_2012_directive_4_6_violation] */
    if( ( ( bool ) ( __atomic_compare_exchange( pDestination,
                                                &comparand,
                                                &newValue,
                                                false,
                                                __ATOMIC_SEQ_CST,
                                                __ATOMIC_SEQ_CST ) ) )  == ( ( bool )( true ) ) )
    {
        swapped = 1;
    }

    return swapped;
}

/*-----------------------------------------------------------*/

/**
 * @brief Implementation of atomic pointer swap for gcc.
 */
static FORCE_INLINE void * Atomic_Swap_Pointer( void * volatile * pDestination,
                                                void * pNewValue )
{
    void * pOldValue = NULL;

    /* This header file is used with only the gcc compiler which 
     * requires an int parameter for this routine. */
    /* coverity[misra_c_2012_directive_4_6_violation] */
    __atomic_exchange( pDestination, &pNewValue, &pOldValue, __ATOMIC_SEQ_CST );

    return pOldValue;
}

/*-----------------------------------------------------------*/

/**
 * @brief Implementation of atomic pointer compare-and-swap for gcc.
 */
static FORCE_INLINE uint32_t Atomic_CompareAndSwap_Pointer( void * volatile * pDestination,
                                                            void * pNewValue,
                                                            void * pComparand )
{
    uint32_t swapped = 0;

    if( ( ( bool ) ( __atomic_compare_exchange( pDestination,
                                                &pComparand,
                                                &pNewValue,
                                                false,
                                                __ATOMIC_SEQ_CST,
                                                __ATOMIC_SEQ_CST ) ) ) == ( ( bool )( true ) ) )
    {
        swapped = 1;
    }

    return swapped;
}

/*----------------------- Arithmetic --------------------------*/

/**
 * @brief Implementation of atomic addition for gcc.
 */
static FORCE_INLINE uint32_t Atomic_Add_u32( uint32_t volatile * pAugend,
                                             uint32_t addend )
{
    /* This header file is used with only the gcc compiler which 
     * requires an int parameter for this routine. */
    /* coverity[misra_c_2012_directive_4_6_violation] */
    return __atomic_fetch_add( pAugend, addend, __ATOMIC_SEQ_CST );
}

/*-----------------------------------------------------------*/

/**
 * @brief Implementation of atomic subtraction for gcc.
 */
static FORCE_INLINE uint32_t Atomic_Subtract_u32( uint32_t volatile * pMinuend,
                                                  uint32_t subtrahend )
{
    /* This header file is used with only the gcc compiler which 
     * requires an int parameter for this routine. */
    /* coverity[misra_c_2012_directive_4_6_violation] */
    return __atomic_fetch_sub( pMinuend, subtrahend, __ATOMIC_SEQ_CST );
}

/*-----------------------------------------------------------*/

/**
 * @brief Implementation of atomic increment for gcc.
 */
static FORCE_INLINE uint32_t Atomic_Increment_u32( uint32_t volatile * pAugend )
{
    return __atomic_fetch_add( pAugend, 1, __ATOMIC_SEQ_CST );
}

/*-----------------------------------------------------------*/

/**
 * @brief Implementation of atomic decrement for gcc.
 */
static FORCE_INLINE uint32_t Atomic_Decrement_u32( uint32_t volatile * pMinuend )
{
    return __atomic_fetch_sub( pMinuend, 1, __ATOMIC_SEQ_CST );
}

/*--------------------- Bitwise logic -------------------------*/

/**
 * @brief Implementation of atomic OR for gcc.
 */
static FORCE_INLINE uint32_t Atomic_OR_u32( uint32_t volatile * pOperand,
                                            uint32_t mask )
{
    /* This header file is used with only the gcc compiler which 
     * requires an int parameter for this routine. */
    /* coverity[misra_c_2012_directive_4_6_violation] */
    return __atomic_fetch_or( pOperand, mask, __ATOMIC_SEQ_CST );
}

/*-----------------------------------------------------------*/

/**
 * @brief Implementation of atomic XOR for gcc.
 */
static FORCE_INLINE uint32_t Atomic_XOR_u32( uint32_t volatile * pOperand,
                                             uint32_t mask )
{
    /* This header file is used with only the gcc compiler which 
     * requires an int parameter for this routine. */
    /* coverity[misra_c_2012_directive_4_6_violation] */
    return __atomic_fetch_xor( pOperand, mask, __ATOMIC_SEQ_CST );
}

/*-----------------------------------------------------------*/

/**
 * @brief Implementation of atomic AND for gcc.
 */
static FORCE_INLINE uint32_t Atomic_AND_u32( uint32_t volatile * pOperand,
                                             uint32_t mask )
{
    /* This header file is used with only the gcc compiler which 
     * requires an int parameter for this routine. */
    /* coverity[misra_c_2012_directive_4_6_violation] */
    return __atomic_fetch_and( pOperand, mask, __ATOMIC_SEQ_CST );
}

/*-----------------------------------------------------------*/

/**
 * @brief Implementation of atomic NAND for gcc.
 */
static FORCE_INLINE uint32_t Atomic_NAND_u32( uint32_t volatile * pOperand,
                                              uint32_t mask )
{
    /* This header file is used with only the gcc compiler which 
     * requires an int parameter for this routine. */
    /* coverity[misra_c_2012_directive_4_6_violation] */
    return __atomic_fetch_nand( pOperand, mask, __ATOMIC_SEQ_CST );
}

#endif /* IOT_ATOMIC_GCC_H_ */
