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
 * @file iot_tests_atomic.c
 * @brief Simple API tests for atomic interfaces.
 *
 * Tests in this file do not check extensively for atomicity,
 * but only guarantee APIs at least do what they supposed to do.
 * 
 * Atomic APIs are wrapped with asm tag, so that objdump disassembly
 * can be examined. 
 */

/* Build using a config header, if provided. */
#ifdef IOT_CONFIG_FILE
    #include IOT_CONFIG_FILE
#endif

/* NULL */
#include <stdlib.h>

/* Platform layer includes. */
#include "platform/atomic.h"

/* Test framework includes. */
#include "unity.h"
#include "unity_fixture.h"

/* Magic numbers. */
#define MAGIC_NUMBER_32BIT_1    ( 0xA5A5A5A5 )
#define MAGIC_NUMBER_32BIT_2    ( 0xF0F0F0F0 )
#define MAGIC_NUMBER_32BIT_3    ( 0x0000000F )

#define MAGIC_NUMBER_8BIT_1     ( 0xA5 )
#define MAGIC_NUMBER_8BIT_2     ( 0xF0 )

/*-----------------------------------------------------------*/

/**
 * @brief Test group for atomic tests.
 */
TEST_GROUP( Common_Unit_Atomic );

/*-----------------------------------------------------------*/

/**
 * @brief Test setup for atomic tests.
 */
TEST_SETUP( Common_Unit_Atomic )
{
}

/*-----------------------------------------------------------*/

/**
 * @brief Test tear down for atomic tests.
 */
TEST_TEAR_DOWN( Common_Unit_Atomic )
{
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group runner for atomic tests.
 */
TEST_GROUP_RUNNER( Common_Unit_Atomic )
{
    RUN_TEST_CASE( Common_Unit_Atomic, AtomicCasHappyPath );
    RUN_TEST_CASE( Common_Unit_Atomic, AtomicArithmeticHappyPath );
    RUN_TEST_CASE( Common_Unit_Atomic, AtomicBitwiseHappyPath );
    RUN_TEST_CASE( Common_Unit_Atomic, AtomicCasFailToSwap );
}


TEST( Common_Unit_Atomic, AtomicCasHappyPath )
{
    uint32_t ulCasDestination_32;
    uint32_t ulCasComparator_32;
    uint32_t ulCasNewValue_32;
    bool bExecutinoStatus;

    uint32_t * pSwapDestination_32;
    uint32_t * pSwapNewValue_32;
    uint32_t * pReturnValue_32;

    uint8_t uCasDestination_8 = MAGIC_NUMBER_8BIT_1;
    uint8_t uCasComparator_8 = MAGIC_NUMBER_8BIT_1;

    uint8_t * pSwapDestination_8 = &uCasDestination_8;
    uint8_t * pSwapNewValue_8 = &uCasComparator_8;
    uint8_t * pReturnValue_8 = NULL;

    /* #1 -- CAS */
    ulCasDestination_32 = MAGIC_NUMBER_32BIT_1;
    ulCasComparator_32 = MAGIC_NUMBER_32BIT_1;
    ulCasNewValue_32 = MAGIC_NUMBER_32BIT_2;

    __asm__ __volatile__ ( "atomic_cas_1: " );
    bExecutinoStatus = Atomic_CompareAndSwap_u32( &ulCasDestination_32, ulCasNewValue_32, ulCasComparator_32 );
    __asm__ __volatile__ ( "atomic_cas_1_end: " );

    TEST_ASSERT_MESSAGE( ulCasDestination_32 == ulCasNewValue_32, "Atomic_CompareAndSwap_u32 -- did not swap." );
    TEST_ASSERT_MESSAGE( bExecutinoStatus, "Atomic_CompareAndSwap_u32 -- expected return value true." );

    /* #2 -- CAS, comparator from the same mem location. */
    ulCasDestination_32 = MAGIC_NUMBER_32BIT_1;

    __asm__ __volatile__ ( "atomic_cas_2: " );
    bExecutinoStatus = Atomic_CompareAndSwap_u32( &ulCasDestination_32, MAGIC_NUMBER_32BIT_2, ulCasDestination_32 );
    __asm__ __volatile__ ( "atomic_cas_2_end: " );

    TEST_ASSERT_MESSAGE( ulCasDestination_32 == MAGIC_NUMBER_32BIT_2, "Atomic_CompareAndSwap_u32 -- did not swap." );
    TEST_ASSERT_MESSAGE( bExecutinoStatus, "Atomic_CompareAndSwap_u32 -- expected return value true." );

    /* #3 -- swap */
    pSwapDestination_32 = &ulCasDestination_32;
    pSwapNewValue_32 = &ulCasNewValue_32;
    pReturnValue_32 = NULL;

    __asm__ __volatile__ ( "atomic_xchg_32bit: " );
    pReturnValue_32 = Atomic_SwapPointers_p32( ( void ** ) &pSwapDestination_32, pSwapNewValue_32 );
    __asm__ __volatile__ ( "atomic_xchg_32bit_end: " );

    TEST_ASSERT_MESSAGE( pSwapDestination_32 == &ulCasNewValue_32, "Atomic_SwapPointers_p32 -- did not swap." );
    TEST_ASSERT_MESSAGE( pReturnValue_32 == &ulCasDestination_32, "Atomic_SwapPointers_p32 -- expected to return previous value." );

    /* #4 -- swap, pointer to variable of uint8_t type. */
    pSwapDestination_8 = &uCasDestination_8;
    pSwapNewValue_8 = &uCasComparator_8;
    pReturnValue_8 = NULL;

    __asm__ __volatile__ ( "atomic_xchg_8bit: nop" );
    pReturnValue_8 = Atomic_SwapPointers_p32( ( void ** ) &pSwapDestination_8, pSwapNewValue_8 );
    __asm__ __volatile__ ( "atomic_xchg_8bit_end: nop" );

    TEST_ASSERT_MESSAGE( pSwapDestination_8 == &uCasComparator_8, "Atomic_SwapPointers_p32 -- did not swap." );
    TEST_ASSERT_MESSAGE( pReturnValue_8 == &uCasDestination_8, "Atomic_SwapPointers_p32 -- expected to return previous value." );

    /* #5 -- CAS pointers. */
    pSwapDestination_32 = &ulCasDestination_32;
    pSwapNewValue_32 = &ulCasNewValue_32;

    __asm__ __volatile__ ( "atomic_CAS_pointers: nop" );
    bExecutinoStatus = Atomic_CompareAndSwapPointers_p32( ( void ** ) &pSwapDestination_32, pSwapNewValue_32, &ulCasDestination_32 );
    __asm__ __volatile__ ( "atomic_CAS_pointers_end: nop" );

    TEST_ASSERT_MESSAGE( ( intptr_t ) pSwapDestination_32 == ( intptr_t ) pSwapNewValue_32, "Atomic_CompareAndSwapPointers_p32 -- did not swap." );
    TEST_ASSERT_MESSAGE( bExecutinoStatus, "Atomic_CompareAndSwapPointers_p32 -- expected return value true." );

    return;
}

TEST( Common_Unit_Atomic, AtomicArithmeticHappyPath )
{
    int32_t iAddend_32;
    int32_t iDelta_32;
    int32_t iReturnValue_32;

    int8_t iAddend_8;

    /* asm (built-in function) implementation --
     * for curiosity, see what instructions add-register and add-immediate are using. */

    /* #1 -- add, overflow */
    iAddend_32 = 1;
    iDelta_32 = INT32_MAX;
    iReturnValue_32 = 0;

    __asm__ __volatile__ ( "atomic_add_reg: " );
    iReturnValue_32 = Atomic_Add_i32( &iAddend_32, iDelta_32 );
    __asm__ __volatile__ ( "atomic_add_reg_end: " );

    TEST_ASSERT_MESSAGE( iAddend_32 == INT32_MIN, "Atomic_Add_i32 -- did not add correctly." );
    TEST_ASSERT_MESSAGE( iReturnValue_32 == 1, "Atomic_Add_i32 -- expected return value 1." );

    /* #2 -- add immediate */
    iAddend_32 = 1;
    iDelta_32 = INT32_MAX;
    iReturnValue_32 = 0;

    __asm__ __volatile__ ( "atomic_add_imme: " );
    iReturnValue_32 = Atomic_Add_i32( &iAddend_32, INT32_MAX );
    __asm__ __volatile__ ( "atomic_add_imme_end: " );

    TEST_ASSERT_MESSAGE( iAddend_32 == INT32_MIN, "Atomic_Add_i32 -- did not add immediate number correctly." );
    TEST_ASSERT_MESSAGE( iReturnValue_32 == 1, "Atomic_Add_i32 -- expected return value 1." );

    /* #3 -- add, 8-bit casting */
    iAddend_8 = 1;
    iAddend_32 = ( uint32_t ) iAddend_8;

    __asm__ __volatile__ ( "atomic_add_8bit: " );
    iReturnValue_32 = Atomic_Add_i32( &iAddend_32, INT8_MAX );
    __asm__ __volatile__ ( "atomic_add_8bit_end: " );

    TEST_ASSERT_MESSAGE( ( uint8_t ) iReturnValue_32 != INT8_MIN, "Atomic_Add_i32 -- expected result to not be INT8_MIN." );

    /* #4 -- sub, almost but not underflow */
    iAddend_32 = -1;

    __asm__ __volatile__ ( "atomic_sub_reg: " );
    iReturnValue_32 = Atomic_Subtract_i32( &iAddend_32, INT32_MAX );
    __asm__ __volatile__ ( "atomic_sub_reg_end: " );

    TEST_ASSERT_MESSAGE( iAddend_32 == INT32_MIN, "Atomic_Subtract_i32 -- did not subtract correctly." );
    TEST_ASSERT_MESSAGE( iReturnValue_32 == -1, "Atomic_Subtract_i32 -- expected return value -1." );

    /* #5 -- inc, sanity check */
    iAddend_32 = INT32_MAX;

    __asm__ __volatile__ ( "atomic_inc: " );
    iReturnValue_32 = Atomic_Increment_i32( &iAddend_32 );
    __asm__ __volatile__ ( "atomic_inc_end: " );

    TEST_ASSERT_MESSAGE( iAddend_32 == INT32_MIN, "Atomic_Increment_i32 -- did not increment correctly." );
    TEST_ASSERT_MESSAGE( iReturnValue_32 == INT32_MAX, "Atomic_Increment_i32 -- expected return value INT32_MAX." );

    /* #6 -- dec, sanity check */
    iAddend_32 = INT32_MIN;

    __asm__ __volatile__ ( "atomic_dec: " );
    iReturnValue_32 = Atomic_Decrement_i32( &iAddend_32 );
    __asm__ __volatile__ ( "atomic_dec_end: " );

    TEST_ASSERT_MESSAGE( iAddend_32 == INT32_MAX, "Atomic_Decrement_i32 -- did not decrement correctly." );
    TEST_ASSERT_MESSAGE( iReturnValue_32 == INT32_MIN, "Atomic_Decrement_i32 -- expected return value INT32_MIN." );
}

TEST( Common_Unit_Atomic, AtomicBitwiseHappyPath )
{
    uint32_t ulOp1;
    uint32_t ulOp2;
    uint32_t ulReturnValue;

    /* #1 -- and */
    ulOp1 = MAGIC_NUMBER_32BIT_1;
    ulOp2 = MAGIC_NUMBER_32BIT_2;

    __asm__ __volatile__ ( "atomic_and: " );
    ulReturnValue = Atomic_AND_u32( &ulOp1, ulOp2 );
    __asm__ __volatile__ ( "atomic_and_end: " );

    TEST_ASSERT_MESSAGE( ulOp1 == 0xA0A0A0A0, "Atomic_AND_u32 -- did not ANDed correctly." );
    TEST_ASSERT_MESSAGE( ulReturnValue == MAGIC_NUMBER_32BIT_1, "Atomic_AND_u32 -- expected return value 0xA5A5A5A5." );

    /* #2 -- or */
    ulOp1 = MAGIC_NUMBER_32BIT_2;
    ulOp2 = MAGIC_NUMBER_32BIT_3;

    __asm__ __volatile__ ( "atomic_or: " );
    ulReturnValue = Atomic_OR_u32( &ulOp1, ulOp2 );
    __asm__ __volatile__ ( "atomic_or_end: " );

    TEST_ASSERT_MESSAGE( ulOp1 == 0xF0F0F0FF, "Atomic_OR_u32 -- did not ORed correctly." );
    TEST_ASSERT_MESSAGE( ulReturnValue == MAGIC_NUMBER_32BIT_2, "Atomic_AND_u32 -- expected return value 0xF0F0F0F0." );

    /* #3 -- nand */
    ulOp1 = MAGIC_NUMBER_32BIT_1;
    ulOp2 = MAGIC_NUMBER_32BIT_2;

    __asm__ __volatile__ ( "atomic_nand: " );
    ulReturnValue = Atomic_NAND_u32( &ulOp1, ulOp2 );
    __asm__ __volatile__ ( "atomic_nand_end: " );

    TEST_ASSERT_MESSAGE( ulOp1 == 0x5F5F5F5F, "Atomic_NAND_u32 -- did not NANDed correctly." );
    TEST_ASSERT_MESSAGE( ulReturnValue == MAGIC_NUMBER_32BIT_1, "Atomic_NAND_u32 -- expected return value 0xA5A5A5A5." );

    /* #4 -- xor */
    ulOp1 = MAGIC_NUMBER_32BIT_1;
    ulOp2 = MAGIC_NUMBER_32BIT_2;

    __asm__ __volatile__ ( "atomic_xor: " );
    ulReturnValue = Atomic_XOR_u32( &ulOp1, ulOp2 );
    __asm__ __volatile__ ( "atomic_XOR_end: " );

    TEST_ASSERT_MESSAGE( ulOp1 == 0x55555555, "Atomic_XOR_u32 -- did not XORed correctly." );
    TEST_ASSERT_MESSAGE( ulReturnValue == MAGIC_NUMBER_32BIT_1, "Atomic_XOR_u32 -- expected return value 0xA5A5A5A5." );
}

TEST( Common_Unit_Atomic, AtomicCasFailToSwap )
{
    uint32_t ulCasDestination_32;
    uint32_t ulCasComparator_32;
    uint32_t ulCasNewValue_32;
    bool bExecutinoStatus;

    uint32_t * pCasDestination_32;
    uint32_t * pCasComparator_32;
    uint32_t * pCasNewValue_32;

    /* #1 -- CAS, not equal, don't swap. */
    ulCasDestination_32 = MAGIC_NUMBER_32BIT_1;
    ulCasComparator_32 = MAGIC_NUMBER_32BIT_2;
    ulCasNewValue_32 = MAGIC_NUMBER_32BIT_3;

    __asm__ __volatile__ ( "atomic_cas_neq: " );
    bExecutinoStatus = Atomic_CompareAndSwap_u32( &ulCasDestination_32, ulCasNewValue_32, ulCasComparator_32 );
    __asm__ __volatile__ ( "atomic_cas_neq_end: " );

    TEST_ASSERT_MESSAGE( ulCasDestination_32 == MAGIC_NUMBER_32BIT_1, "Atomic_CompareAndSwap_u32 -- should not swap." );
    TEST_ASSERT_MESSAGE( !bExecutinoStatus, "Atomic_CompareAndSwap_u32 -- expected return value false." );

    /* #2 -- CAS, pointers not equal, don't swap. */
    pCasDestination_32 = &ulCasDestination_32;
    pCasComparator_32 = &ulCasComparator_32;
    pCasNewValue_32 = &ulCasNewValue_32;

    __asm__ __volatile__ ( "atomic_cas_pointers_neq: " );
    bExecutinoStatus = Atomic_CompareAndSwapPointers_p32( ( void ** ) &pCasDestination_32, pCasNewValue_32, pCasComparator_32 );
    __asm__ __volatile__ ( "atomic_cas_pointers_neq_end: " );

    TEST_ASSERT_MESSAGE( ( intptr_t ) pCasDestination_32 == ( intptr_t ) &ulCasDestination_32, "Atomic_CompareAndSwapPointers_p32 -- should not swap." );
    TEST_ASSERT_MESSAGE( !bExecutinoStatus, "Atomic_CompareAndSwapPointers_p32 -- expected return value false." );
}
