// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sys/mman.h>
#include <string.h>
#include <errno.h>
#include <gtest/gtest.h>
#include <exception>
#include <random>
#include <iostream>
#include <sentry/arch/asm-cortex-m/layout.h>
#include <bsp/drivers/exti/exti.h>
#include <sentry/ktypes.h>
#include "stm32-exti-dt.h"


class ExtiDevice : public testing::Test {
public:
    void SetUp() override {
        /* map EXTI device and init to reset value at test setup */
        /* using map an anonymous memory as the device, aligned on page size */
        map = mmap((void*)EXTI_BASE_ADDR, 4096UL, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
        if (map != (void*)EXTI_BASE_ADDR) {
            if ((size_t)map > EXTI_BASE_ADDR) {
                std::cerr << "Unable to map device to correct address 0x" << std::hex << EXTI_BASE_ADDR << std::endl;
                std::abort();
            }
            /* the kernel may have align the mapping on 4k size */
            if ((size_t)map + 4096 < (EXTI_BASE_ADDR + 0x400)) {
                std::cerr << "Unable to map device to correct address 0x" << std::hex << EXTI_BASE_ADDR << std::endl;
                std::cerr << "Page alignment problem not resolvable" << std::endl;
                std::cerr << "address is 0x" << std::hex << map << std::endl;
                std::cerr << strerror(errno);
                std::abort();
                /* page-alignment do include the device*/
            }
            if (map == (void*)-1) {
                std::cerr << "mmap has failed !" << std::endl;
                std::cerr << strerror(errno);
                std::abort();
            }
        }
        /*
         * push reset values (0x0 for EXTI= in the device. Using standard memory mapping size of device,
         * portable to any STM32 for offset
         */
        for (uint8_t *addr = (uint8_t*)EXTI_BASE_ADDR; addr < (uint8_t*)map+0x400; ++addr) {
            *addr = 0x0;
        }
        _device_mapped = true;
    }
    void TearDown() override {
        if (device_mapped()) {
            munmap(map, 4096UL);
        }
    }

    bool device_mapped(void) {
        return _device_mapped;
    }
private:
    bool _device_mapped;
    void* map;
};

extern "C" {
    kstatus_t mgr_mm_map_kdev(uint32_t addr __attribute__((unused)),
                              size_t size __attribute__((unused)))
    {
        return K_STATUS_OKAY;
    }

    kstatus_t mgr_mm_unmap_kdev(void) {
        return K_STATUS_OKAY;
    }
}

TEST_F(ExtiDevice, TestProbe)
{
    ASSERT_EQ(exti_probe(), K_STATUS_OKAY);
}

TEST_F(ExtiDevice, TestUnmaskInterrupt)
{
    std::random_device rd;
    std::mt19937 gen(rd());
        // generate garbage between 1 and 65.535
    uint8_t max = std::numeric_limits<uint8_t>::max();

    std::uniform_int_distribution<> distrib(1, max);
    // choose uniformly selected 127 integer values in the previous range
    for (int n = 0; n != 127; ++n) {
        uint8_t Val = distrib(gen);
        kstatus_t res;
        res = exti_unmask_interrupt(Val);
        if (Val <= EXTI_NUM_INTERRUPTS) {
            EXPECT_EQ(res, K_STATUS_OKAY);
        } else {
            EXPECT_EQ(res, K_ERROR_INVPARAM);
        }
    };
    for (int n = 0; n != 127; ++n) {
        uint8_t Val = distrib(gen);
        kstatus_t res;
        res = exti_mask_interrupt(Val);
        if (Val <= EXTI_NUM_INTERRUPTS) {
            EXPECT_EQ(res, K_STATUS_OKAY);
        } else {
            EXPECT_EQ(res, K_ERROR_INVPARAM);
        }
    };
}
