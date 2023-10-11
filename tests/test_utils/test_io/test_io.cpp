
#include <random>
#include <iostream>
#include <sentry/io.h>
#include <gtest/gtest.h>

template<typename T>
void iowrite(size_t addr, T val);
template<typename T>
void ioread(size_t addr, T* val);

void iowrite(size_t addr, uint8_t val) { iowrite8(addr, val); }
void iowrite(size_t addr, uint16_t val) { iowrite16(addr, val); }
void iowrite(size_t addr, uint32_t val) { iowrite32(addr, val); }
void ioread(size_t addr, uint8_t *val) { *val = ioread8(addr); }
void ioread(size_t addr, uint16_t *val) { *val = ioread16(addr); }
void ioread(size_t addr, uint32_t *val) { *val = ioread32(addr); }

TEST(Io, Write) {

    auto test_iowrite = [] <typename T>(size_t reg, T) -> void {
        std::random_device rd;
        std::mt19937 gen(rd());
        // max is kept under 268Mb (when T=uint32_t only) to avoid SIGSEGV
        T max = std::numeric_limits<T>::max() & 0xfffffff;

        std::uniform_int_distribution<> distrib(1, max);
        // choose uniformly selected 255 integer values in the previous range
        for (int n = 0; n != 255; ++n) {
            T Val = distrib(gen);
            iowrite(reg, Val);
            T res = 0;
            ioread(reg, &res);
            EXPECT_EQ(res, Val);
        }
    };

    uint32_t Reg;
    size_t reg_ref = (size_t)&Reg;

    //iowrite(reg_ref, (uint16_t)0);
    test_iowrite(reg_ref, uint8_t{});
    test_iowrite(reg_ref, uint16_t{});
    test_iowrite(reg_ref, uint32_t{});
};
