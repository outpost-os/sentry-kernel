#include <stdio.h>
#include <iostream>
#include <sentry/ktypes.h>
#include <gtest/gtest.h>
#include <gmock/gmock.h>
#include <sentry/managers/debug.h>

struct PrintkMock {
    MOCK_METHOD(void, on_tx, (std::string));
};

static std::unique_ptr<PrintkMock> printkMock;

class PrintkTest : public testing::Test {
    void SetUp() override {
        printkMock = std::make_unique<PrintkMock>();
    }
    void TearDown() override {
        printkMock.reset();
    }
};

extern "C" {
    kstatus_t usart_tx(char *buf, uint16_t len) {
        std::string s;
        //std::clog << "string len: " << len << std::endl;
        //std::clog << "buf is: " << buf << std::endl;
        s.assign(buf, len);
        printkMock->on_tx(s);
        //std::clog << s << std::endl;
        return K_STATUS_OKAY;
    }
}


TEST_F(PrintkTest, TestBasicPointer) {
    uint32_t mytarget;
    void *toto = (void*)&mytarget;
    std::ostringstream patternstream;
    patternstream << toto;
    std::string pattern;
    pattern.assign(patternstream.str());
    EXPECT_CALL(*printkMock, on_tx(pattern));
    printk("%p", toto);
}

TEST_F(PrintkTest, TestPercent) {
    std::string pattern("%");
    EXPECT_CALL(*printkMock, on_tx(pattern));
    printk("%%");
}

TEST_F(PrintkTest, TestNullString) {
    std::string pattern("(null)");
    EXPECT_CALL(*printkMock, on_tx(pattern));
    printk("%s", NULL);
}

TEST_F(PrintkTest, TestBasicString) {
    static const char* pat = "my taylor is rich";
    std::string pattern(pat);
    EXPECT_CALL(*printkMock, on_tx(pattern));
    printk("%s", pat);
}

TEST_F(PrintkTest, TestRecursivePatternString) {
    static const char* pat = "my %d is a %s with %%";
    std::string pattern(pat);
    EXPECT_CALL(*printkMock, on_tx(pattern));
    printk("%s", pat);
}
