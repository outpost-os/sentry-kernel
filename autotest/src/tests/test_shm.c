#include <inttypes.h>
#include <testlib/log.h>
#include <testlib/assert.h>
#include <uapi/uapi.h>
#include "test_shm.h"

/**
 * Note: in autotest-based DTS, the following SHM are defined
 * (see local dts example files)
 */
#define SHM_MAP_DMAPOOL 0xf00UL
#define SHM_NOMAP_DMAPOOL 0xf01UL
#define SHM_MAP_NODMAPOOL 0xf02UL

/* TODO: use generated instead */
#define SHM_MAP_DMAPOOL_BASEADDR 0x2000a000UL
#define SHM_MAP_DMAPOOL_SIZE 0x256UL

static taskh_t myself;

void test_shm_handle(void) {
    Status res;
    shmh_t shm;
    TEST_START();
    res = sys_get_shm_handle(SHM_MAP_DMAPOOL);
    ASSERT_EQ(res, STATUS_OK);
    res = sys_get_shm_handle(SHM_NOMAP_DMAPOOL);
    ASSERT_EQ(res, STATUS_OK);
    res = sys_get_shm_handle(SHM_MAP_NODMAPOOL);
    ASSERT_EQ(res, STATUS_OK);
    res = sys_get_shm_handle(0x42);
    ASSERT_EQ(res, STATUS_INVALID);
    TEST_END();
}

void test_shm_unmap_notmapped(void) {
    Status res;
    shmh_t shm;
    TEST_START();
    res = sys_get_shm_handle(SHM_MAP_DMAPOOL);
    copy_to_user((uint8_t*)&shm, sizeof(shmh_t));
    ASSERT_EQ(res, STATUS_OK);
    res = sys_unmap_shm(shm);
    ASSERT_EQ(res, STATUS_INVALID);
    TEST_END();
}

void test_shm_invalidmap(void) {
    Status res;
    shmh_t shm;
    TEST_START();
    res = sys_get_shm_handle(SHM_MAP_DMAPOOL);
    copy_to_user((uint8_t*)&shm, sizeof(shmh_t));
    ASSERT_EQ(res, STATUS_OK);
    shm += 42;
    shm = sys_map_shm(shm);
    ASSERT_EQ(res, STATUS_INVALID);
    TEST_END();
}

void test_shm_mapunmap(void) {
    Status res;
    shmh_t shm;
    TEST_START();
    /* get own handle first */
    res = sys_get_process_handle(0xbabeUL);
    copy_to_user((uint8_t*)&myself, sizeof(taskh_t));
    /* get shm handle then */
    res = sys_get_shm_handle(SHM_MAP_DMAPOOL);
    copy_to_user((uint8_t*)&shm, sizeof(shmh_t));
    LOG("handle is %lx", shm);
    ASSERT_EQ(res, STATUS_OK);
    /* give full write to myself */
    res = sys_shm_set_credential(shm, myself,
      (SHMPermission)(SHM_PERMISSION_READ | SHM_PERMISSION_WRITE | SHM_PERMISSION_TRANSFER)
    );
    ASSERT_EQ(res, STATUS_OK);
    /* map SHM */
    res = sys_map_shm(shm);
    ASSERT_EQ(res, STATUS_OK);
    if (res != STATUS_OK) {
        goto end;
    }

    uint32_t* shmptr = (uint32_t*)SHM_MAP_DMAPOOL_BASEADDR;
    LOG("shm mapped, checking read/write");
    for (uint8_t offset = 0; offset < 12*sizeof(uint32_t); offset += 4) {
        *shmptr = offset;
        shmptr++;
    }
    LOG("unmapping");
    res = sys_unmap_shm(shm);
    ASSERT_EQ(res, STATUS_OK);
end:
    TEST_END();
}

void test_shm(void) {
    TEST_SUITE_START("sys_map_shm");
    test_shm_handle();
    test_shm_invalidmap();
    test_shm_unmap_notmapped();
    test_shm_mapunmap();
    TEST_SUITE_END("sys_map_shm");
}
