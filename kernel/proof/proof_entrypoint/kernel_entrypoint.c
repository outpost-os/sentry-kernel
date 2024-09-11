// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>
#include <sentry/managers/task.h>
/*
 * Frama-C entropy sources. This variables have their value changed each time
 * they are read
 */
extern volatile int Frama_C_entropy_source_int __attribute__((unused))
__attribute__((FRAMA_C_MODEL));
extern volatile uint8_t Frama_C_entropy_source_u8 __attribute__((unused))
__attribute__((FRAMA_C_MODEL));
extern volatile uint16_t Frama_C_entropy_source_u16 __attribute__((unused))
__attribute__((FRAMA_C_MODEL));
extern volatile uint16_t Frama_C_entropy_source_u32 __attribute__((unused))
__attribute__((FRAMA_C_MODEL));
extern volatile uint8_t Frama_C_entropy_source_bool __attribute__((unused))
__attribute__((FRAMA_C_MODEL));

//@ assigns Frama_C_entropy_source_int \from Frama_C_entropy_source_int;
void Frama_C_update_entropy_int(void)
{
    Frama_C_entropy_source_int = Frama_C_entropy_source_int;
}

//@ assigns Frama_C_entropy_source_u8 \from Frama_C_entropy_source_u8;
void Frama_C_update_entropy_u8(void)
{
    Frama_C_entropy_source_u8 = Frama_C_entropy_source_u8;
}

//@ assigns Frama_C_entropy_source_u16 \from Frama_C_entropy_source_u16;
void Frama_C_update_entropy_u16(void)
{
    Frama_C_entropy_source_u16 = Frama_C_entropy_source_u16;
}

//@ assigns Frama_C_entropy_source_u32 \from Frama_C_entropy_source_u32;
void Frama_C_update_entropy_u32(void)
{
    Frama_C_entropy_source_u32 = Frama_C_entropy_source_u32;
}
//@ assigns Frama_C_entropy_source_bool \from Frama_C_entropy_source_bool;
void Frama_C_update_entropy_bool(void)
{
    Frama_C_entropy_source_bool = Frama_C_entropy_source_bool;
}

/*@
  @ assigns Frama_C_entropy_source_int \from Frama_C_entropy_source_int;
  */
int Frama_C_interval_int(int min, int max)
{
    int r, aux;
    Frama_C_update_entropy_int();
    aux = Frama_C_entropy_source_int;
    if ((aux >= min) && (aux <= max))
        r = aux;
    else
        r = min;
    return r;
}

/*@
  @ assigns Frama_C_entropy_source_u8 \from Frama_C_entropy_source_u8;
  */
uint8_t Frama_C_interval_u8(uint8_t min, uint8_t max)
{
    uint8_t r, aux;
    Frama_C_update_entropy_u8();
    aux = Frama_C_entropy_source_u8;
    if ((aux >= min) && (aux <= max))
        r = aux;
    else
        r = min;
    return r;
}

/*@
  @ assigns Frama_C_entropy_source_u16 \from Frama_C_entropy_source_u16;
  */
uint16_t Frama_C_interval_u16(uint16_t min, uint16_t max)
{
    uint16_t r, aux;
    Frama_C_update_entropy_u16();
    aux = Frama_C_entropy_source_u16;
    if ((aux >= min) && (aux <= max))
        r = aux;
    else
        r = min;
    return r;
}

/*@
  @ assigns Frama_C_entropy_source_u32 \from Frama_C_entropy_source_u32;
  */
uint32_t Frama_C_interval_u32(uint32_t min, uint32_t max)
{
    uint32_t r, aux;
    Frama_C_update_entropy_u32();
    aux = Frama_C_entropy_source_u32;
    if ((aux >= min) && (aux <= max))
        r = aux;
    else
        r = min;
    return r;
}

/*@
  @ assigns Frama_C_entropy_source_bool \from Frama_C_entropy_source_bool;
  */
bool Frama_C_interval_bool(void)
{
    uint8_t raw_val;
    bool    val = true;
    Frama_C_update_entropy_bool();
    raw_val = Frama_C_entropy_source_bool;
    if (raw_val == 0) {
        val = false;
    }
    /*@ assert val \in {0, 1}; */
    return val;
}

extern task_meta_t __task_meta_table[CONFIG_MAX_TASKS];

static void Frama_C_task_init_meta(void)
{
    uint32_t *target = (uint32_t*)&__task_meta_table[0];
    for (uint32_t offset = 0; offset < (sizeof(task_meta_t)*CONFIG_MAX_TASKS) / sizeof(uint32_t); ++offset)
    {
        target[offset] = ghost_Frama_C_get_random_u32();
    }
}

void Reset_Handler(void);

void kernel_entrypoint(void)
{
    /** INFO: inject garbage in metadata. This structure is build system forged.
     * This allows to:
     * 1. avoid uninitialized error from frama-C
     * 2. generate potential invalid inputs values from corrupted build system
     */
    Frama_C_task_init_meta();
    /* calling kernel entrypoint */
    Reset_Handler();
    //_entrypoint();
}
