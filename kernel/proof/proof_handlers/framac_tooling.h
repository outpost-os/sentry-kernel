#ifndef FRAMAC_TOOLING
#define FRAMAC_TOOLING

#include <sentry/arch/asm-cortex-m/thread.h>
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

/* forge fully randomized frame content */
static volatile stack_frame_t frame;

#endif/*!FRAMAC_TOOLING*/
