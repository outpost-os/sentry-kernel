#ifndef MANAGER_INTERRUPT_H
#define MANAGER_INTERRUPT_H

/**
 * IRQ handle structure. Used by the userspace application to unically identify a given
 * interrupt.
 * The fields allows to detect kernel-controlled (yet IRQ push to user) devices such as EXTI or DMA
 */
typedef struct kirqh {
    uint32_t IRQn : 10;           /**< IRQ number, as attached to NVIC (ctrl == 0) */
    uint32_t controller : 2;      /**< controller identifier, from 0 to 3 */
    uint32_t shared : 1;          /**< (bool) IRQ is shared between devices */
    uint32_t kirq : 1;            /**< (bool) IRQ-associated device is under the kernel resposability (DMA...) */
    uint16_t entropy : 15;        /**< random value, set at boot */
    uint32_t family : 3;          /**< handle family */
} kirqh_t;

static_assert(sizeof(kirqh_t) == sizeof(uint32_t), "device opaque sizing failed!");

#endif /*!MANAGER_INTERRUPT_H*/
