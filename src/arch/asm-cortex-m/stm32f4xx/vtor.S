.syntax unified
.cpu cortex-m4
.thumb


/******************************************************************************
 *
 * The minimal vector table for a Cortex M4. Note that the proper constructs
 * must be placed on this to ensure that it ends up at physical address
 * 0x0000.0000.
 *
 ******************************************************************************/
.section  .isr_vector,"a",%progbits
  .type  VTOR_table, %object
  .size  VTOR_table, .-VTOR_table

VTOR_table:
  .word  _estack
  .word  Reset_Handler
  .word  Default_Handler
  .word  Default_Handler
  .word  Default_Handler
  .word  Default_Handler
  .word  Default_Handler
  .word  0
  .word  0
  .word  0
  .word  0
  .word  Default_Handler
  .word  Default_Handler
  .word  0
  .word  Default_Handler
  .word  Default_Handler

  /*
   * External Interrupts
   */
  .word     Default_Handler     /* Window WatchDog */
  .word     Default_Handler     /* PVD through EXTI Line detection */
  .word     Default_Handler     /* Tamper and TimeStamps through the EXTI line */
  .word     Default_Handler     /* RTC Wakeup through the EXTI line */
  .word     Default_Handler     /* FLASH */
  .word     Default_Handler     /* RCC */
  .word     Default_Handler     /* EXTI Line0 */
  .word     Default_Handler     /* EXTI Line1 */
  .word     Default_Handler     /* EXTI Line2 */
  .word     Default_Handler     /* EXTI Line3 */
  .word     Default_Handler     /* EXTI Line4 */
  .word     Default_Handler     /* DMA1 Stream 0 */
  .word     Default_Handler     /* DMA1 Stream 1 */
  .word     Default_Handler     /* DMA1 Stream 2 */
  .word     Default_Handler     /* DMA1 Stream 3 */
  .word     Default_Handler     /* DMA1 Stream 4 */
  .word     Default_Handler     /* DMA1 Stream 5 */
  .word     Default_Handler     /* DMA1 Stream 6 */
  .word     Default_Handler     /* ADC1, ADC2 and ADC3s */
  .word     Default_Handler     /* CAN1 TX */
  .word     Default_Handler     /* CAN1 RX0 */
  .word     Default_Handler     /* CAN1 RX1 */
  .word     Default_Handler     /* CAN1 SCE */
  .word     Default_Handler     /* External Line[9:5]s */
  .word     Default_Handler     /* TIM1 Break and TIM9 */
  .word     Default_Handler     /* TIM1 Update and TIM10 */
  .word     Default_Handler     /* TIM1 Trigger and Commutation and TIM11 */
  .word     Default_Handler     /* TIM1 Capture Compare */
  .word     Default_Handler     /* TIM2 */
  .word     Default_Handler     /* TIM3 */
  .word     Default_Handler     /* TIM4 */
  .word     Default_Handler     /* I2C1 Event */
  .word     Default_Handler     /* I2C1 Error */
  .word     Default_Handler     /* I2C2 Event */
  .word     Default_Handler     /* I2C2 Error */
  .word     Default_Handler     /* SPI1 */
  .word     Default_Handler     /* SPI2 */
  .word     Default_Handler     /* USART1 */
  .word     Default_Handler     /* USART2 */
  .word     Default_Handler     /* USART3 */
  .word     Default_Handler     /* External Line[15:10]s */
  .word     Default_Handler     /* RTC Alarm (A and B) through EXTI Line */
  .word     Default_Handler     /* USB OTG FS Wakeup through EXTI line */
  .word     Default_Handler     /* TIM8 Break and TIM12 */
  .word     Default_Handler     /* TIM8 Update and TIM13 */
  .word     Default_Handler     /* TIM8 Trigger and Commutation and TIM14 */
  .word     Default_Handler     /* TIM8 Capture Compare */
  .word     Default_Handler     /* DMA1 Stream7 */
  .word     Default_Handler     /* FSMC */
  .word     Default_Handler     /* SDIO */
  .word     Default_Handler     /* TIM5 */
  .word     Default_Handler     /* SPI3 */
  .word     Default_Handler     /* UART4 */
  .word     Default_Handler     /* UART5 */
  .word     Default_Handler     /* TIM6 and DAC1&2 underrun errors */
  .word     Default_Handler     /* TIM7 */
  .word     Default_Handler     /* DMA2 Stream 0 */
  .word     Default_Handler     /* DMA2 Stream 1 */
  .word     Default_Handler     /* DMA2 Stream 2 */
  .word     Default_Handler     /* DMA2 Stream 3 */
  .word     Default_Handler     /* DMA2 Stream 4 */
  .word     Default_Handler     /* Ethernet */
  .word     Default_Handler     /* Ethernet Wakeup through EXTI line */
  .word     Default_Handler     /* CAN2 TX */
  .word     Default_Handler     /* CAN2 RX0 */
  .word     Default_Handler     /* CAN2 RX1 */
  .word     Default_Handler     /* CAN2 SCE */
  .word     Default_Handler     /* USB OTG FS */
  .word     Default_Handler     /* DMA2 Stream 5 */
  .word     Default_Handler     /* DMA2 Stream 6 */
  .word     Default_Handler     /* DMA2 Stream 7 */
  .word     Default_Handler     /* USART6 */
  .word     Default_Handler     /* I2C3 event */
  .word     Default_Handler     /* I2C3 error */
  .word     Default_Handler     /* USB OTG HS End Point 1 Out */
  .word     Default_Handler     /* USB OTG HS End Point 1 In */
  .word     Default_Handler     /* USB OTG HS Wakeup through EXTI */
  .word     Default_Handler     /* USB OTG HS */
  .word     Default_Handler     /* DCMI */
  .word     Default_Handler     /* CRYP crypto */
  .word     Default_Handler     /* Hash and Rng */
  .word     Default_Handler     /* FPU */
