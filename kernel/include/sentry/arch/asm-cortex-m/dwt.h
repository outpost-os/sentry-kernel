// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef __DWT_H
#define __DWT_H

#include <inttypes.h>
#include <sentry/arch/asm-cortex-m/core.h>

/*@
  assigns CoreDebug->DEMCR, DWT->CTRL;
 */
__STATIC_FORCEINLINE void dwt_enable_cyccnt(void)
{
    CoreDebug->DEMCR |= CoreDebug_DEMCR_TRCENA_Msk;
    DWT->CTRL |= DWT_CTRL_CYCCNTENA_Msk;
}

/*@
  assigns DWT->CTRL;
 */
__STATIC_FORCEINLINE void dwt_disable_cyccnt(void)
{
    DWT->CTRL &= ~DWT_CTRL_CYCCNTENA_Msk;
}

/*@
  assigns DWT->CTRL;
 */
__STATIC_FORCEINLINE void dwt_reset_cyccnt(void)
{
    DWT->CYCCNT = 0;
}

/*@
  assigns \nothing;
 */
__STATIC_FORCEINLINE uint32_t dwt_cyccnt(void)
{
    return DWT->CYCCNT;
}

#endif /* __ARCH_PERFO_H */
