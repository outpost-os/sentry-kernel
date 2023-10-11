// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef USART_H
#define USART_H

#include <sentry/ktypes.h>

kstatus_t usart_probe(void);

kstatus_t usart_tx(uint8_t *data, size_t data_len);


#endif/*!USART_H*/
