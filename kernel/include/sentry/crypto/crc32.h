// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef CRC32_H
#define CRC32_H

/*@
  @ requires \valid(buf + (0 .. (len-1)));
  @ assigns buf[0 .. (len -1)];
  @*/
uint32_t crc32(unsigned char const * const buf, uint32_t len, uint32_t init);

#endif/*!CRC32_H*/
