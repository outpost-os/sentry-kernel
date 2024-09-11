// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef ARM_SEMIHOSTING_H
#define ARM_SEMIHOSTING_H

#define SYS_FILE_MODE_READ              0
#define SYS_FILE_MODE_READBINARY        1
#define SYS_FILE_MODE_READWRITE         2
#define SYS_FILE_MODE_READWRITEBINARY   3
#define SYS_FILE_MODE_WRITE             4
#define SYS_FILE_MODE_WRITEBINARY       5
#define SYS_FILE_MODE_WRITEREAD         6
#define SYS_FILE_MODE_WRITEREADBINARY   7
#define SYS_FILE_MODE_APPEND            8
#define SYS_FILE_MODE_APPENDBINARY      9
#define SYS_FILE_MODE_APPENDREAD        10
#define SYS_FILE_MODE_APPENDREADBINARY  11


int arm_semihosting_open(const char* filename, int length, int mode);
int arm_semihosting_close(int file);
int arm_semihosting_writec(char c);
int arm_semihosting_write0(const char* s);
int arm_semihosting_write(int file, const char* buffer, int length);

#endif /* ARM_SEMIHOSTING_H */
