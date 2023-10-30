// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <stdarg.h>
#include <string.h>
#include <inttypes.h>
#include <stdbool.h>
#include <sentry/ktypes.h>
#include <bsp/drivers/usart/usart.h>

#ifndef TEST_MODE
/* string related functions, for debug usage only */
static size_t sentry_strlen(const char *s)
{
    size_t result = 0;

    if (s == NULL) {
        /** TODO: panic to be called */
        goto err;
    }

    while (s[result] != '\0') {
        result++;
    }
err:
    return result;
}

/**
 * @brief Set n first bytes of a given memory area with a given byte value
 *
 * INFO: The C standard says that null argument(s) to string
 * functions produce undefined behavior.
 *
 * This is a global warning for the POSIX and C99/C99 libstring:
 * check your arguments before using it!
 *
 * Conforming to:
 * POSIX.1-2001, POSIX.1-2008, C89, C99, SVr4, 4.3BSD.
 */
static void   *sentry_memset(void *s, int c, unsigned int n)
{
    /* sanitation. This part can produce, as defined in the above
     * standard, an 'undefined behavior'. As a consequence, in all
     * string function, invalid input will produce, for integer
     * return, returning 42, for string return, returning NULL */
    if (unlikely(!s)) {
        goto err;
    }

    /* memseting s with c */
    char   *bytes = s;

    while (n) {
        *bytes = c;
        bytes++;
        n--;
    }
err:
    return s;
}

/* if not in the test suite case, aliasing to POSIX symbols */
size_t strlen(const char *s) __attribute__((alias("sentry_strlen")));
void* memset(void *s, int c, unsigned int n) __attribute__((alias("sentry_memset")));
#endif/*!TEST_MODE*/

/***********************************************
 * local utility functions
 **********************************************/

/*
 * Stdio functions (*printf) use a local ring buffer
 * to hold formated content before sending it to the
 * kernel via the kernel log API (typically sys_log()
 * for EwoK).
 * This ring buffer is holded in the libstd as a global
 * variable, local to this very file.
 * The ring buffer is initialized by the libstd at
 * application boot time, as the libstd is managing the
 * application starting point, including the ring buffer
 * and stack canaries initialization in the do_starttask()
 * function.
 *
 * All the ring-buffer associated function, used only by
 * the stdio functions, are implemented here.
 */


/*********************************************
 * Ring buffer and ring buffer utility functions
 */

// FIXME: must be Kconfig based
#define BUF_MAX 512

/*
 * .bss based, init to 0
 */
typedef struct debug_buffer {
    uint16_t offset;
    char buf[BUF_MAX];
} debug_buffer_t;

static debug_buffer_t dbgbuf;



/*
 * add a char in the ring buffer.
 *
 * INFO: by now, there is no bound check here. As a consequence, if
 * the ring buffer is full,
 *
 * WARNING: this function is the only one holding the ring buffer full
 * flag detection. As a consequence, any write access to the ring buffer
 * must be done through this function *exclusively*.
 */
static inline void dbgbuffer_write_char(const char c)
{
    /* if the buffer is full when we try to put char in it,
     * the char is discared, waiting for the ring buffer to be flushed.
     */
    if (unlikely(dbgbuf.offset == BUF_MAX)) {
        goto end;
    }
    dbgbuf.buf[dbgbuf.offset++] = c;
 end:
    return;
}

/*
 * Write a digit to the ring buffer.
 * This function convert a basic digit into a printable one.
 *
 * This function support usual bases such as binary
 *
 * INFO: this function can write digits in base up to hexadecimal one.
 * Bases bigger than hex are not supported.
 *
 */
static inline void dbgbuffer_write_digit(uint8_t digit)
{
    if (digit < 0xa) {
        digit += '0';
        dbgbuffer_write_char(digit);
    } else if (digit <= 0xf) {
        digit += 'a' - 0xa;
        dbgbuffer_write_char(digit);
    }
}

/*
 * copy a string to the ring buffer. This is an abstraction of the
 * dbgbuffer_write_char() function.
 *
 * This function is a helper function above dbgbuffer_write_char().
 */
 /*@
   requires \valid_read(str);
  */
static inline void dbgbuffer_write_string(char *str, uint32_t len)
{
    for (uint32_t i = 0; (i < len) && (str[i]); ++i) {
        dbgbuffer_write_char(str[i]);
    }
    return;
}

/*
 * Write a number in the ring buffer.
 * This function is a helper function above dbgbuffer_write_char().
 */
static inline void dbgbuffer_write_number(uint64_t value, uint8_t base)
{
    /* we define a local storage to hold the digits list
     * in any possible base up to base 2 (64 bits) */
    uint8_t number[64] = { 0 };
    int     index = 0;

    for (; (value / base) != 0; value /= base) {
        number[index++] = value % base;
    }
    /* finishing with most significant unit */
    number[index++] = value % base;

    /* Due to the last 'index++', index is targetting the first free cell.
     * We make it points the last *used* cell instead */
    index--;

    /* now we can print out, starting with the most significant unit */
    for (; index >= 0; index--) {
        dbgbuffer_write_digit(number[index]);
    }
}


static inline void dbgbuffer_flush(void)
{
    memset(&dbgbuf.buf[0], 0x0, BUF_MAX);
    dbgbuf.offset = 0;
}


/*
 * Print the ring buffer content (if there is some), and reset its
 * state to empty state.
 * The ring buffer is also memset'ed to 0.
 *
 * The buffer content is sent to the kernel log API.
 */
static inline kstatus_t dbgbuffer_display(void)
{
    /* usart as no notion of the byte type it emit. sending unsigned content */
    return usart_tx((uint8_t*)dbgbuf.buf, dbgbuf.offset);
}


/*********************************************
 * other, not ring-buffer associated local utility functions
 */

/*
 * Return the number of digits of the given number, considering
 * the base in which the number is encoded.
 */
static uint8_t dbgbuffer_get_number_len(unsigned long value, uint8_t base)
{
    /* at least, if value is 0, its lenght is 1 digit */
    uint8_t len = 1;

    /* now we calculate the number of digits in the number */
    for (; (value / base) != 0; value /= base) {
        len++;
    }
    return len;
}

/**************************************************
 * printf lexer implementation
 *************************************************/

typedef enum {
    FS_NUM_DECIMAL,
    FS_NUM_HEX,
    FS_NUM_UCHAR,
    FS_NUM_SHORT,
    FS_NUM_LONG,
    FS_NUM_LONGLONG,
    FS_NUM_UNSIGNED,
} fs_num_mode_t;

typedef struct {
    bool    attr_0len;
    bool    attr_size;
    uint8_t size;
    fs_num_mode_t numeric_mode;
    bool    started;
    uint8_t consumed;
    uint32_t strlen;
} fs_properties_t;


/*
 * Handle one format string (starting with '%' char).
 *
 * This function transform a format string into an effective content using given
 * va_list argument.
 *
 * The function updated the consumed argument with the number of char consumed
 * by the format string itself, and return 0 if the format string has been
 * correctly parsed, or 1 if the format string parsing failed.
 */
static kstatus_t print_handle_format_string(const char *fmt, va_list *args,
                                          uint8_t * consumed,
                                          uint32_t * out_str_len)
{
    kstatus_t status = K_ERROR_INVPARAM;
    fs_properties_t fs_prop = {
        .attr_0len = false,
        .attr_size = false,
        .size = 0,
        .numeric_mode = FS_NUM_DECIMAL, /*default */
        .started = false,
        .consumed = 0,
        .strlen = 0
    };

    /*
     * Sanitation
     */
    if (!fmt || !consumed) {
        return 1;
    }

    /* Let parse the format string ... */
    do {
        /*
         * Handling '%' character
         */
        switch (fmt[fs_prop.consumed]) {
            case '%':
                {
                    if (fs_prop.started == false) {
                        /* starting string format parsing */
                        fs_prop.started = true;
                    } else if (fs_prop.consumed == 1) {
                        /* detecting '%' just after '%' */
                        dbgbuffer_write_char('%');
                        fs_prop.strlen++;
                        /* => end of format string */
                        goto end;
                    } else {
                        /* invalid: there is content before two '%' chars
                         * in the same format_string (e.g. %02%) */
                        goto err;
                    }
                    break;
                }
            case '0':
                {
                    /*
                     * Handling '0' character
                     */
                    if (fs_prop.started == false) {
                        goto err;
                    }
                    fs_prop.attr_0len = true;
                    /* 0 must be completed with size content. We check it now */
                    while ((fmt[fs_prop.consumed + 1] >= '0') &&
                           (fmt[fs_prop.consumed + 1] <= '9')) {
                        /* getting back the size. Here only decimal values are handled */
                        fs_prop.size =
                            (fs_prop.size * 10) +
			    (fmt[fs_prop.consumed + 1] - '0');
                        fs_prop.consumed++;
                    }
                    /* if digits have been found after the 0len format string, attr_size is
                     * set to true
                     */
                    if (fs_prop.size != 0) {
                        fs_prop.attr_size = true;
                    }
                    break;
                }
            case 'd':
            case 'i':
                {
                    /*
                     * Handling integers
                     */
                    if (fs_prop.started == false) {
                        goto err;
                    }
                    fs_prop.numeric_mode = FS_NUM_DECIMAL;
                    int     val = va_arg(*args, int);
                    uint8_t len = dbgbuffer_get_number_len(val, 10);

                    if (fs_prop.attr_size && fs_prop.attr_0len) {
                        /* we have to pad with 0 the number to reach
                         * the desired size */
                        for (uint32_t i = len; i < fs_prop.size; ++i) {
                            dbgbuffer_write_char('0');
                            fs_prop.strlen++;
                        }
                    }
                    /* now we can print the number in argument */
                    dbgbuffer_write_number(val, 10);
                    fs_prop.strlen += len;
                    /* => end of format string */
                    goto end;
                }
            case 'l':
                {
                    /*
                     * Handling long and long long int
                     */
                    long    lval = 0;
                    long long llval = 0;
                    uint8_t len = 0;

                    if (fs_prop.started == false) {
                        goto err;
                    }
                    fs_prop.numeric_mode = FS_NUM_LONG;
                    /* detecting long long */
                    if (fmt[fs_prop.consumed + 1] == 'l') {
                        fs_prop.numeric_mode = FS_NUM_LONGLONG;
                        fs_prop.consumed++;
                    }
                    if (fs_prop.numeric_mode == FS_NUM_LONG) {
                        lval = va_arg(*args, long);

                        len = dbgbuffer_get_number_len(lval, 10);
                    } else {
                        llval = va_arg(*args, long long);

                        len = dbgbuffer_get_number_len(llval, 10);
                    }
                    if (fs_prop.attr_size && fs_prop.attr_0len) {
                        /* we have to pad with 0 the number to reach
                         * the desired size */
                        for (uint32_t i = len; i < fs_prop.size; ++i) {
                            dbgbuffer_write_char('0');
                            fs_prop.strlen++;
                        }
                    }
                    /* now we can print the number in argument */
                    if (fs_prop.numeric_mode == FS_NUM_LONG) {
                        dbgbuffer_write_number(lval, 10);
                    } else {
                        dbgbuffer_write_number(llval, 10);
                    }
                    fs_prop.strlen += len;
                    /* => end of format string */
                    goto end;
                }
            case 'h':
                {
                    /*
                     * Handling long and long long int
                     */
                    short   s_val = 0;
                    unsigned char uc_val = 0;
                    uint8_t len = 0;

                    if (fs_prop.started == false) {
                        goto err;
                    }
                    fs_prop.numeric_mode = FS_NUM_SHORT;
                    /* detecting long long */
                    if (fmt[fs_prop.consumed + 1] == 'h') {
                        fs_prop.numeric_mode = FS_NUM_UCHAR;
                        fs_prop.consumed++;
                    }
                    if (fs_prop.numeric_mode == FS_NUM_SHORT) {
                        s_val = (short) va_arg(*args, int);

                        len = dbgbuffer_get_number_len(s_val, 10);
                    } else {
                        uc_val = (unsigned char) va_arg(*args, int);

                        len = dbgbuffer_get_number_len(uc_val, 10);
                    }
                    if (fs_prop.attr_size && fs_prop.attr_0len) {
                        /* we have to pad with 0 the number to reach
                         * the desired size */
                        for (uint32_t i = len; i < fs_prop.size; ++i) {
                            dbgbuffer_write_char('0');
                            fs_prop.strlen++;
                        }
                    }
                    /* now we can print the number in argument */
                    if (fs_prop.numeric_mode == FS_NUM_SHORT) {
                        dbgbuffer_write_number(s_val, 10);
                    } else {
                        dbgbuffer_write_number(uc_val, 10);
                    }
                    fs_prop.strlen += len;
                    /* => end of format string */
                    goto end;
                }
            case 'u':
                {
                    /*
                     * Handling unsigned
                     */
                    if (fs_prop.started == false) {
                        goto err;
                    }
                    fs_prop.numeric_mode = FS_NUM_UNSIGNED;
                    uint32_t val = va_arg(*args, uint32_t);
                    uint8_t len = dbgbuffer_get_number_len(val, 10);

                    if (fs_prop.attr_size && fs_prop.attr_0len) {
                        /* we have to pad with 0 the number to reach
                         * the desired size */
                        for (uint32_t i = len; i < fs_prop.size; ++i) {
                            dbgbuffer_write_char('0');
                            fs_prop.strlen++;
                        }
                    }
                    /* now we can print the number in argument */
                    dbgbuffer_write_number(val, 10);
                    fs_prop.strlen += len;
                    /* => end of format string */
                    goto end;
                }
            case 'p':
                {
                    /*
                     * Handling pointers. Include 0x prefix, as if using
                     * %#x format string in POSIX printf.
                     */
                    if (fs_prop.started == false) {
                        goto err;
                    }
                    unsigned long val = va_arg(*args, unsigned long);
                    uint8_t len = dbgbuffer_get_number_len(val, 16);

                    dbgbuffer_write_string("0x", 2);
                    for (uint32_t i = len; i < fs_prop.size; ++i) {
                        dbgbuffer_write_char('0');
                        fs_prop.strlen++;
                    }
                    /* now we can print the number in argument */
                    dbgbuffer_write_number(val, 16);
                    fs_prop.strlen += len;
                    /* => end of format string */
                    goto end;
                }

            case 'x':
                {
                    /*
                     * Handling hexadecimal
                     */
                    if (fs_prop.started == false) {
                        goto err;
                    }
                    fs_prop.numeric_mode = FS_NUM_UNSIGNED;
                    uint32_t val = va_arg(*args, uint32_t);
                    uint8_t len = dbgbuffer_get_number_len(val, 16);

                    if (fs_prop.attr_size && fs_prop.attr_0len) {
                        /* we have to pad with 0 the number to reach
                         * the desired size */
                        for (uint32_t i = len; i < fs_prop.size; ++i) {
                            dbgbuffer_write_char('0');
                            fs_prop.strlen++;
                        }
                    }
                    /* now we can print the number in argument */
                    dbgbuffer_write_number(val, 16);
                    fs_prop.strlen += len;
                    /* => end of format string */
                    goto end;
                }
            case 'o':
                {
                    /*
                     * Handling octal
                     */
                    if (fs_prop.started == false) {
                        goto err;
                    }
                    fs_prop.numeric_mode = FS_NUM_UNSIGNED;
                    uint32_t val = va_arg(*args, uint32_t);
                    uint8_t len = dbgbuffer_get_number_len(val, 8);

                    if (fs_prop.attr_size && fs_prop.attr_0len) {
                        /* we have to pad with 0 the number to reach
                         * the desired size */
                        for (uint32_t i = len; i < fs_prop.size; ++i) {
                            dbgbuffer_write_char('0');
                            fs_prop.strlen++;
                        }
                    }
                    /* now we can print the number in argument */
                    dbgbuffer_write_number(val, 8);
                    fs_prop.strlen += len;

                    /* => end of format string */
                    goto end;
                }
            case 's':
                {
                    /*
                     * Handling strings
                     */
                    if (fs_prop.started == false) {
                        goto err;
                    }
                    /* no size or 0len attribute for strings */
                    if (fs_prop.attr_size && fs_prop.attr_0len) {
                        goto err;
                    }
                    char   *str = va_arg(*args, char *);
                    if (str == NULL) {
                        dbgbuffer_write_string("(null)", 6);
                        fs_prop.strlen += 6;
                    } else {
                        /* now we can print the number in argument */
                        dbgbuffer_write_string(str, strlen(str));
                        fs_prop.strlen += strlen(str);
                    }
                    /* => end of format string */
                    goto end;
                }
            case 'c':
                {
                    /*
                     * Handling chars
                     */
                    if (fs_prop.started == false) {
                        goto err;
                    }
                    /* no size or 0len attribute for strings */
                    if (fs_prop.attr_size && fs_prop.attr_0len) {
                        goto err;
                    }
                    unsigned char val = (unsigned char) va_arg(*args, int);

                    /* now we can print the number in argument */
                    dbgbuffer_write_char(val);

                    /* => end of format string */
                    goto end;
                }

                /* none of the above. Unsupported format */
            default:
                /* should not happend, unable to parse format string */
                goto err;

        }
        fs_prop.consumed++;
    } while (fmt[fs_prop.consumed]);
end:
    status = K_STATUS_OKAY;
 err:
    *out_str_len += fs_prop.strlen;
    *consumed = fs_prop.consumed + 1;   /* consumed is starting with 0 */
    return status;
}


/*
 * Print a given fmt string, considering variable arguments given in args.
 * This function *does not* flush the ring buffer, but only fullfill it.
 */
/*@
   requires \valid_read(fmt);
   requires \valid(sizew);
*/
static kstatus_t print_with_len(const char *fmt, va_list *args, size_t *sizew)
{
    kstatus_t status;
    int     i = 0;
    uint8_t consumed = 0;
    uint32_t out_str_s = 0;

    while (fmt[i]) {
        if (fmt[i] == '%') {
            status = print_handle_format_string(&(fmt[i]), args, &consumed, &out_str_s);
            if (unlikely(status != K_STATUS_OKAY)) {
                /* the string format parsing has failed ! */
                goto err;
            }
            i += consumed;
            consumed = 0;
        } else {
            out_str_s++;
            dbgbuffer_write_char(fmt[i++]);
        }
    }
    status = K_STATUS_OKAY;
err:
    *sizew = out_str_s;
    return status;
}


/*************************************************************
 * libstream exported API implementation: POSIX compilant API
 ************************************************************/

/*
 * Linux-like printk() API (no kernel tagging by now)
 */
__attribute__ ((format (printf, 1, 2))) kstatus_t printk(const char *fmt, ...)
{
    kstatus_t status = K_ERROR_INVPARAM;
    va_list args;
    size_t  len;

    if (unlikely(fmt == NULL)) {
        goto err;
    }
    /*
     * if there is some asyncrhonous printf to pass to the kernel, do it
     * before execute the current printf command
     */
    va_start(args, fmt);
    status = print_with_len(fmt, &args, &len);
    va_end(args);
    if (unlikely(status != K_STATUS_OKAY)) {
        dbgbuffer_flush();
        goto err;
    }
    /* display to debug output */
    dbgbuffer_display();
    dbgbuffer_flush();
err:
    return status;
}
