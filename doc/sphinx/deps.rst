LibSEPH external dependencies
=============================

libSEPH is made to be a standalone, portable library. Although, some external symbols
are required by the library.
These symbols are separated in two main categories:

   * generic primitives
   * lower medium access

generic primitives
------------------

.. function:: uint16_t htons(uint16_t x)

   Standard POSIX-1-2001 implementation of the inet `htons()` function, used in order to
   encode SEPH messages typed fields in big-endian

.. function:: uint16_t ntohs(uint16_t x)

   Standard POSIX-1-2001 implementation of the inet `ntohs()` function, used in order to
   decode SEPH messages typed fields from big-endian

.. function:: void *memcpy(void *dest, const void *src, size_t n)

    memcpy is a compiler primitive, that is automatically substitued at link time, except if a
    local implementation already exist and overload it. Used to store and load data from/to
    SEPH emission/reception buffer.

lower medium access
-------------------

.. function:: ssize_t spi_rx(uint8_t *rx_buf, size_t len, uint8_t default_tx)

    spi_rx aims to receive `len` bytes from the given `rx_buf` into the SPI device. As SPI is a
    always full-duplex communication media, for each byte read, another one must be sent.
    `default_tx` is the one sent each time a byte is read.

.. function:: ssize_t spi_tx(const uint8_t *tx_buf, uint8_t *rx_buf, size_t len)

    spi_tx aims to emit `len` bytes from the given `tx_buf` into the SPI device. As SPI is
    a always full-duplex communication media, for each byte sent, another one must be read.
    `rx_buf` is used to receive each byte from the slave.
