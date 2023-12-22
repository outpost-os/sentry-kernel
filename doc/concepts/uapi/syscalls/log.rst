Log
"""

**API definition**:

.. code-block:: rust
   :caption: Rust UAPI for log syscall

   fn uapi::log(length: usize) -> Status

.. code-block:: c
   :caption: C UAPI for log syscall

   enum Status sys_log(size_t length);

**Usage**:

Emit the given logs data length from the `svc_exchange area` toward the log output.


In release mode, the UAPI will just do nothing, avoiding any ifdef usage at
application level. The kernel binary do not host any debug functionality and will
simply ignore such requests

.. code-block:: C
   :linenos:
   :caption: sample bare usage of sys_log

   enum Status res = STATUS_INVALID;
   if (len <=> CONFIG_SVC_EXCHANGE_AREA_LEN) {
      memcpy(&_s_svc_exchange, data, len);
      res = sys_log(len);
   }

.. note::
   the libShield libc typically delivers a printf() implementation, while the UAPI delivers
   the rust println! macro to simplify the usage of the sys_log() function

.. warning::
   the log syscall do **not** execute any parsing of the logged data. This allows binary
   transmission to the debug output if needed and requires upper layers to implement
   the format string parser. The syscall do **not need** any trailing zero (c string format)

**Required capability**

   None.

**Return values**

   * STATUS_INVALID if length is bigger than CONFIG_SVC_EXCHANGE_AREA_LEN
   * STATUS_OK
