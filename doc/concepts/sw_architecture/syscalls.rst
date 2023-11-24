UAPI architecture
-----------------

About basics
^^^^^^^^^^^^

Sentry UAPI is implemented in Rust. In order to ensure compatibility with
both Rust and C worlds, the UAPI specification is made using `extern C`
external interface specification and types, and the crate defintion is
automatically exported to C headers using `cbindgen`.

This allows a single root of trust for all UAPI definition, for both languages,
in our case using a Rust definition that ensure struct typing usage.

The UAPI is design using the following:

   * a `systypes` package, that define all Sentry types shared with userspace
   * a `uapi` package, that hold the UAPI implementation in rust, depending on `systypes`

In the kernel counter part:

   * a `sysgate` package, that define all the kernel syscall implementation, and
     also depend on `systypes`



Syscall definition
^^^^^^^^^^^^^^^^^^



Exit
""""

**API definition**:

.. code-block:: rust

   fn uapi::exit(status: i32) -> u32

.. code-block:: c

   sys_return_t sys_exit(uint32_t status);


**Usage**:

   Terminate the current job with status code given in argument.
   Any non-zero status code is considered as an abnormal status code and is
   passed to job termination mechanism.

**Required capability**

   None.

**Return values**

   End the current job, never returns.

.. note::
    The goal here is to support runtime-based termination call with potential
    application developper hook (sigterm handler), so that a unified central handler
    can react to various status code values, wherever the `exit()` call is made in the
    job implementation.
