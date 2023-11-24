UAPI model
----------

UAPI introduction
"""""""""""""""""

The Sentry kernel is designed in order to deliver an easy to use, generic and
portable UAPI.
The Sentry UAPI is written and Rust and is defined as the following in the
Syscall namepace:

.. literalinclude:: ../../../uapi/include/uapi/types/types.rs
  :language: rust
  :lines: 10-22
  :linenos:

This UAPI is build in order to respond to all needs for which the kernel execution
is required.

Any other need should be considered as being under the responsability of a dedicated
task that deliver a value added service to others. In that later case, the API is
IPC and signal based and the kernel remains only responsible of the task partitioning.

As the overall UAPI is written in Rust, the Sentry UAPI documentation (i.e. Sentry
application developer interface specification) is generated through
`RustDoc <https://doc.rust-lang.org/rustdoc/what-is-rustdoc.html>`_

UAPI abstraction
""""""""""""""""

The Sentry UAPI is not built to be used directly by userspace task, even if it
remains possible. The UAPI Rust crate is designed to be associated to:

   * a full Rust ecosystem including libCore and libStd for Rust developments
   * libShield, as a POSIX PSE51-2001 implementation (in Rust too, but exporting POSIX C API)
     for C runtime

Using standard abstractions allows userspace code to stay portable, making easier
userspace code testing and debugging.
