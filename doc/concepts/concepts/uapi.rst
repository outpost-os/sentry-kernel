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

Sentry events
^^^^^^^^^^^^^

The Sentry UAPI is built in order to allow an easy event-driven userspace implementation
with easy, well-known abstraction. It allows userspace implementation of POSIX API such as `poll()`,
`timer_create()`, `timer_set()`, `timer_get()` or `clock_gettime()`, which are
POSIX.1-2001 compliant API.

To do this, all events sources are using a single abstraction model using handlers,
as defined in :ref:`handlers <handles>` dedicated chapter. Handles are a unified mechanism
in order to support allow synchronisation mechanisms with multiple sources.
For example, a task can wait for multiple event sources at a time, such as interrupts, signals,
and IPC, and being unlocked automatically as soon as any of them have risen.

This is done using the `WaitForEvent` UAPI. As a job may have multiple events waiting
in the same time, the Sentry kernel define a predictable receive order, when executing this
syscall:

   * Interrupts have the higher priority
   * Signals have middle priority
   * IPC have low priority

For each event type, if multiple elements of the same event is waiting, the kernel returns
the events starting with the first that have risen (FIFO model). The syscall always return
only one event at a time.

.. figure:: ../_static/figures/waiting_events.png
   :width: 90%
   :alt: Receiving events
   :align: center

   Receiving events with Sentry

While it is possible to listen to multiple event types at a time, events that are emitted
by a job are always unique. A job can only emit a single event once, the event being
a signal or an IPC.
Emitting and receiving IPC is made using the :ref:`SVC Exhcange <svc_exchange>` region of
each task between which IPC data is copied by the kernel.

Signals are non-blocking events, meaning that the job is not preempted by the emission of
a signal. As this API is non-blocking, only a single signal can be received by a task from
a single other task at once. If a job emit another signal to the same peer task, while the
first signal is not yet received, the syscall will return a SYS_RET_BUSY error, informing
that the peer has not yet read the previous signal.

On the other hands, IPC are blocking events. When emitting an IPC, the job is preempted and
will not be resheduled while the peer has not received the IPC. Once the peer receive the IPC,
the emitting job is scheduled again and will get out of the `SendIPC()` syscall.

Even in `SendIPC()` is a blocking call that seems to never fail at first, it may
fail though, if the kernel detect a direct or indirect deadlock, as described in the
following figure:

.. figure:: ../_static/figures/deadlock.png
   :width: 60%
   :alt: IPC deadlock detection
   :align: center

   IPC deadlock detection
