Syscalls
--------

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


.. index::
  single: UAPI; syscalls
  single: UAPI; syscall definition



Syscall definition
^^^^^^^^^^^^^^^^^^

.. index::
  single: sys_alarm; definition
  single: sys_alarm; usage
.. include:: syscalls/alarm.rst

.. index::
  single: sys_exit; definition
  single: sys_exit; usage
.. include:: syscalls/exit.rst

.. index::
  single: sys_get_random; definition
  single: sys_get_random; usage
.. include:: syscalls/get_random.rst

.. index::
  single: sys_get_task_handle; definition
  single: sys_get_task_handle; usage
.. include:: syscalls/get_task_handle.rst

.. index::
  single: sys_gpio_get; definition
  single: sys_gpio_get; usage
.. include:: syscalls/gpio_get.rst

.. index::
  single: sys_gpio_reset; definition
  single: sys_gpio_reset; usage
.. include:: syscalls/gpio_reset.rst

.. index::
  single: sys_gpio_set; definition
  single: sys_gpio_set; usage
.. include:: syscalls/gpio_set.rst

.. index::
  single: sys_gpio_toggle; definition
  single: sys_gpio_toggle; usage
.. include:: syscalls/gpio_toggle.rst

.. index::
  single: sys_irq_acknowledge; definition
  single: sys_irq_acknowledge; usage
.. include:: syscalls/irq_acknowledge.rst

.. index::
  single: sys_log; definition
  single: sys_log; usage
.. include:: syscalls/log.rst

.. index::
  single: sys_map; definition
  single: sys_map; usage
.. include:: syscalls/map.rst

.. index::
  single: sys_send_ipc; definition
  single: sys_send_ipc; usage
.. include:: syscalls/send_ipc.rst

.. index::
  single: sys_send_signal; definition
  single: sys_send_signal; usage
.. include:: syscalls/send_signal.rst
