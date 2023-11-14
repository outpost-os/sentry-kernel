Hardware support in Sentry
--------------------------

.. _bsp:

Basics about HAL
^^^^^^^^^^^^^^^^

Sentry HAL is built around two main blocks, including a set of *device drivers*
and a *platform support* component, corresponding to the board and the architecture
support package of the micro-kernel.

As this is a micro-kernel, these two components are quite small, reduced to what
is required to bootup, secure and spawn the userspace tasks.


Adding a new board
^^^^^^^^^^^^^^^^^^

A new board in Sentry, while the board SoC is supported, should not require any
source modification. The board configuration and pinout should be fully defined
throug the board device tree, and thus being considered as an input information for
the kernel while the corresponding SoC required platform and device drivers are
supported.

.. note::

  Using full dts-based board support allows to keep the very same Sentry git tag or
  source distribution (dist target) for board evolution in a given project, ensuring that
  no modification has been made to a source that have passed quality gate or certifications

Adding a new SoC
^^^^^^^^^^^^^^^^

Adding a new SoC is a work that may require more or less work depending on the level
of platform related modifications. For a new SoC for which all the platform related
part is already supported (e.g. adding a new armv7m SoC), only missing drivers or
upgrade to incomplete drivers is required.

Such a modification should only impact the `src/drivers` subdir. The Sentry-private driver
API, exposed in `include/bsp` and used by managers, should not be modified as this API has
no device-specific element.
By modifying or adding only corresponding driver, the impact of such a modification should
not generate border effects in others kernel parts, including managers and syscalls, and should
not require any modification of unit tests other than including new, new SoC specific, tests.

Adding a new architecture
^^^^^^^^^^^^^^^^^^^^^^^^^

Adding a new architecture correspond to the addition of a new directory in the `src/arch`
subdir, associated to `include/sentry/arch/`. This new directory add all the new hardware
specific implementations. The hardware dispatcher, that use the complier's variables to
know which target architecture is used, need to be updated in `include/sentry/arch/asm-genric`
directory.

.. note::

    `include/sentry/arch/asm-genric` directory is used as a trampoline to hardware specific
    headers. Headers in that directory are dispatcher to correct hardware subdirectory headers
    and may, for some of them, hold some generic code.

    Headers out of `arch/asm-*` directories are headers for components that have no link with
    hardware related features.
