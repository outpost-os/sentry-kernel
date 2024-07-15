Functional correctness
----------------------

.. _proof_wp:

.. index::
    single: WP; integration

About WP
""""""""

WP plugin is responsible for validate that a specific, formally described, subprogram contract
is strictly respected by the given sub-program. The subprogram contract defines the way
a subprogram behave, in terms of border effects (meaning any impact on inputs, output and external
elements), for all possible input values and context when being executed.

As a subprogram behavior depends on the way child subprogram themselves behave, demonstrate
a full correctness with WP require to demonstrate from leaf calls (without any external subprogram
dependencies) to root call, naming the entrypoint or the library interface for libraries.

A typical WP program contract would look like:

.. code-block:: c
  :linenos:
  :caption: Basic program contract for a statically forged table getter

    /*@
        behavior invalidid:
            assumes id >= SHM_LIST_SIZE;
            assigns \nothing;
            ensures \result == NULL;
        behavior validid:
            assumes id < SHM_LIST_SIZE;
            assigns \nothing;
            ensures \valid_read(\result);

        complete behaviors;
        disjoint behaviors;
    */
    shm_meta_t const *memory_shm_get_meta(size_t id)
    {
        shm_meta_t const *meta = NULL;
        if (unlikely(id >= SHM_LIST_SIZE)) {
            goto end;
        }
        meta = &shms[id];
        /*@ assert \valid_read(meta); */
    end:
        return meta;
    }

This is a typical leaf program, that is manipulating a build-time generated const table.
The program specification is using behaviors for simplicity, using separated explicit
program behaviors depending on its single input.
Behaviors are then proven to be 1. strictly separated, 2. complete (no potential input
exists that do not match any of the defined behaviors).

WP and composition-based correctness
""""""""""""""""""""""""""""""""""""

The kernel is voluntary composed of libraries, meaning that each part of the kernel, from
arch part to BSP implementation upto syscalls are separated libraries that depend on each-others
through unified, build-independent interfaces specification.

This allows, for example, to substitute a given BSP with another without impacting other libraries.
Another positive point is the enabling of compositional correctness :

Given a Sentry sub-library (e.g. libbsp), it is possible to demonstrate correctness of a library that
use it by considering its interface specification only.
Given that the current libbsp implementation has been separately proven to respect its own
interface specification, it is then possible to demonstrate the other library implementation, based
on the libbsp interface correctness as hypothesis.

Such model is efficient as:

   * it is possible to demonstrate faster each library separately, allowing parallelism
   * it is possible to hold multiple libbsp implementations (for e.g. for multiple SoCs) that can be
     demonstrated separately
   * it allows incremental proofness, when adding new implementations of the same interface, without
     breaking other components proofness

.. note::
    For easy plugable implementation over unified interface, the usage of C aliases is used, in order
    to link the corresponding implementation over the local API

Correctness of hardware manipulation
""""""""""""""""""""""""""""""""""""

Hardware manipulations are very low level specific behavior that are difficult to be considered for
pure software correctness analysis, as hardware behavior is not a part of software analysis.

Nonetheless, it is possible, when using sufficient fine-grain correctness analysis to inform
Frama-C that a given memory area (typically a io-mapped device) do exist and is accessible.

In Sentry, hardware accesses (typically register accesses) is made using uniquely defined API, such as
``iowrite32(size_t addr, uint32_t val)``.
Such an implementation, considering usage of Frama-C is written as:

.. code-block:: c
  :linenos:
  :caption: Typical low-level accessor

  /*@
    assigns *(uint32_t*)addr;
    */
  __attribute__((always_inline))
  static inline void iowrite32(size_t addr, uint32_t val)
  {
  #ifdef __FRAMAC__
      *(uint32_t*)addr = val;
  #else
      __iowrite32(addr, val);
  #endif
}

In that case, the `__iowrite32` symbol is not considered by Frama-C as it includes
some hardware specific ASM implementation such as memory barrier or memory order
arch-specific opcodes, that have now meaning for Frama-C.

Although, Frama-C is still able to considered that the address is effectively written,
and do generate a border effect in the `addr` memory cell. Moreover, any register is
considered as a volatile memory cell, meaning that any consecutive access may lead to
uncontrolled value read, which is an over-definition of a register.

In a statistical way, belong all potential retrieved values from a register, some leads
to error management paths (invalid register's value from the driver point of vue), others to correct paths.
This is costly but ensure that all potential paths can be triggered, whatever the register
fields are (write/clear, etc.).

From SVD to generated predicates
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Only defining a device as a basic *memory area* is not precise enough, and in Sentry, some
supplementary checks are automatically forged, using the SVD file describing the hardware.

In sentry, a lot of predicates are automatically forged using SVD specification. This is done when
generating all device register structure, address and fields from the SVD file. This is
done using the ``svd2json`` python package which allows the usage of jinja2 syntax to forge C files.

A typically autogenerated predicate for a ``lpuart`` driver looks like:


.. code-block:: c
  :linenos:
  :caption: Auto-generated device-related predicate

  /*@
    predicate lpuart_is_writable_register(ℤ r) = (
        r == 0x0 ||
        r == 0x0 ||
        r == 0x4 ||
        r == 0x8 ||
        r == 0xc ||
        r == 0x18 ||
        r == 0x1c ||
        r == 0x1c ||
        r == 0x20 ||
        r == 0x24 ||
        r == 0x28 ||
        r == 0x2c ||
        r == 0x30 ||
        \false
    );
  */

For all devices, the following predicate are defined:

   * `<devname>_is_writable_register`: the target offset-based memory started from the device address is writeable
   * `<devname>_is_readable_register`: the target offset-based memory started from the device address is readable
   * `<devname>_register_exists`: the target offset-based memory started from the device address is a real register

Using this three typical predicates, it is possible to:

   * demonstrate accesses to read-only, write-only and read-write registers (SVD conformity)
   * demonstrate that no potential memory hole that exists in the device is accedded

It is then possible to write code such as:

.. code-block:: c
  :linenos:
  :caption: Driver implementation with functional proofness

  /*@
     // MYDEVICE_BASE_ADDR is forged using SVD
     requires mydevice_register_exists(offset);
     requires mydevice_is_writeable_register(offset);
     assigns *(uint32_t*)(MYDEVICE_BASE + offset);
     // [...]
   */
  void mydevice_register_write(size_t offset, uint32_t value)
  {
      iowrite32(MYDEVICE_BASE + offset, value);
  }

.. note::
    By now, registers accessor are not generated, although, this can be easily done as
    all required information for register's accessor exists in the SVD file

Based on this leaf implementation of register accessor plus iowrite32, it is then
possible to define clean behaviors for upper layer API of a given device driver such as
`mydriver_probe()`, `mydriver_xmit()` and so on.

When defining a public contract for a given library interface though, some internal-specific
elements (private context manipulation, etc.) may requires to define separated public and private
contracts than need to be fusionned at proof time.
This may, then, requires to define higher grain, publicly defined behaviors, while local,
private specific behavior are kept hidden from external callers, as they have no meaning out of
the local compilation unit.
The usage of ghost functions and ghost variables are a useful helper for such cases, so that
sequential behaviors (context setting, locks, etc.) can be demonstrated through ghost code.
As ghost code is specific to Frama-C execution, they do not impact the target execution.
