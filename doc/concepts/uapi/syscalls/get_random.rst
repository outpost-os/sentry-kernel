Get_Random
""""""""""

**API definition**:

.. code-block:: rust
   :caption: Rust UAPI for get_random syscall

   mod uapi {
      fn get_random() -> Status
   }

.. code-block:: c
   :caption: C UAPI for get_random syscall

   enum Status sys_get_random(void);

**Usage**:

Receive a 32bit length random value from the kernel RNG source in the `svc_exchange area`.

In devices that support hardware-based random source, the random source is using the hardware
source and respects the FIPS requirements on random generators.
This value can be used as a random seed for userspace-based cryptographic implemention.

.. code-block:: C
   :linenos:
   :caption: sample bare usage of sys_log

   uint32_t seed = 0;
   if (sys_get_random() != STATUS_OK) {
      // [...]
   }
   memcpy(&seed, _s_svc_exchange, sizeof(uint32_t));

.. note::
   the libShield libc can typically delivers PRNG rand() API seeded by this syscall. other
   cryptographic libraries such as libecc can also use this syscall as random source


**Required capability**

   CAP_CRY_KRNG

**Return values**

   * STATUS_DENIED if the task do not own the capability
   * STATUS_INVALID if the random source failed to delivers a FIPS-compliant random value
   * STATUS_OK
