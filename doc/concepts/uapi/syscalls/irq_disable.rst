sys_irq_disable
"""""""""""""""

**API definition**

   .. code-block:: rust
      :caption: Rust UAPI for irq_disable syscall

      mod uapi {
         fn irq_disable(irq: u16) -> Status
       }

   .. code-block:: c
      :caption: C UAPI for irq_disable syscall

      enum Status sys_irq_disable(uint16_t IRQn);

**Usage**

   Disable (mask) given IRQ line at IRQ main controller level.

   .. note::
      the controller assignation is not yet supported with this API, and would
      require a modification to support this

   This syscall is made in order to allow userspace driver to disable a given IRQ.
   This is useful when the IRQ was previously enabled, and need, for the driver own
   specific requirements, to be disabled. This syscall do not check that the IRQ was
   previously enabled.

   This requires the interrupt line to be owned by a device of the given task.

   The kernel do not modify the IRQ enable flag of any devices here, but only masks
   the IRQ line from the main interrupt controller. The userspace driver is responsible
   for manipulating device-specific configuration.

   .. code-block:: C
      :linenos:
      :caption: disable given IRQ of an owned device

      if (sys_irq_disable(myIRQn) != STATUS_OK) {
            // [...]
      }

**Required capability**

   at least one CAP_DEV_xxx capa is required, as the IRQ disabling is linked to
   a given device.

**Return values**

   * STATUS_INVALID if the IRQ is not owned or do not exists
   * STATUS_DENIED if the task do not hold any DEV capability
   * STATUS_OK
