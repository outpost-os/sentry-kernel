sys_irq_enable
""""""""""""""

**API definition**

   .. code-block:: rust
      :caption: Rust UAPI for irq_enable syscall

      mod uapi {
         fn irq_enable(irq: u16) -> Status
       }

   .. code-block:: c
      :caption: C UAPI for irq_enable syscall

      enum Status sys_irq_enable(uint16_t IRQn);

**Usage**

   Enable (unmask) given IRQ line at IRQ controller level.

   .. note::
      the controller assignation is not yet supported with this API, and would
      require a modification to support this

   This syscall is made in order to allow userspace driver to enable a given IRQ once
   the device is properly configured.

   This requires the interrupt line to be owned by a device of the given task.

   The kernel do not modify the IRQ enable flag of any devices here, but only unmasks
   the IRQ line in the main interrupt controller. This means that an interrupt may rise
   as soon as the kernel unmask the interrupt, pushing an interrupt event in the task's input
   queue just after the syscall execution.
   The userspace driver is responsible for (un)masking the interrupt-enable flag at
   device level.

   .. code-block:: C
      :linenos:
      :caption: enable given IRQ of an owned device

      // configure the device (and device-relative IRQ config)
      // [...]
      if (sys_irq_enable(myIRQn) != STATUS_OK) {
            // [...]
      }

**Required capability**

   at least one CAP_DEV_xxx capa is required, as the IRQ enabling is linked to
   a given device.

**Return values**

   * STATUS_INVALID if the IRQ is not owned or do not exists
   * STATUS_DENIED if the task do not hold any DEV capability
   * STATUS_OK
