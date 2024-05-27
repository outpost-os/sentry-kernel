sys_irq_acknowledge
"""""""""""""""""""

**API definition**

   .. code-block:: rust
      :caption: Rust UAPI for irq_acknowledge syscall

      mod uapi {
         fn irq_acknowledge(irq: u16) -> Status
       }

   .. code-block:: c
      :caption: C UAPI for irq_acknowledge syscall

      enum Status sys_irq_acknowledge(uint16_t IRQn);

**Usage**

   Acknowledge (clear pending) given IRQ line.

   This syscall is made in order to allow userspace driver to acknowledge a given IRQ
   when the IRQ handler is executed.

   This requires the interrupt line to be owned by a device of the given task.

   .. code-block:: C
      :linenos:
      :caption: acknowledge given IRQ of an owned device

      int my_handler(uint16_t IRQn) {
         // executing the handler
         // [...]
         if (sys_irq_acknowledge(myIRQn) != STATUS_OK) {
            // [...]
         }
         // [...]
      }

**Required capability**

   at least one CAP_DEV_xxx capa is required, as the IRQ acknowledgement is linked to
   a given device.

**Return values**

   * STATUS_INVALID if the IRQ is not owned or do not exists
   * STATUS_DENIED if the task do not hold any DEV capability
   * STATUS_OK
