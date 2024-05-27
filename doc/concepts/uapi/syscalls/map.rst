sys_map_dev
"""""""""""

**API definition**

   .. code-block:: rust
      :caption: Rust UAPI for device mapping syscall

      mod uapi {
         fn map_dev(devh: dev_handle) -> Status
         fn unmap_dev(devh: dev_handle) -> Status
      }

   .. code-block:: c
      :caption: C UAPI for device mapping syscall

      enum Status sys_map_dev(devh_t dev);
      enum Status sys_unmap_dev(devh_t dev);

**Usage**

   Map a given device into the task context.
   If the device has never been mapped before:

      * configure the device input clock(s).
      * enable interrupts line associated to the device if set in the device node

   Once returning from this syscall, the device is mapped at its corresponding
   address (io-mapped address) as declared in its device tree node.

   The `devh_t` device handle value is a property of the device driver library that
   has been forged at build time and must be used as an opaque field.

   .. code-block:: C
      :linenos:
      :caption: sample bare usage of sys_map

      enum Status res = STATUS_INVALID;
      devh_t mydriver_handle = mydriver_get_handle();
      res = sys_map_dev(mydriver_handle);
      // manipulating device registers.....
      res = sys_unmap_dev(mydriver_handle);

   .. note::
      the libShield libc typically delivers a mmap() implementation with, for
      example, the following usage type:

      ``addr = mmap(NULL, 0, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, devh, 0);``


**Required capability**

   The required capability depend on the concerned device, with the following capability
   mapping:

      * CAP_DEV_BUSES: All buses such as USART, SPI, CAN, I2C...
      * CAP_DEV_IO: bare general purpose I/O manipulation (e.g. LED or button)
      * CAP_DEV_DMA: DMA streams, and DMA masters such as GPU, DMA2D
      * CAP_DEV_ANALOG: analogic devices, such as DAC and ADC
      * CAP_DEV_TIMER: hardware timers
      * CAP_DEV_STORAGE: storage devices (MMIO, etc.)
      * CAP_DEV_CRYPTO: cryptographic accelerator (HMAC, CRYP, etc.)
      * CAP_DEV_CLOCK: real-time clock, GPS, when in-SoC
      * CAP_DEV_POWER: power-related devices
      * CAP_DEV_NEURAL: neural accelerators

**Return values**

   * STATUS_INVALID if length is bigger than CONFIG_SVC_EXCHANGE_AREA_LEN
   * STATUS_PERM if device or device capability capability is not owned
   * STATUS_DENIED if device or device capability capability is not owned
   * STATUS_ALREADY_MAPPED if device is already mapped
   * STATUS_OK if device was successfully mapped
