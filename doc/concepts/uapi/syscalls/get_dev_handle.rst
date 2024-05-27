sys_get_device_handle
"""""""""""""""""""""
.. _uapi_dev_handle:

**API definition**

.. code-block:: rust
   :caption: Rust UAPI for get_task_handle syscall

   mod uapi {
      fn get_device_handle(dev_label: u32) -> Status
   }

.. code-block:: c
   :caption: C UAPI for get_task_handle syscall

   enum Status sys_get_device_handle(uint32_t dev_label);

**Usage**

   In Sentry, all devices are uniquely identified by ther handle. At bootup,
   the userspace task only hold the device label, which is generated using the
   ``dts`` file. This label is unique to the system and may vary depending on
   the project device tree file evolution.

   In order to manipulate devices (for e.. to map or unmap it), a task must
   require the device handle from the kernel, using the device label as unique
   identifier.

   As a consequence, before manipulating a device, a device driver (or the
   corresponding task holding it) must first get back the device handle. While
   got, the handle is valid for all the current OS lifecycle.

   .. note::
       the device identifier is stored in the devinfo_t const structure generated using the
       dts file

   .. code-block:: C
      :linenos:
      :caption: sample bare usage of sys_get_device_handle

      uint32_t my_dev_label = devinfo[MYDEVICE].id;
      devh_t my_dev_handle;
      if (sys_get_device_handle(my_dev_label) != STATUS_OK) {
         // [...]
      }
      copy_to_user(&my_dev_handle, sizeof(devh_t));

**Required capability**

   None in this syscall while the device is owned by the current task.

   .. warning::
       if the application do not hold the corresponding device capability, other
       device-related syscalls, such as sys_map_dev() will failed with STATUS_DENIED.

**Return values**

   * STATUS_INVALID if the label do not exist or is owned by another task
   * STATUS_OK
