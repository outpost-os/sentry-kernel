About user devices
------------------

.. _userspace_devices:

Device list generation and kernel storage
"""""""""""""""""""""""""""""""""""""""""

A word about project device tree usage
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The Sentry kernel hold a list of the active devices of the project that is
forged using the project's device tree. This is a useful helper as by doing
that, only active devices are stored in the Sentry kernel device list,
seen as a whitelist.

When a Outpost-based project modify its device tree to add or remove a device,
or update a board reference, modying some device's pinmux configuration, the
kernel device listing and associated configuration is automatically regenerated.

.. note::
    an active device is a device declared with `status = okay` in the
    device tree, meaning that it can be used at runtime. Others are ignored

The kernel device listing
~~~~~~~~~~~~~~~~~~~~~~~~~

The kernel list, generated using the device tree file, hold for each device
the following elements:

   * **devh_t**: the device handle, which uniquely identify the device on the
     system. This handle is also used when forging the corresponding _userspace
     driver metadata that include the very same field. This opaque is used in
     order to share the device identification between kernelspace and userspace.

   * **addresses**: base address and size, used for memory mapping. These informations
     are known by the userspace driver even if never directly manipulated, as
     userspace driver registers address are generated using SVD file. When using
     the *Map* UAPI, the *devh_t* is enough to map and clock the device.

   * **clocking**: this part is only hold by the kernel and correspond to the device
     clocking requirements, as defined in the device tree.

   * **capability**: Each user device is associated to a capability. This capability
     must be owned by the requiring task to manipulate it. More about device capabilities
     assignation is described in :ref:`auto-assignation of device capability <capa_deb_assign>` chapter.

   * **interrupts**: If the device holds interrupt lines, they are declared here,
     which allows to move between `IRQn` and `devh_t`.

   * **IOs**: If the device has configured I/Os (device tree's pinmux configuration), it is
     fully declared here. The complete I/0 configuration for the target board and SoC is
     stored directly in the device data thanks to the dt-bindings. This allows to fully configure
     I/O ports for the device when required.

.. note::
    see `Linux kernel Bindings documentation <https://elixir.bootlin.com/linux/latest/source/Documentation/devicetree/bindings>`_
    for more information on what is a binding


Auto-assignation of device capability
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. _capa_deb_assign:

(Un)mapping devices
"""""""""""""""""""


Linking IRQ with its owner
""""""""""""""""""""""""""
