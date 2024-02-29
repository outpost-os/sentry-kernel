Wait_For_Event
""""""""""""""

**API definition**:

.. code-block:: rust
   :caption: Rust UAPI for wait_for_event syscall

   mod uapi {
      fn wait_for_event(mask: u8, timeout: u32) -> Status

      fn get_received_event_type() -> EventType
      fn get_received_event_length() -> u8
      fn get_received_event_data(length: u8) -> mut *data
   }

.. code-block:: c
   :caption: C UAPI for wait_for_event syscall

   typedef enum EventType {
     EVENT_TYPE_NONE = 0,
     EVENT_TYPE_IPC = 1,
     EVENT_TYPE_SIGNAL = 2,
     EVENT_TYPE_IRQ = 4,
     EVENT_TYPE_ALL = 7,
   } EventType;

   enum Status sys_wait_for_event(uint8_t mask, uint32_t timeout);
   void get_received_event_type(void);
   uint8_t get_received_event_length(void);
   uint8_t *get_received_event_data();

.. warning::
    the get_received_event_data directly return a pointer on the data part of
    the exchange area. Remember to copy the data if needed as other syscalls will
    erase the content of svc_exchange

**Usage**:

This syscall is built in order to be a blocking point of the calling thread.
This syscall handles external events blocking reception (IPCs, signals or interrupt).

In order to wait for specific event(s) only, the mask argument is used in order to
filter some specific inputs events using logical OR between waited event(s).

Any received event is delivered with a TLV basic content in the **svc_exchange** area:

```
[T:u8][L:u8][magic:16][data]
```

The T field is keeping the enumerate EventMask encoding, in order to identify the
type of received event.

.. note::
    Only one type of event per call is returned, meaning that only EVENT_IPC, EVENT_SIGNAL
    or EVENT_IRQ is used for the T field

The L field always specify the exact data size. This means that:

   * An IPC event L field is equal to the effective received bytes
   * A signal event L field is always equal to 4 (signal value length)
   * An IRQ fevent L field hold one or more IRQ numbers. Each IRQ value being
     encoded on 16 bits values, meaning that the number of received IRQ is equal
     to L/2. In that last case, the IRQ are stored in the chronologically received order

The magic field is used in order to detect invalid exchange content easily, to prevent
invalid data values access from userspace upper layers.
