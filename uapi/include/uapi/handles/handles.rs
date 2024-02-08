#![no_std]
#![allow(non_camel_case_types)]

#[cfg(not(feature = "cbindgen"))]
macro_rules! make_member {
    { $name:ident ($place:expr) {$($body:tt)*} } => {
        #[derive(Default, Clone, Copy)]
        #[repr(transparent)]
        pub struct $name(u32);

        impl $name {
            // Static check: if there were not exactly 32 bits defined in the bitfield
            // this will not compile.
            const _STATIC_CHECK: u8 = [0][$place - 32];

            pub fn bits(&self) -> u32 {
                self.0
            }

            $($body)*
        }

        impl From<u32> for $name {
            fn from(inval: u32) -> $name {
                $name(inval)
            }
        }
    };
    {
        $name:ident
        ($place:expr)
        {$($body:tt)*}
        $member:ident $length:literal
        $($tail:tt)*
    } => {
        make_member!{
            $name
            ($place + $length)
            {
                $($body)*

                paste::paste! {
                pub fn [<get_ $member>] (&self) -> u32 {
                    const MASK: u32 = (1<<$length) - 1;
                    self.0.wrapping_shr($place) & MASK
                }

                pub fn [<set_ $member>] (&mut self, val: u32) {
                    const MASK: u32 = (1<<$length) - 1;
                    self.0 = (self.0 & !MASK.wrapping_shl($place) ) | (val & MASK).wrapping_shl($place);
                }
                }
            }
            $($tail)*
        }
    };
}

#[cfg(not(feature = "cbindgen"))]
macro_rules! bitfield_u32 {
    (
        $(#[$doc:meta])*
        pub struct $name:ident {
            $(
                $(#[$comment:meta])*
                $member:ident : $length:literal,
            )*
        }
    ) => {
        make_member!{ $name (0) {} $($member $length)* }
    }
}

#[cfg(feature = "cbindgen")]
macro_rules! bitfield_u32 {
    (
        $(#[$doc:meta])*
        pub struct $name:ident {
            $(
                $(#[$comment:meta])*
                $member:ident : $length:literal,
            )*
        }
    ) => {
        #[repr(packed)]
        #[repr(C)]
        pub struct $name {
            $(
                $(#[$comment])*
                #[doc = concat!("cbindgen:bitfield=", $length)]
                $member : u32,
            )*

        }
    }
}

bitfield_u32! {
    /// Any of the above resource can be acceded only through a handle. This handle is unique and
    /// must be used as an opaque in userspace implementation.
    /// This allows fully-portable and reusable implementation of tasks, libraries, drivers so
    /// avoiding any hard-coded content. All SoC specific content is manipulated by device-trees
    /// exclusively, generating the overall handles.
    pub struct ResourceHandle {
        /// forged from dtsi, matches resource type
        resource_type : 4,
        /// task namespace, matches task label, forged at build time
        task_ns : 12,
        /// forged from dtsi if not a process, or at process startup
        resource_id : 16,
    }
}

// pub const HANDLE_ID_SHIFT: u32 = 13;
// pub const HANDLE_ID_SIZE: u32 = 16;
// pub const HANDLE_ID_MASK: u32 = ((1 << HANDLE_ID_SIZE) - 1) << HANDLE_ID_SHIFT; // 0x7fff_8000;
// pub const HANDLE_FAMILY_SHIFT: u32 = HANDLE_ID_SIZE + HANDLE_ID_SHIFT;
// pub const HANDLE_FAMILY_SIZE: u32 = 3;
// pub const HANDLE_FAMILY_MASK: u32 = ((1 << HANDLE_FAMILY_SIZE) - 1) << HANDLE_FAMILY_SHIFT; // 0xe000_0000;

bitfield_u32! {
    /// Signal handle
    pub struct sigh_t {
        source : 16,
        /// unique id for current handle (current device, task, etc)
        id : 13,
        family : 3,
    }
}

bitfield_u32! {
    /// IPC handle
    pub struct ipch_t {
        /// IPC source (task label)
        source : 16,
        /// IPC len in bytes
        len : 13,
        family : 3,
    }
}

bitfield_u32! {
    /// Device handle
    pub struct devh_t {
        /// device required dev-capabilities (mask)
        dev_cap : 12,
        reserved : 1,
        /// unique id for current handle (current device, task, etc)
        id : 16,
        family : 3,
    }
}

bitfield_u32! {
    /// Task handle
    pub struct taskh_t {
        /// current spawn id (start with 1)
        rerun : 13,
        /// unique id for current handle (current device, task, etc)
        id : 16,
        family : 3,
    }
}

bitfield_u32! {
    /// io_handle
    #[align(4)]
    pub struct ioh_t {
        /// 0=A, 1=B...
        ioport   : 6,
        /// 0=0, 1=1, ...
        iopin    : 6,
        /// this part if fixed
        reserved : 1,
        /// unique id for current handle (current device, task, etc)
        id       : 16,
        family  : 3,
    }
}

bitfield_u32! {
    /// irq_handle
    pub struct irqh_t {
        /// IRQ Number
        irqn     : 8,
        reserved : 5,
        /// unique id for current handle (current device, task, etc)
        id       : 16,
        family  : 3,
    }
}

bitfield_u32! {
    /// shm_handle
    pub struct shmh_t {
        /// TODO define reserved content
        reserved : 13,
        /// unique id for current handle (current device, task, etc)
        id       : 16,
        family  : 3,
    }
}

bitfield_u32! {
    /// dma_handle
    pub struct dmah_t {
        /// TODO define reserved content
        reserved : 13,
        /// unique id for current handle (current device, task, etc)
        id       : 16,
        family  : 3,
    }
}

#[cfg(feature = "cbindgen")]
#[no_mangle]
pub extern "C" fn handles_keep_me(
    a: sigh_t,
    b: ipch_t,
    c: devh_t,
    d: taskh_t,
    e: ioh_t,
    f: irqh_t,
    g: shmh_t,
    h: dmah_t,
    i: ResourceHandle,
) {
}
