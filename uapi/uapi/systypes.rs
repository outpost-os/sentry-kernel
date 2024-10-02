// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/// This library defines types (structs, enums, ...) related to syscalls,
/// that need to be shared between the kernel and the uapi.
///
/// Most important enum is `Syscall`, which defines the list of available
/// syscalls and sets their identifier/number.
///

/// This macro takes an enum and implements fallible conversion from a u8
/// exhaustively, as required by the SVC Handler.
///
/// ```
/// pub enum Syscall {
///     Exit,
/// }
///
/// impl TryFrom<u8> for Syscall {
///     type Error = ();
///     fn try_from(v: u8) -> Result<Self, Self::Error> {
///         match v {
///             x if x == Syscall::Exit as u8 => Ok(Syscall::Exit),
///             _ => Err(())
///         }
///     }
/// }
/// ```
/// (inspired by https://stackoverflow.com/a/58715864)
///
/// It also ensures that there cannot be a mismatch between the u8 value
/// used to define the enum, and the value used for converting to it.
macro_rules! syscall_list {
    ($vis:vis enum $name:ident {
        $($vname:ident,)*
    }) => {
        #[repr(C)]
        #[cfg_attr(debug_assertions, derive(Debug))]
        $vis enum $name {
            $($vname,)*
        }

        impl TryFrom<u8> for $name {
            type Error = Status;

            fn try_from(v: u8) -> Result<Self, Self::Error> {
                match v {
                    $(x if x == $name::$vname as u8 => Ok($name::$vname),)*
                    _ => Err(Status::Invalid),
                }
            }
        }
    }
}

syscall_list! {
pub enum Syscall {
    Exit,
    GetProcessHandle,
    GetDeviceHandle,
    Yield,
    Sleep,
    Start,
    MapDev,
    MapShm,
    UnmapDev,
    UnmapShm,
    SHMSetCredential,
    SendIPC,
    SendSignal,
    WaitForEvent,
    PmManage,
    PmSetClock,
    Log,
    Alarm,
    GetRandom,
    GetCycle,
    GpioGet,
    GpioSet,
    GpioReset,
    GpioToggle,
    GpioConfigure,
    IrqAcknowledge,
    IrqEnable,
    IrqDisable,
    GetShmHandle,
    GetDmaStreamHandle,
    DmaStartStream,
    DmaStopStream,
    DmaGetStreamStatus,
    ShmGetInfos,
    DmaAssignStream,
    DmaUnassignStream,
}
}

macro_rules! mirror_enum {
    ($to:ty, $vis:vis enum $name:ident {
        $($vname:ident,)*
    }) => {
        #[repr(C)]
        $vis enum $name {
            $($vname,)*
        }

        impl TryFrom<$to> for $name {
            type Error = Status;

            fn try_from(v: $to) -> Result<Self, Self::Error> {
                match v {
                    $(x if x == $name::$vname as $to => Ok($name::$vname),)*
                    _ => Err(Status::Invalid),
                }
            }
        }
    }
}

/// Sentry syscall return values
/// NonSense must never be returned, as it means that an
/// asynchronously updated return value.... has not been updated at all
/// This must raise a security exception. All syscalls that can't set
/// they return code synchronously (e.g. IPC), MUST use this value as
/// default one
#[repr(C)]
#[cfg_attr(debug_assertions, derive(Debug, PartialEq))]
#[derive(Copy, Clone)]
pub enum Status {
    Ok,
    Invalid,
    Denied,
    NoEntity,
    Busy,
    AlreadyMapped,
    Critical,
    Timeout,
    Again,
    Intr,
    Deadlk,
}

impl From<u32> for Status {
    fn from(status_int: u32) -> Status {
        match status_int {
            0 => Status::Ok,
            1 => Status::Invalid,
            2 => Status::Denied,
            3 => Status::NoEntity,
            4 => Status::Busy,
            5 => Status::AlreadyMapped,
            6 => Status::Critical,
            7 => Status::Timeout,
            8 => Status::Again,
            9 => Status::Intr,
            10 => Status::Deadlk,
            _ => panic!(),
        }
    }
}

/// A process label is a development-time fixed identifier that can be used hardcoded
///  in the source code. This can be used in order to get back remote process effective
/// identifier from label at any time in order to communicate
pub type ProcessLabel = u32;

/// A shm label is a development-time fixed identifier that can be used hardcoded
/// in the source code. This label is set in the device-tree in the shm declaration,
/// and can be used in order to get back the effective shm handler from it in order
/// to manipulate it
pub type ShmLabel = u32;

/// A stream label is a development-time fixed identifier that can be used hardcoded
/// in the source code in order to dientify declared DMA streams.
/// This label is set in the device-tree in the stream declaration,
/// and can be used in order to get back the effective DMA stream handler from it in order
/// to manipulate it
pub type StreamLabel = u32;

/// List of Sentry resource types
///
/// Multiple opaque are used in userspace. This opaques are namespaced and
/// manipulated at kernel level to ensure unicity, identification, etc.
#[repr(C)]
pub enum ResourceType {
    PID = 1,
    Device = 2,
    SHM = 4,
    DMA = 8,
}

#[repr(C)]
pub enum EventType {
    None = 0,
    Ipc = 1,
    Signal = 2,
    Irq = 4,
    Dma = 8,
    All = 15,
}

impl From<EventType> for u32 {
    fn from(event: EventType) -> u32 {
        match event {
            EventType::None => 0,
            EventType::Ipc => 1,
            EventType::Signal => 2,
            EventType::Irq => 4,
            EventType::Dma => 8,
            EventType::All => 15,
        }
    }
}

/// Erase type that can be used to clear the SVC_Exchange.
///
/// There are two types of erase model:
/// - Zeroify, that write 0x0 pattern in the SVC exchange zone
/// - Random, that write a random pattern
///
/// By now, only Zeroify ils supported.
#[repr(C)]
pub enum EraseType {
    Zeroify = 0x5a,
    Random = 0xa5,
}

impl From<EraseType> for u32 {
    fn from(etype: EraseType) -> u32 {
        match etype {
            EraseType::Zeroify => 0x5a,
            EraseType::Random => 0xa5,
        }
    }
}

/// Erase mode that can be used to clear the SVC_Exchange.
///
/// There are two types of erase mode:
/// - UserErase, leaving the write action to the UAPI crate, withtout kernel call
/// - KernelErase, requiring the kernel to execute the erasing.
///   This last mode ensure that the erasing is atomic while it is started.
///
/// By now, only UserErase ils supported.
#[repr(C)]
pub enum EraseMode {
    UserErase = 0x72,
    KernelErase = 0x27,
}

impl From<EraseMode> for u32 {
    fn from(emode: EraseMode) -> u32 {
        match emode {
            EraseMode::UserErase => 0x72,
            EraseMode::KernelErase => 0x27,
        }
    }
}

/// Sentry syscall return values
/// NonSense must never be returned, as it means that an
/// asynchronously updated return value.... has not been updated at all
/// This must raise a security exception. All syscalls that can't set
/// they return code synchronously (e.g. IPC), MUST use this value as
/// default one
#[repr(C)]
pub enum AlarmFlag {
    AlrmStart,
    AlrmStartPeriodic,
    AlrmStop,
}

impl From<AlarmFlag> for u32 {
    fn from(mode: AlarmFlag) -> u32 {
        match mode {
            AlarmFlag::AlrmStart => 0,
            AlarmFlag::AlrmStartPeriodic => 1,
            AlarmFlag::AlrmStop => 2,
        }
    }
}

#[repr(C)]
pub enum SHMPermission {
    /// allows target process to map the SHM. No read nor write though
    Map,

    /// allows target process to read the mapped SHM. Requires MAP
    Read,

    /// allows target process to write shared memory. Requires MAP
    Write,

    /// allows target process to transfer SHM to another, pre-allowed, process
    Transfer,
}

impl From<SHMPermission> for u32 {
    fn from(shm_perm: SHMPermission) -> u32 {
        match shm_perm {
            SHMPermission::Map => 0x1,
            SHMPermission::Read => 0x2,
            SHMPermission::Write => 0x4,
            SHMPermission::Transfer => 0x8,
        }
    }
}

/// Events tasks can listen on
#[repr(C)]
pub enum Signal {
    /// Abort signal
    Abort = 1,

    /// Timer (from alarm)
    Alarm,

    /// Bus error (bad memory access, memory required)
    Bus,

    /// Continue if previously stopped
    Cont,

    /// Illegal instruction. Can be also used for upper provtocols
    Ill,

    /// I/O now ready
    Io,

    /// Broken pipe
    Pipe,

    /// Event pollable
    Poll,

    /// Termination signal
    Term,

    /// Trace/bp signal (debug usage only)
    Trap,

    /// 1st user-defined signal
    Usr1,

    /// 2nd user-defined signal
    Usr2,

    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    PanicUserHardFault,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    PanicKernelHardFault,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    PanicUserBusFault,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    PanicKernelBusFault,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    PanicUserUsageFault,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    PanicKernelUsageFault,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    PanicUserMemAccess,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    PanicKernelMemAccess,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    PanicKernelInvalidUsespaceInput,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    PanicKernelShorterKBuffersConfig,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    PanicKernelInvalidManagerState,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    PanicKernelInvalidManagerResponse,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    PanicKernelTimeout,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    PanicKernelBadCFICalculation,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    PanicHardwareInvalidState,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    PanicHardwareUnexpectedModification,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    AutotestDone,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    AutotestFailed,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    AutotestTimedOut,
}

pub type ProcessID = u32;

#[repr(C)]
pub enum SleepDuration {
    D1ms,
    D2ms,
    D5ms,
    D10ms,
    D20ms,
    D50ms,
    ArbitraryMs(u32),
}

impl From<SleepDuration> for u32 {
    fn from(duration: SleepDuration) -> u32 {
        match duration {
            SleepDuration::D1ms => 1,
            SleepDuration::D2ms => 2,
            SleepDuration::D5ms => 5,
            SleepDuration::D10ms => 10,
            SleepDuration::D20ms => 20,
            SleepDuration::D50ms => 50,
            SleepDuration::ArbitraryMs(v) => v,
        }
    }
}

#[repr(C)]
pub enum SleepMode {
    Shallow,
    Deep,
}

impl From<SleepMode> for u32 {
    fn from(mode: SleepMode) -> u32 {
        match mode {
            SleepMode::Shallow => 0,
            SleepMode::Deep => 1,
        }
    }
}

impl TryFrom<u32> for SleepMode {
    type Error = Status;
    fn try_from(mode: u32) -> Result<SleepMode, Self::Error> {
        match mode {
            0 => Ok(SleepMode::Shallow),
            1 => Ok(SleepMode::Deep),
            _ => Err(Status::Invalid),
        }
    }
}

#[repr(C)]
pub enum CPUSleep {
    WaitForInterrupt,
    WaitForEvent,
    ForbidSleep,
    AllowSleep,
}

impl From<CPUSleep> for u32 {
    fn from(mode: CPUSleep) -> u32 {
        match mode {
            CPUSleep::WaitForInterrupt => 0,
            CPUSleep::WaitForEvent => 1,
            CPUSleep::ForbidSleep => 2,
            CPUSleep::AllowSleep => 3,
        }
    }
}

impl TryFrom<u32> for CPUSleep {
    type Error = Status;
    fn try_from(mode: u32) -> Result<CPUSleep, Self::Error> {
        match mode {
            0 => Ok(CPUSleep::WaitForInterrupt),
            1 => Ok(CPUSleep::WaitForEvent),
            2 => Ok(CPUSleep::ForbidSleep),
            3 => Ok(CPUSleep::AllowSleep),
            _ => Err(Status::Invalid),
        }
    }
}

mirror_enum! {
    u32,
    pub enum Precision {
        Cycle,
        Nanoseconds,
        Microseconds,
        Milliseconds,
    }
}

#[allow(non_camel_case_types)]
pub type devh_t = u32;
#[allow(non_camel_case_types)]
pub type taskh_t = u32;
#[allow(non_camel_case_types)]
pub type shmh_t = u32;
#[allow(non_camel_case_types)]
pub type dmah_t = u32;

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct shm_infos {
    pub handle: shmh_t,
    pub label: u32,
    pub base: usize,
    pub len: usize,
    pub perms: u32,
}

#[test]
fn test_layout_shm_infos() {
    const UNINIT: ::std::mem::MaybeUninit<shm_infos> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<shm_infos>(),
        32usize,
        concat!("Size of: ", stringify!(shm_infos))
    );
    assert_eq!(
        ::std::mem::align_of::<shm_infos>(),
        8usize,
        concat!("Alignment of ", stringify!(shm_infos))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).handle) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(shm_infos),
            "::",
            stringify!(handle)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).label) as usize - ptr as usize },
        4usize,
        concat!(
            "Offset of field: ",
            stringify!(shm_infos),
            "::",
            stringify!(label)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).base) as usize - ptr as usize },
        8usize,
        concat!(
            "Offset of field: ",
            stringify!(shm_infos),
            "::",
            stringify!(base)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).len) as usize - ptr as usize },
        16usize,
        concat!(
            "Offset of field: ",
            stringify!(shm_infos),
            "::",
            stringify!(len)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).perms) as usize - ptr as usize },
        24usize,
        concat!(
            "Offset of field: ",
            stringify!(shm_infos),
            "::",
            stringify!(perms)
        )
    );
}
