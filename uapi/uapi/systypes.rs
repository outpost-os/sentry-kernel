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
    /// Successful result, the kernel has terminated its task with no error
    Ok,
    /// At least one parameter is not valid (not allowed or not found)
    Invalid,
    /// The requested action is not allowed for caller, or the resource is not owned
    Denied,
    /// The requested resource do not exist
    NoEntity,
    /// The requested resource is in a state that do now allow the current call
    Busy,
    /// The requested resource is already mapped
    AlreadyMapped,
    /// Critical (mostly security-related) unexpected event
    Critical,
    /// The requested resource did not respond or the call has reached its maximum wait time
    Timeout,
    /// The requested resource is not here yet, come back later
    Again,
    /// The call has been interrupted sooner than expected. Used for blocking calls
    Intr,
    /// The requested resource can't be manipulated without generating a dead lock
    Deadlk,
}

/// u32 to Status converter, required to support register encoded value
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
/// in the source code in order to identify declared DMA streams.
/// This label is set in the device-tree in the stream declaration,
/// and can be used in order to get back the effective DMA stream handler from it in order
/// to manipulate it
pub type StreamLabel = u32;


/// Definition of Sentry events
///
/// Multiple events can targets a given task. These events are strictly
/// identified so that the task can easily differentiate them.
#[repr(C)]
pub enum EventType {
    /// No event
    None = 0,
    /// Inter-task slow path IPC event
    Ipc = 1,
    /// Inter-task signal event
    Signal = 2,
    /// Hardware interrupt event
    Irq = 4,
    /// DMA stream event
    Dma = 8,
    All = 15,
}

/// Event Type to register (u32) converter
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
/// TODO: to be moved to svc_exchange module as used exclusively by
/// this module primitives.
///
/// There are two types of erase model:
/// - Zeroify, that write 0x0 pattern in the SVC exchange zone
/// - Random, that write a random pattern
///
/// By now, only Zeroify is supported.
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

/// Alarm type for alarm-related API
#[repr(C)]
pub enum AlarmFlag {
    /// Start an alarm
    AlrmStart,
    /// Start a periodic alarm
    AlrmStartPeriodic,
    /// Stop an alarm, being periodic or not
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

/// Permission model definition for shared memories
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

/// Converter for SHM permission to register encoding (u32)
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

/// Sentry signals definition. Most of them are aligned on standard POSIX signals
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
    /// Autotest-specific: User hardfault detected
    PanicUserHardFault,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: A panic() has been reached in kernel handler
    PanicKernelHardFault,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: User bus fault detected
    PanicUserBusFault,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Kernel bus fault detected
    PanicKernelBusFault,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: User user usage fault detected
    PanicUserUsageFault,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Kernel usage fault detected
    PanicKernelUsageFault,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: User memory fault detected
    PanicUserMemAccess,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Kernel memoryfault detected
    PanicKernelMemAccess,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Invalid userspace input received
    PanicKernelInvalidUserspaceInput,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Memory limit reached in a kernel buffer
    PanicKernelShorterKBuffersConfig,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: A given manager returns invalid state error
    PanicKernelInvalidManagerState,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: A given manager return an invalid response
    PanicKernelInvalidManagerResponse,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Kernel handler as reach timeout limit
    PanicKernelTimeout,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Kernel CFI violation
    PanicKernelBadCFICalculation,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Kernel-related hardware IP (MPU, etc.) is in invalid state
    PanicHardwareInvalidState,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: An unexpected modification of a kernel context has been detected
    PanicHardwareUnexpectedModification,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Requested kernel autotest has finished successfully
    AutotestDone,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Requested kernel autotest has finished with a failure
    AutotestFailed,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Requested kernel autotest has timed-out
    AutotestTimedOut,
}

/// Sleep durations input values for the sleep API
#[repr(C)]
pub enum SleepDuration {
    /// Sleep for 1ms
    D1ms,
    /// Sleep for 2ms
    D2ms,
    /// Sleep for 5ms
    D5ms,
    /// Sleep for 10ms
    D10ms,
    /// Sleep for 20ms
    D20ms,
    /// Sleep for 50ms
    D50ms,
    /// Sleep for a user-specificed number of ms (>0)
    ArbitraryMs(u32),
}

/// Converter for SleepDuration type to register-encoded value
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

/// Sleep mode requested
#[repr(C)]
pub enum SleepMode {
    /// Sleep in shallow mode. External events awake the job
    Shallow,
    /// Sleep in deep mode. No sleep interruption
    Deep,
}

/// Converter for SleepMode type to register-encoded value
impl From<SleepMode> for u32 {
    fn from(mode: SleepMode) -> u32 {
        match mode {
            SleepMode::Shallow => 0,
            SleepMode::Deep => 1,
        }
    }
}

/// Converter from register-encoded or C FFI defined value to SleepMode
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

/// Low power configuration support, defining the CPU sleep state exit event
///
/// There are multiple HW events that may terminate a low-power hardware cycle.
/// These are separated in two main families:
///
/// - Interrupt event (external interrupt)
/// - external event (not interrupt related)
///
/// Moreover, there is some time when the CPU must NOT enter sleep mode for a
/// given amount of time. This can be set with this CPUSleep configuration state.
///
/// > **FIXME**: the sleep trigger and the sleep constraints shoud be defined in separated
/// > types and calls.
#[repr(C)]
pub enum CPUSleep {
    /// Enter sleep mode and wait for external interrupt
    WaitForInterrupt,
    /// Enter sleep mode and wait for external event
    WaitForEvent,
    /// Disable any enter to the low power mode
    ForbidSleep,
    /// Re-enable low power
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


// TODO: using CamelCase instead, as independant of C Snake Case definitions
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
