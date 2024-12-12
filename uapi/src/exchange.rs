// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

use core::ptr::{addr_of_mut,addr_of};
use crate::systypes::shm::ShmInfo;
use crate::systypes::Status;

const EXCHANGE_AREA_LEN: usize = 128; // TODO: replace by CONFIG-defined value


/// The effective kernelspace/userspace exchange zone, set in a dedicated section
///
#[unsafe(link_section = ".svcexchange")]
static mut EXCHANGE_AREA: [u8; EXCHANGE_AREA_LEN] = [0u8; EXCHANGE_AREA_LEN];

/// public trait of kernel-user exchangeable objects
///
/// This trait is public at the crate-internal level in order to support
/// ffi_c copy_to_user/copy_from_user implementation.
/// Although, this very module is kept private, so that the crate external
/// API do not deliver such a trait specification.
/// This allows to ensure that only sentry-uapi local types are exchangeable
/// with the Sentry kernel.
pub trait SentryExchangeable {
    fn to_kernel(&self) -> Result<Status,Status>;
    fn from_kernel(&mut self) -> Result<Status, Status>;
}


/// SentryExchangeable trait implementation for ShmInfo.
/// Shminfo is a typical structure which is returned by the kernel to the
/// userspace in order to delivers various SHM-related information to a given
/// task that is using the corresponding SHM.
///
/// In test mode only, this structure can be written back to the Exchange Area.
/// In production mode, the application can't write such a content to the exchange
/// as the kernel as strictly no use of it.
///
impl SentryExchangeable for crate::systypes::shm::ShmInfo {
    #[allow(static_mut_refs)]
    fn from_kernel(&mut self) -> Result<Status, Status> {
        unsafe {
            core::ptr::copy_nonoverlapping(
                EXCHANGE_AREA.as_ptr(),
                addr_of_mut!(*self) as *mut u8,
                core::mem::size_of::<ShmInfo>().min(EXCHANGE_AREA_LEN),
            );
        }
        Ok(Status::Ok)
    }

    #[cfg(test)]
    #[allow(static_mut_refs)]
    fn to_kernel(&self) -> Result<Status,Status> {
        unsafe {
            core::ptr::copy_nonoverlapping(
                addr_of!(*self) as *const u8,
                EXCHANGE_AREA.as_mut_ptr(),
                core::mem::size_of::<ShmInfo>().min(EXCHANGE_AREA_LEN),
            );
        }
        Ok(Status::Ok)
    }

    #[cfg(not(test))]
    #[allow(static_mut_refs)]
    fn to_kernel(&self) -> Result<Status,Status> {
        Err(Status::Invalid)
    }
}

impl SentryExchangeable for *mut u8 {
    #[allow(static_mut_refs)]
    fn from_kernel(&mut self) -> Result<Status, Status> {
        unsafe {
            core::ptr::copy_nonoverlapping(
                EXCHANGE_AREA.as_ptr(),
                addr_of_mut!(*self) as *mut u8,
                core::mem::size_of::<ShmInfo>().min(EXCHANGE_AREA_LEN),
            );
        }
        Ok(Status::Ok)
    }

    #[allow(static_mut_refs)]
    fn to_kernel(&self) -> Result<Status,Status> {
        unsafe {
            core::ptr::copy_nonoverlapping(
                addr_of!(*self) as *const u8,
                EXCHANGE_AREA.as_mut_ptr(),
                core::mem::size_of::<ShmInfo>().min(EXCHANGE_AREA_LEN),
            );
        }
        Ok(Status::Ok)
    }
}

impl SentryExchangeable for *const u8 {
    #[allow(static_mut_refs)]
    fn from_kernel(&mut self) -> Result<Status, Status> {
        Err(Status::Invalid)
    }

    #[allow(static_mut_refs)]
    fn to_kernel(&self) -> Result<Status,Status> {
        unsafe {
            core::ptr::copy_nonoverlapping(
                addr_of!(*self) as *const u8,
                EXCHANGE_AREA.as_mut_ptr(),
                core::mem::size_of::<ShmInfo>().min(EXCHANGE_AREA_LEN),
            );
        }
        Ok(Status::Ok)
    }
}


pub const fn length() -> usize {
    EXCHANGE_AREA_LEN
}

pub fn copy_to_kernel<T>(from : &T) -> Result<Status,Status>
    where T:SentryExchangeable
{
    from.to_kernel()
}

pub fn copy_from_kernel<T>(to: &mut T) -> Result<Status,Status>
where T:SentryExchangeable
{
    to.from_kernel()
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn back_to_back_shminfo() {
        let src = ShmInfo {
            handle: 2,
            label: 42,
            base: 0x123456,
            len: 64,
            perms: 0x1,
        };
        let mut dst = ShmInfo {
            handle: 0,
            label: 0,
            base: 0,
            len: 0,
            perms: 0,
        };
        let _ = src.to_kernel();
        let _ = dst.from_kernel();
        assert_eq!(src, dst);
    }
}
