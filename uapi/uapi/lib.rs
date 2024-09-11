// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#![cfg_attr(not(feature = "std"), no_std)]
#![feature(asm_const)]

#[macro_use]
mod arch;

pub mod svc_exchange;
pub mod syscall;
pub mod uapi;
pub mod systypes;

#[cfg(not(feature = "std"))]
mod panic;
