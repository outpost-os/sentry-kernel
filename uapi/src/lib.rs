// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

//! [![github]](https://github.com/outpost-os/sentry-kernel)&ensp;
//!
//! [github]: https://img.shields.io/badge/github-8da0cb?style=for-the-badge&labelColor=555555&logo=github
//!
//! <br>
//!
//! sentry_uapi is the user API library that delivers a full access to the Sentry kernel
//! interface.
//! This crate aim to be used by any Outpost-OS Rust application.
//!
//! -**Data types** — Sentry_uapi provices a complete set of data types and
//!  values that are required in order to properly exchange informations with the Sentry kernel.
//!  All the data types are stored in the [`mod@systypes`] public module.
//!
//! -**Sentry syscalls** — Syscall are defined in a two layers way. The bare syscalls
//!  are implemented in the [`mod@syscall`] module, while the upper, easy interface
//!  is implemented in the [`mod@uapi`] module. Unless specific needs, there is no
//!  usual case where the [`mod@syscall`] module interface needs to be acceded directly.

#![cfg_attr(not(feature = "std"), no_std)]

#[macro_use]
mod arch;


/// Sentry SVC_EXCHANGE area manipulation primitives
///
/// # Usage
///
/// This module should not be used directly unless the [`mod@syscall`] module
/// interface is used. Sentry kernel interactions should be, instead, made with
/// the [`mod@uapi`] upper interface.
///
/// As the SVC_EXCHANGE area is a special userspace/kernelspace fixed size area
/// made in order to exchange data between userspace and kernelspace without
/// manpulating any pointer, this space has a particular meaning and usage, holding
/// any type of content as a 'retention area' before and after system calls.
///
/// > **NOTE**: svc exchange manipulation is unsafe
///
pub mod svc_exchange;

/// Sentry kernel low level syscall implementation
///
/// # Usage
///
/// This module is responsible for calling the kernel gate through the target
/// architecture supervisor access opcode, in interaction with the corresponding
/// arch backend.
///
/// There is no abstraction at this module's level and should not be used directly.
/// The [`mod@uapi`] module should be used instead.
///
/// > **NOTE**: This module may not be kept public forever
///
pub mod syscall;

/// Sentry kernel user API
///
/// # Usage
///
/// This module is the main entrypoint of all Sentry kernel calls.
/// It is made in order to simplify the usage of the effective kernel syscall gate
/// by automatically manipulate the exchange area in both ways, when syscalls
/// needs non-scalar inputs or instead returns data.
///
/// As a consequence, except for very specific needs, this is the lonely module
/// that should be used when using the Sentry UAPI.
///
pub mod uapi;

/// Sentry kernelspace/userspace shared types and values
///
/// # Usage
///
/// This module holds all the Sentry kernel types and values required by all other modules
/// but also types that need to be used by upper layers in order to properly manipulate
/// Sentry's syscalls.
///
/// This module do not hold any function nor macro, but only all scalar and non-scalar
/// types for userspace/Sentry-kernel exchanges.
///
/// Some types are snake case based because of the C export. None the less,
/// they will be moved to standard Rust Caml case to stay conform to the
/// Rust guildelines
///
/// > **Note**: there is no bindgen nor cbindgen call in order to ensure FFI
/// > interface with the C language, to avoid any inter-languages naming and
/// > complexity (macros cases, static inline case and so on), meaning that
/// > the corresponding C types are defined in a dedicated include dir
///
pub mod systypes;

#[cfg(not(feature = "std"))]
mod panic;
