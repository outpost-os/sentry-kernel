# Sentry kernel implementation

## Current project state

![Build-n-test](https://git.orange.ledgerlabs.net/outpost/sentry-kernel/actions/workflows/build.yml/badge.svg)
![Quality](https://git.orange.ledgerlabs.net/outpost/sentry-kernel/actions/workflows/codequal.yml/badge.svg)

[![Quality Gate Status](https://sonarqube.orange.ledgerlabs.net/api/project_badges/measure?branch=main&project=sentry-kernel&metric=alert_status&token=cb81b19de8549e9c2701899ecba06d9526bf5513)](https://sonarqube.orange.ledgerlabs.net/dashboard?id=sentry-kernel&branch=main)
[![Reliability Rating](https://sonarqube.orange.ledgerlabs.net/api/project_badges/measure?branch=main&project=sentry-kernel&metric=reliability_rating&token=cb81b19de8549e9c2701899ecba06d9526bf5513)](https://sonarqube.orange.ledgerlabs.net/dashboard?id=sentry-kernel&branch=main)
[![Security Rating](https://sonarqube.orange.ledgerlabs.net/api/project_badges/measure?branch=main&project=sentry-kernel&metric=security_rating&token=cb81b19de8549e9c2701899ecba06d9526bf5513)](https://sonarqube.orange.ledgerlabs.net/dashboard?id=sentry-kernel&branch=main)
[![Technical Debt](https://sonarqube.orange.ledgerlabs.net/api/project_badges/measure?branch=main&project=sentry-kernel&metric=sqale_index&token=cb81b19de8549e9c2701899ecba06d9526bf5513)](https://sonarqube.orange.ledgerlabs.net/dashboard?id=sentry-kernel&branch=main)
[![Vulnerabilities](https://sonarqube.orange.ledgerlabs.net/api/project_badges/measure?branch=main&project=sentry-kernel&metric=vulnerabilities&token=cb81b19de8549e9c2701899ecba06d9526bf5513)](https://sonarqube.orange.ledgerlabs.net/dashboard?id=sentry-kernel&branch=main)


## About

This is the repository of the Sentry kernel

Sentry kernel uses [The Meson Build System](https://mesonbuild.com/).

# Prerequisites

## Tools installation
Before building the project, one needs to install the build system and related tool. This project use the meson reference implementation in python. All dependencies are described in `requirements.txt`.

```console
pip3 install -r requirements.txt
```

## Cross Toolchain

This kernel aims to be fully portable. Its initial target are ARM Cortex-M MCUs (starting with STM32) and thus one needs a cross toolchain for such target. One can use any cross toolchain as long as this is a GNU compatible compiler for Cortex-M. The reference toolchain used for `CI/CD` is bundled in this project using `meson` wrap mechanism.

### Project bootstrap

A common good practice is `do not inject environment variable for build configuration`. For this purpose, `meson` does not allow using relative path in toolchain definition. Toolchain path **_must_** be absolute.

One needs to deliver to the `meson` build system the kernel configuration based on Kconfig. This can be done with
kconfiglib that is listed in `requirements.txt. The kernel configuration is generated into a local `.config` file that
holds the complete kernel configuration, and that is used at build time to select the corresponding sources and features.

#### Using defconfigs

defconfig files are stored in configs/ directory and can be used directly. In that case, the kconfig:config option can be used at setup time:

```console
meson setup -Dkconfig:config=configs/stm32f4_debug_defconfig [...]
```

#### Setting custom configurations

Generating the configuration is made using the standard Linux Kconfig UI. This interface can be called by ninja by targetting the kconfig module's menuconfig target:
```console
ninja -C builddir kconfig@@menuconfig
```

# How to build

## meson setup
The first step in meson build is project setup, this will create a specific build directory for the given options. This step also configures the toolchain to use.
Some cross-files describing toolchain configuration are set in `support/meson` directory. More than one cross file can be used if needed.

```console
meson setup [-Doption ...] --cross-file=</path/to/cross/file> <builddir>
```

## build

The build step is as simple as calling ninja.
```console
ninja -C builddir
```

## proof

Sentry kernel proof is supported by Frama-C framework. It is based on the
analysis of the libsentry sources, which include all the kernel drivers,
services, etc. except the kernel entrypoint.

**INFO**: the Frama-C framework used is Cobalt (27), with why3 and cvc4. Meson check that they are installed on the system.

Frama-C targetts are hosted in the `proof` directory and are activable using
the `with_proof` option:

```console
meson setup -Dwith_proof=true [...]
```

It can be directly used with the cross configuration, as frama-C only preprocess the sources and then natively parse the C code into its own AST
in order to analyse the source correctness.

FramaC execution is controled through the meson test framework (see tests chapter) and thus is directly accessible through the test command.
All Frama-C tests are a part of the same suite denoted proof. If both proofs and tests are enabled in the very same time, the proof tests can
then be called separatelly by calling only the proof suite.

FramaC tests can be listed using:

```console
$ meson test -C builddir_framac/ --list
frama-C-parsing
frama-C-eva
frama-C-wp-bsp-exti
frama-C-wp-bsp-pwr
frama-C-wp-bsp-rcc
frama-C-wp-bsp-rng
[...]
```

EVA and WP targets generate `.eva` and `.wp` files in the corresponding test build directory that can then be opened with `ivette` and the Frama-C GUI for analysis.
In the same time, red-alarms file holding detected RTE are also stored for each test.

## tests

Sentry kernel supports unit testing. This is done using the gtest framework.
Analysis of various components of the Sentry kernel is made by emulating, for each subcomponent, the ecosystem it needs in order to simulate the target.
For e.g., the EXTI driver is unit-tested using an emulated EXTI device mapped at the very same memory address map as the effective device, so that the device driver do not need any modifiacations while tested.

Other non-HW related components are tested for their expected behavior, in multiple nominal and borderline cases.

Enabling the test suite is made by activating the tests at setup time:

```console
meson setup -Dwith_tests=true [...]
```

The test framework is based on multiple test suites. The suite names can be listed using the standard `meson test` target:

```console
meson test -C <builddir> --list
sentry-kernel:ut-utils / io
sentry-kernel:ut-utils / bits
sentry-kernel:ut-bsp / exti
```

Each test suite (or even test) can be executed independently if needed:

```console
meson test -C <builddir> --suite ut-utils
[...]
```

## doc
TBD
