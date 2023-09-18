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

Generating the configuration is made using the standard Linux Kconfig UI:
```console
menuconfig Kconfig
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

## tests
TBD
## doc
TBD
## proof
TBD
