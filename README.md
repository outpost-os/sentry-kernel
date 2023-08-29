# Sentry kernel implementation

## Current project state

![Build-n-test](https://git.orange.ledgerlabs.net/outpost/sentry-kernel/actions/workflows/build.yml/badge.svg)
![Quality](https://git.orange.ledgerlabs.net/outpost/sentry-kernel/actions/workflows/codequal.yml/badge.svg)

[![Quality Gate Status](https://sonarqube.orange.ledgerlabs.net/api/project_badges/measure?project=sentry-kernel&metric=alert_status&token=3fb69c3f1ffc9ea920e1cc7a6ea03045416f113f)](https://sonarqube.orange.ledgerlabs.net/dashboard?id=sentry-kernel&branch=main)
[![Reliability Rating](https://sonarqube.orange.ledgerlabs.net/api/project_badges/measure?project=sentry-kernel&metric=reliability_rating&token=3fb69c3f1ffc9ea920e1cc7a6ea03045416f113f)](https://sonarqube.orange.ledgerlabs.net/dashboard?id=sentry-kernel&branch=main)
[![Security Rating](https://sonarqube.orange.ledgerlabs.net/api/project_badges/measure?project=sentry-kernel&metric=security_rating&token=3fb69c3f1ffc9ea920e1cc7a6ea03045416f113f)](https://sonarqube.orange.ledgerlabs.net/dashboard?id=sentry-kernel&branch=main)
[![Vulnerabilities](https://sonarqube.orange.ledgerlabs.net/api/project_badges/measure?project=sentry-kernel&metric=vulnerabilities&token=3fb69c3f1ffc9ea920e1cc7a6ea03045416f113f)](https://sonarqube.orange.ledgerlabs.net/dashboard?id=sentry-kernel&branch=main)


## About

This is the repository of the Sentry kernel

Sentry kernel use [The Meson Build Sytem](https://mesonbuild.com/).

# Prerequisits

## Tools installation
Before building the project, one needs to install the build system and related tool. This project use the meson reference implementation in python. All dependencies are described in `requirements.txt`.

```console
pip3 install -r requirements.txt
```

## Cross Toolchain

This kernel aim to be fully portable. Its inital target are ARM Cortex-M MCUs (starting with STM32) and thus one needs a cross toolchain for such target. One can use any cross toolchain as long as this is a gnu compatible compiler for Cortex-M. The reference toolchain used for `CI/CD` is bundle in this project using `meson` wrap mechanism.

### Project bootstrap


A common good practice is `do not inject environment variable for build configuration`. For this purpose, `meson` does not allow to use relative path in toolchain definition. Toolchain path **_must_** be absolute.


One needs to deliver to the `meson` build system the kernel configuration based on Kconfig. This can be done with
kconfiglib that is listed in `requirements.txt. The kernel configuration is generated into a local `.config` file that
hold the complete kernel configuration, and that is used at build time to select the corresponding sources and features.

Generating the configuration is made using the standard Linux Kconfig UI:
```console
menuconfig Kconfig
```

# How to build

## meson setup
The first step in meson build is project setup, this will create a specific build directory for the given options. This step is also configuring the toolchain to use.
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
TDB
## doc
TDB
## proof
TDB
