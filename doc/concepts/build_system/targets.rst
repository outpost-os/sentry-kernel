Basics and targets
------------------

Dependencies
""""""""""""

Sentry build system is based on Meson, but also needs some external python tooling.
The meson build system automatically check that all python modules are installed on
the build system, but in order to simplify the setup phase, a `requirements.txt` file
has been added to the kernel root source path.

As a consequence, before building the project, one needs to install meson, and then
all python dependencies are described in `requirements.txt`.

.. code-block:: shell

  pip3 install -r requirements.txt


Cross-compilation concept
"""""""""""""""""""""""""

As the cross-toolchain installation and configuration is not a build-system related
content but a build-host related information, the `meson` build systems is using
cross-files to define the current build host toolchain configuration that need to
be used for the project.

A typical cross-file defines all the toolchain binaries to use and would look
like the following:

.. code-block::
    :linenos:

    [constants]
    cross_triple = 'arm-none-eabi'
    cross_toolchain = '/opt/arm-none-eabi/'
    cross_compile = cross_toolchain + 'bin/' + cross_triple + '-'

    [host_machine]
    system = 'baremetal'
    cpu_family = 'arm'
    cpu = 'cortex-m4'
    endian = 'little'
    exe_wrapper = 'qemu-arm-static'

    [binaries]
    c = cross_compile + 'gcc'
    cpp = cross_compile + 'g++'
    ar = cross_compile + 'gcc-ar'
    ranlib = cross_compile + 'gcc-ranlib'
    strip = cross_compile + 'strip'
    objcopy = cross_compile + 'objcopy'
    clang = 'clang'
    rust_ld = cross_compile + 'gcc'
    rust = ['rustc', '--target', 'thumbv7m-none-eabi']


.. note::
    A repository hosting various cross-files, denoted `meson-cross-files`, exists
    in the Outpost organisation. Although, anyone can write its own toolchain for
    its own host, like, for e.g. on Windows build environment:

.. code-block::
    :linenos:

    [constants]
    cross_triple = 'arm-none-eabi'
    sysroot = 'c:/program files (x86)/arm gnu toolchain arm-none-eabi/12.2 rel1/arm-none-eabi'

    [host_machine]
    system = 'baremetal'
    cpu_family = 'arm'
    endian = 'little'
    cpu = 'cortex-m4'

    [binaries]
    c = cross_triple + '-gcc'
    cpp = cross_triple + '-g++'
    ar = cross_triple + '-gcc-ar'
    ranlib = cross_triple + '-gcc-ranlib'
    strip = cross_triple + '-strip'
    objcopy = cross_triple + '-objcopy'
    clang = 'clang'
    rust_ld = cross_triple + '-gcc'
    rust = ['rustc', '--target', 'thumbv7m-none-eabi']

    [properties]
    bindgen_clang_arguments = [ '--sysroot=' + sysroot, '--target=' + cross_triple ]


Bootstraping Sentry build
"""""""""""""""""""""""""

A common good practice is `do not inject environment variable for build configuration`. For this purpose, `meson` does
not allow using relative path in toolchain definition. Toolchain path **_must_** be absolute.

One needs to deliver to the `meson` build system the kernel configuration based on Kconfig. The configuration is forged
at project level, using, among others, the Sentry kernel `Kconfig` entry.

Although, the global project config file generation is under the project responsability, and the
Sentry kernel build system consider that this file is built when starting. This is a requirement
in order to keep the configuration phase, under Kconfig responsablity, separated from the build
phase of each project component, including the Sentry kernel itself.
As the configuration phase is handled at project level, the project configuration(s) must be
kept somewhere and passed to the kernel build system at setup time.

Modifying the configuration can be done at project level, upgrading or creating new
defconfig files, so that the Sentry kernel setup phase can get back the newly created
configuration. This part is out of this documentation though and is explained in the
project generator documentation.

Here are all the Sentry kernel custom command line options:

   * `kconfig:config`: *string*: declare a project defconfig file that can be used by the Kernel as input
   * `with_docs`: *boolean*: activate doc build targets
   * `with_proof`: *boolean*: activate formal proof build and exec targets
   * `with_tests`: *boolean*: activate gtest unit test framework build and exec

All options can be passed using the widely used `-Doption=value` argument passing. See
meson build system manual to see all possible options that can be transmitted.

Building Sentry
"""""""""""""""

Sentry build is decomposed into two main components:

    * `libsentry.a`, a static containing all the Sentry components but the entrypoint and the ldscript. This lib
      is composed of:

       * libsysgate, a static library of the Rust implementation of the syscalls
       * Sentry static C sources
       * Sentry generated sources (from SVD and DTS files)
       * Sentry generated headers (from SVD and DTS files)

      libsentry sources list varies depending on the passed configuration, as all arch-dependant and SoC-dependant
      sources (such as drivers) are dynamically selected by the build system based on the current project configuration,
      namely the current SoC name, familly, subfamilly, and the current selected features-set (e.g. debug or release).

    * `sentry-kernel.elf`, kernel executable, including libsentry, the entrypoint, linked using the Sentry ldscript

When setuping the project, the build system shows the current Sentry project configuration state:

.. code-block:: shell

    $ meson setup -Dkconfig:config=configs/stm32f429i_disc1_defconfig -Dwith_doc=true --cross-file /workspace/arm-none-eabi-gcc.ini builddir
    The Meson build system
    Version: 1.2.2
    Source dir: /workspace/sentry-kernel/sentry-kernel
    Build dir: /workspace/sentry-kernel/builddir
    Build type: cross build
    Project name: sentry-kernel
    Project version: undefined
    C compiler for the host machine: /opt/arm-none-eabi/bin/arm-none-eabi-gcc (gcc 12.2.1 "arm-none-eabi-gcc (Arm GNU Toolchain 12.2.Rel1 (Build arm-12.24)) 12.2.1 20221205")
    C linker for the host machine: /opt/arm-none-eabi/bin/arm-none-eabi-gcc ld.bfd 12.2
    C++ compiler for the host machine: /opt/arm-none-eabi/bin/arm-none-eabi-g++ (gcc 12.2.1 "arm-none-eabi-g++ (Arm GNU Toolchain 12.2.Rel1 (Build arm-12.24)) 12.2.1 20221205")
    C++ linker for the host machine: /opt/arm-none-eabi/bin/arm-none-eabi-g++ ld.bfd 12.2
    C compiler for the build machine: cc (gcc 11.4.0 "cc (Ubuntu 11.4.0-1ubuntu1~22.04) 11.4.0")
    C linker for the build machine: cc ld.bfd 2.38
    C++ compiler for the build machine: c++ (gcc 11.4.0 "c++ (Ubuntu 11.4.0-1ubuntu1~22.04) 11.4.0")
    C++ linker for the build machine: c++ ld.bfd 2.38
    Build machine cpu family: x86_64
    Build machine cpu: x86_64
    Host machine cpu family: arm
    Host machine cpu: cortex-m4
    Target machine cpu family: arm
    Target machine cpu: cortex-m4
    Program objcopy found: YES
    Program python3 (dunamai) found: YES (/bin/python3) modules: dunamai
    [...]
    Message: build targetting SoC STM32F429
    ../meson.build:200: WARNING: !!! This is NOT a release build ! DO NOT USE IT IN PRODUCTION !!!
    Build targets in project: 33

    sentry-kernel undefined

    Configuration
        soc           : stm32f429
        dts           : dts/sentry_stm32f429i_disc1.dts

    Subprojects
        cmsis         : YES
        devicetree    : YES
        kconfig       : YES
        meson-svd     : YES

    User defined options
        Cross files   : /workspace/arm-none-eabi-gcc.ini
        with_doc      : true
        kconfig:config: configs/stm32f429i_disc1_defconfig


Building the Sentry kernel is as easy as calling Ninja:

.. code-block:: shell

    ninja -C builddir all



Sentry unit-testing
"""""""""""""""""""

Sentry kernel unit testing is using the Gtest framework. All unit tests are executed as
x86_64 userspace code, meaning that all Sentry code blocks that are executed under test
are compiled and executed as x86_64 code.

Even if the Sentry kernel is built for embedded, it is not, even for drivers testing,
a problem to execute unit testsing in order to validate C-level (or Rust level)
behavior analysis.
The global model is that any peace of code in Sentry can be extracted, compiled for
x86_64, and linked to a test source that implement the potential missing blocs and
validate the behavior of the code under test in various cases.

To do that, the gtest framework delivers multiple useful components such as
mocks, to trigger execution of test fixtures when the source code calls external
symbols. In the same time, the usage of C++ allows templated testing, that
permit to forge a great amount of inputs and stimulii to various Sentry modules.

The Sentry tests suites are natively integrated into meson and are the following:

   * ut-managers: test suite targetting managers
   * ut-bsp: test suite targetting drivers
   * ut-utils: test suite targetting generic kernel utilities and core library


The Sentry test support is integrated into the build system, and associated to the
Sentry static analyser to ensure coverage metrics.

Calling only a given test suite is then supported through:

.. code-block:: shell

    meson test -C builddir --suite ut-utils

Executing the test suite generates test report. SonarQube XML test report
can be generated for SonarQube input.

A typical test execution is the following:

.. code-block:: shell

    meson test -C builddir
    [...]
    [61/62] Running all tests.
    1/5 sentry-kernel:ut-utils / io               OK              0.03s
    2/5 sentry-kernel:ut-utils / bits             OK              0.02s
    3/5 sentry-kernel:ut-bsp / exti               OK              0.01s
    4/5 sentry-kernel:ut-managers / printk        OK              0.01s
    5/5 sentry-kernel:ut-managers / task          OK              0.01s

    Ok:                 5
    Expected Fail:      0
    Fail:               0
    Unexpected Pass:    0
    Skipped:            0
    Timeout:            0
