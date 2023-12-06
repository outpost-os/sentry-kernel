Unit testing Sentry
-------------------

.. _unittest:

.. index::
    single: unit test; model
    single: unit test; test suites
    single: gtest; tests design

Unit testing framework
""""""""""""""""""""""

Even if the Sentry kernel is built for embedded, it is not, even for drivers testing,
a problem to execute unit testing in order to validate C-level (or Rust level)
behavior analysis.
The global test model is that any peace of code in Sentry can be extracted, compiled for
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

Building and testing modules on build host
""""""""""""""""""""""""""""""""""""""""""


Mocking externals, checking behaviors
"""""""""""""""""""""""""""""""""""""
