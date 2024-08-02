from conan import ConanFile
from conan.tools.meson import MesonToolchain, Meson
from conan.tools.gnu import PkgConfigDeps


class sentry_kernelConan(ConanFile):
    name = "sentry-kernel"
    version = "0.3"
    channel = "testing"
    package_type = "application"
    description = """This is the package of the Sentry kernel.
                    A fully featured micro-kernel for small embedded systems, designed
                    for the Outpost Operating System"""
    License = "Apache-2.0"
    topics = ("kernel", "embedded", "Outpost", "security")
    url = "https://github.com/outpost-os/sentry-kernel.git"
    tools_requires = ""
    build_requires = "ninja/>1.11", "dtc/[>1.6]", "cargo/[>1.75]"
    test_requires = "gcovr", "frama-c"
    python_requires = "meson/[>1.3 <1.5]", "dts-utils/[>0.2.2]", "svd2json/[>0.1.6]", "kconfiglib/[>14.1]"

    # Binary configuration
    settings = "os", "baremetal", "arch", "armv7", "compiler", "gcc"

    exports = "dts/*", "configs/*", "schemas/*", "subprojects/*"
    # Sources are located in the same place as this recipe, copy them to the recipe
    exports_sources = "meson.build", "meson.options", "kernel/*", "uapi/*", "autotest/*", "idle/*", "doc/*", "tools/*"
    package_type = "unknown"


    def layout(self):
        self.folders.build = "build"

    def generate(self):
        deps = PkgConfigDeps(self)
        deps.generate()
        tc = MesonToolchain(self)
        tc.generate()

    def build(self):
        meson = Meson(self)
        meson.configure(c)
        meson.build()

    def package(self):
        meson = Meson(self)
        meson.install()
