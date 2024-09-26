import os
import json
import subprocess
from conan import ConanFile
from conan.tools.files import copy


class Sentryecipe(ConanFile):
    name = "sentry-kernel"
    relpath = "builddir/staging"
    settings = "arch", "os"

    def init(self):
        proc = subprocess.run(["meson", "introspect", "--machines", "builddir"], check=True, capture_output=True, text=True)
        result = json.loads(proc.stdout)
        self.arch = result["host"]["cpu_family"]
        self.os = result["host"]["system"]

    def set_version(self):
        proc = subprocess.run(["meson", "introspect", "--projectinfo", "builddir"], check=True, capture_output=True, text=True)
        result = json.loads(proc.stdout)
        self.version = result["version"]

    def layout(self):
        self.folders.build = os.path.join(self.relpath)
        self.folders.source = self.folders.build
        self.cpp.source.includedirs = ["usr/local/include"]
        self.cpp.build.libdirs = ["usr/local/lib"]
        self.cpp_info.bindirs = ['usr/local/bin']
        self.cpp_info.resdirs = ['usr/local/share']

    def package(self):
        local_include_folder = os.path.join(self.source_folder, self.cpp.source.includedirs[0])
        local_lib_folder = os.path.join(self.build_folder, self.cpp.build.libdirs[0])
        copy(self, "*.h", local_include_folder, os.path.join(self.package_folder, "include"), keep_path=False)
        copy(self, "*.lib", local_lib_folder, os.path.join(self.package_folder, "lib"), keep_path=False)
        copy(self, "*.elf", local_lib_folder, os.path.join(self.package_folder, "bin"), keep_path=False)
        copy(self, "*.hex", local_lib_folder, os.path.join(self.package_folder, "hex"), keep_path=False)

    def package_info(self):
        self.cpp_info.libs = ["uapi"]
        self.cpp_info.components["uapi"].libs = "libuapi"
        self.cpp_info.components["firmware"].filenames = "*.hex"
        self.cpp_info.components["binaries"].filenames = "*.elf"
