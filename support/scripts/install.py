#! /usr/bin/env python3

import os
import shlex
import shutil
import sys
from pathlib import Path
from subprocess import run

prefix = os.getenv("MESON_INSTALL_DESTDIR_PREFIX")
src = sys.argv[1]
destdir = os.path.join(prefix, sys.argv[2])

os.makedirs(destdir, exist_ok=True)
shutil.copyfile(src, os.path.join(destdir, Path(src).name))