"""Minimal `kpsewhich` replacement for building the blueprint without a TeX distribution.

plasTeX resolves `\\input{macros/common}` and friends by calling `kpsewhich`. When that program
is missing, its fallback only matches bare file names, so any path containing a `/` is skipped
and the theorem environments declared in `macros/common.tex` never get defined. This script
looks the name up (as given, then with `.tex`) in each `TEXINPUTS` directory, which plasTeX
sets to the directory of the file being processed, and in the current directory.
"""

import os
import sys


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: kpsewhich NAME", file=sys.stderr)
        return 2
    name = sys.argv[1]
    dirs = [d for d in os.environ.get("TEXINPUTS", "").split(os.pathsep) if d] + [os.getcwd()]
    for d in dirs:
        for candidate in (name, name + ".tex"):
            path = os.path.join(d, candidate)
            if os.path.isfile(path):
                print(os.path.abspath(path))
                return 0
    return 1
