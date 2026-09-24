"""A TeX distribution (TinyTeX, with xelatex and latexmk) living inside the uv environment.

`install-tinytex` downloads a pinned TinyTeX release into `<venv>/tinytex` and installs the LaTeX
packages the blueprint's `print.tex` needs. `latexmk` runs TinyTeX's latexmk with TinyTeX's
binaries first on PATH, which is what `leanblueprint pdf` calls. Nothing is installed outside the
environment, and removing `.venv` removes TeX with it.
"""

import os
import platform
import subprocess
import sys
import tarfile
import tempfile
import urllib.request
from pathlib import Path

VERSION = "v2026.09"
RELEASES = "https://github.com/rstudio/tinytex-releases/releases/download"
ARCHIVES = {
    ("darwin", "arm64"): "darwin",
    ("darwin", "x86_64"): "darwin",
    ("linux", "x86_64"): "linux-x86_64",
    ("linux", "aarch64"): "linux-arm64",
}
# LaTeX packages used by blueprint/src/print.tex and blueprint.sty beyond TinyTeX's base set.
PACKAGES = ["latexmk", "mathtools"]

ROOT = Path(sys.prefix) / "tinytex"


def _bin_dir() -> Path:
    dirs = sorted((ROOT / "bin").glob("*"))
    if not dirs:
        sys.exit(f"TinyTeX is not installed in {ROOT}; run `install-tinytex` first.")
    return dirs[0]


def _env() -> dict:
    env = dict(os.environ)
    env["PATH"] = f"{_bin_dir()}{os.pathsep}{env.get('PATH', '')}"
    return env


def install() -> int:
    if not (ROOT / "bin").is_dir():
        key = (sys.platform, platform.machine())
        if key not in ARCHIVES:
            sys.exit(f"No TinyTeX archive for platform {key}.")
        url = f"{RELEASES}/{VERSION}/TinyTeX-1-{ARCHIVES[key]}-{VERSION}.tar.xz"
        with tempfile.TemporaryDirectory() as tmp:
            archive = Path(tmp) / "tinytex.tar.xz"
            print(f"Downloading {url}", flush=True)
            urllib.request.urlretrieve(url, archive)
            with tarfile.open(archive) as tar:
                tar.extractall(tmp, filter="tar")
            extracted = next(p for p in Path(tmp).iterdir() if p.is_dir())
            extracted.rename(ROOT)
    tlmgr = str(_bin_dir() / "tlmgr")
    subprocess.run([tlmgr, "install", *PACKAGES], env=_env(), check=True)
    return 0


def latexmk() -> int:
    exe = str(_bin_dir() / "latexmk")
    return subprocess.run([exe, *sys.argv[1:]], env=_env()).returncode
