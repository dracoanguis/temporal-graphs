#!/usr/bin/env bash
# Recreate vendor/verso-blueprint: upstream verso-blueprint v4.35.0 plus our port to the Lean 4.36
# core APIs (patches/verso-blueprint-v4.35.0-lean-4.36.patch). Temporary, until upstream publishes
# a v4.36 release line; then `lakefile.lean` requires it from git again and this script goes away.
# Run from anywhere; idempotent (does nothing if the patched checkout is already there).
set -euo pipefail

here="$(cd "$(dirname "$0")/.." && pwd)"
dest="$here/vendor/verso-blueprint"
rev="4943d3335ffa9221a39949e60836a8ad5dc2a456" # tag v4.35.0
patch="$here/patches/verso-blueprint-v4.35.0-lean-4.36.patch"

if [ -d "$dest/.git" ]; then
  echo "vendor/verso-blueprint already present; remove it to recreate it."
  exit 0
fi

mkdir -p "$here/vendor"
git clone --quiet https://github.com/leanprover/verso-blueprint.git "$dest"
git -C "$dest" checkout --quiet --detach "$rev"
git -C "$dest" apply "$patch"
echo "vendor/verso-blueprint ready (v4.35.0 + Lean 4.36 patch)."
