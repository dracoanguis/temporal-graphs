/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import Lean

/-!
# Blueprint declaration check, restricted to the library

`leanblueprint checkdecls` runs `lake exe checkdecls`, which imports every library of the
package together. The Palomar files `Challenge` and `Solution` define the same names (as
Comparator requires), so that joint import fails on the duplicates. This script checks
the declarations listed by the blueprint against the `TemporalGraph` library alone.

Usage, from the repository root, after `leanblueprint web`:
`lake env lean --run scripts/CheckDecls.lean blueprint/lean_decls`
-/

public section

open Lean

/-- Check that every declaration named in the file `args[0]` exists in `TemporalGraph`. -/
unsafe def main (args : List String) : IO UInt32 := do
  let [file] := args
    | IO.eprintln "usage: lake env lean --run scripts/CheckDecls.lean <declaration list>"
      return 1
  unless ← System.FilePath.pathExists file do
    IO.eprintln s!"Could not find declaration list {file}."
    return 1
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `TemporalGraph }] {}
  let mut ok := true
  let mut count := 0
  for line in ← IO.FS.lines file do
    if line.isEmpty then continue
    count := count + 1
    unless env.contains line.toName do
      IO.println s!"{line} is missing."
      ok := false
  IO.println s!"{count} declarations checked."
  return if ok then 0 else 1
