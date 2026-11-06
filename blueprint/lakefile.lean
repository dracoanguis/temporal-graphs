/-
Separate Lake project for the Verso blueprint, so that the library itself does not depend on
Verso (same pattern as `../docbuild`). `packagesDir` shares the parent's packages: Mathlib's
build is reused, never recompiled. Keep the Verso stack on the tag of `../lean-toolchain`.

Usage, from this directory: `lake exe vbp build` (HTML in `_out/site/html-multi/`), add `--pdf`
for `_out/site/pdf/main.pdf` (needs `lualatex`), `--serve` for a local preview.
-/
import Lake
open Lake DSL

require «temporal-graph» from ".."

-- Dependencies shared with Mathlib, pinned on the revisions of `../lake-manifest.json`. Without
-- these pins Lake takes verso-blueprint's older pins and checks them out in the *shared*
-- `.lake/packages`, breaking the library's build (observed: listing the library first is not
-- enough). Update them together with the parent manifest.
require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4" @
  "16259c0d07d61ee37d999d05b5cf96338b8daa11"
require Cli from git "https://github.com/leanprover/lean4-cli" @
  "c09cb1e4f1e6e1c231a1175a12b681b075054a1b"
require plausible from git "https://github.com/leanprover-community/plausible" @
  "129d1ba9a16bc0660f46c79e9fb041ef5d5d80de"

-- verso-blueprint has no v4.36 release line yet: its v4.35.0 branch is built against the
-- v4.36.0-rc2 Verso stack, overridden here (a root `require` wins over a transitive one).
require verso from git "https://github.com/leanprover/verso" @ "v4.36.0-rc2"
require subverso from git "https://github.com/leanprover/subverso" @ "verso-v4.36.0-rc2"
require «verso-slides» from git "https://github.com/leanprover/verso-slides" @ "v4.36.0-rc2"
-- lean-vir #275, "feat: support Lean 4.36.0-rc2" (the v4.35.0 pin no longer loads in Lake 4.36).
require lean_vir from git "https://github.com/ejgallego/lean-vir" @
  "9c4141f10e598b02f4c7f190ae11aa9e87fc1a9a"
-- Temporary: verso-blueprint v4.35.0 patched for the Lean 4.36 core APIs (`Lean.Html`,
-- `Lean.Doc` views). Drop for the upstream v4.36 branch once it exists.
require VersoBlueprint from "vendor/verso-blueprint"

package TemporalGraphBlueprint where
  packagesDir := "../.lake/packages"
  precompileModules := false
  leanOptions := #[
    ⟨`experimental.module, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.verso.blueprint.math.lint, true⟩,
    ⟨`weak.verso.blueprint.externalCode.strictResolve, true⟩,
    ⟨`weak.verso.code.warnLineLength, .ofNat 0⟩
  ]

@[default_target]
lean_lib Blueprint where
  roots := #[`Blueprint]

@[default_target]
lean_exe «blueprint-gen» where
  root := `Main
  supportInterpreter := true
