import VersoManual
import VersoBlueprint.PreviewManifest
import Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
