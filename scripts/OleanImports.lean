import Lean

/-!
Harness tool (manifest-covered): print the module imports recorded in compiled `.olean` files,
one line `<path>\t<Module1> <Module2> ...`. Used by the partition check of prereg §6a: no
manifest-covered `.olean` may import a module of the vector/test library.
-/

open Lean

def main (args : List String) : IO UInt32 := do
  for a in args do
    let (md, _) ← readModuleData (System.FilePath.mk a)
    let mods := md.imports.toList.map fun i => i.module.toString
    IO.println s!"{a}\t{String.intercalate " " mods}"
  return 0
