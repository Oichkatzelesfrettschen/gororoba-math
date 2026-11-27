/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Sebastian Ullrich

`replayFromImports` is copied verbatim from `src/lean/LeanChecker.lean` of Lean v4.35.0 (commit
eb6cafb7290e8bd5f2937522d8d804f58f02bafc); the driver below it is this repository's.
-/
import Lean.CoreM
import Lean.Replay

open Lean

/-!
# Kernel replay of named modules

Each argument names one module. The driver replays the module from its imports with the kernel, as
`leanchecker` does, without the walk over every object file of the search path that `leanchecker`
runs per target to resolve a module-name prefix: a named module replays exactly itself, and a name
that is a prefix of other modules (the root module) replays only its own object. It prints
`PASS M` or `FAIL M: error` per module, with the kernel's error as `leanchecker` reports it,
and the exit code is 1 when any module fails.

Run it as `lake env lean --run ../ci/replay_modules.lean M...` from `lean/`: `lake env` supplies
`LEAN_PATH` and the sysroot once.
-/

unsafe def replayFromImports (module : Name) : IO Unit := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  -- Load all module data parts (exported, server, private)
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants := {}
  -- Collect constants from last ("most private") part, which subsumes all prior ones
  for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
    newConstants := newConstants.insert name ci
  discard <| env.toKernelEnv.replay newConstants
  env.freeRegions

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut rc : UInt32 := 0
  for a in args do
    let m := a.toName
    if m.isAnonymous then
      IO.println s!"FAIL {a}: not a module name"
      rc := 1
    else
      try
        replayFromImports m
        IO.println s!"PASS {a}"
      catch e =>
        IO.println s!"FAIL {a}: {e}"
        rc := 1
    (← IO.getStdout).flush
  return rc
