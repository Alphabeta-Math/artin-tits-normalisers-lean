import Lean.CoreM
import Lean.Replay

open Lean

unsafe def replayExact (module : Name) : IO Nat := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"Missing exact module artifact: {mFile}"
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then
    throw <| IO.userError "Empty exact module data"
  else
    let (mod, _) := parts[0]
    let (_, state) ← importModulesCore mod.imports |>.run
    let env ← finalizeImport state mod.imports {} 0 false false (isModule := true)
    let mut newConstants := {}
    for name in parts[parts.size - 1].1.constNames, ci in parts[parts.size - 1].1.constants do
      newConstants := newConstants.insert name ci
    discard <| env.toKernelEnv.replay newConstants
    env.freeRegions
    return newConstants.size

unsafe def main (args : List String) : IO UInt32 := do
  try
    let [arg] := args | throw <| IO.userError "Expected one exact module name"
    initSearchPath (← findSysroot)
    let count ← replayExact arg.toName
    let row := Json.mkObj [("module", toJson arg), ("declarations", toJson count),
      ("exact", toJson true), ("kernel_replay_passed", toJson true)]
    IO.println s!"EXACT_REPLAY_JSON {row.compress}"
    return 0
  catch error =>
    IO.eprintln s!"Exact kernel replay failed: {error}"
    return 1
