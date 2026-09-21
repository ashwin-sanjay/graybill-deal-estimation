import Lean.CoreM
import Lean.Replay

open Lean




unsafe def main (args : List String) : IO UInt32 := do
  try
    let [arg] := args
      | throw <| IO.userError "usage: lean --run ReplayModule.lean Target.Module"
    let target := arg.toName
    if target.isAnonymous then throw <| IO.userError "empty target module"
    initSearchPath (← getBuildDir)
    let objectPath ← findOLean target
    unless ← objectPath.pathExists do
      throw <| IO.userError s!"Missing compiled module: {objectPath}"
    let mut files := #[objectPath]
    let serverPath := OLeanLevel.server.adjustFileName objectPath
    if ← serverPath.pathExists then
      files := files.push serverPath
      let privatePath := OLeanLevel.private.adjustFileName objectPath
      if ← privatePath.pathExists then files := files.push privatePath
    let parts ← readModuleDataParts files
    if h : parts.size = 0 then throw <| IO.userError "No readable module data parts" else
    let (mod, _) := parts[0]
    let (_, state) ← importModulesCore mod.imports |>.run
    let imported ← finalizeImport state mod.imports {} 0 false false (isModule := true)
    let mut constants := {}
    let mut count := 0
    for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
      constants := constants.insert name ci
      count := count + 1
    let checked ← imported.replay constants
    checked.freeRegions
    IO.println <| (Json.mkObj [
      ("schema_version", toJson (1 : Nat)),
      ("status", toJson "passed"),
      ("target_module", toJson target.toString),
      ("lean_version", toJson Lean.versionString),
      ("replayed_declaration_count", toJson count),
      ("object_path", toJson objectPath.toString),
      ("object_parts", toJson (files.map (·.toString))),
      ("method", toJson "Exact-module Lean kernel replay using LeanChecker.replayFromImports algorithm; imported declarations reused.")]).compress
    return (0 : UInt32)
  catch e =>
    IO.eprintln <| (Json.mkObj [("error", toJson e.toString)]).compress
    return (1 : UInt32)
