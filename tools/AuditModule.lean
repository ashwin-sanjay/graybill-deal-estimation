import Lean
import Lean.Util.CollectAxioms

open Lean








def auditKind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def standardAxiom (n : Name) : Bool :=
  n == ``propext || n == ``Classical.choice || n == ``Quot.sound

def jsonNames (ns : Array Name) : Json :=
  toJson (ns.map (·.toString))

def importJson (i : Import) : Json := Json.mkObj [
  ("module", toJson i.module.toString),
  ("import_all", toJson i.importAll),
  ("exported", toJson i.isExported),
  ("meta", toJson i.isMeta)]

def auditOwned (target : Name) : CoreM Json := do
  let env ← getEnv
  let some idx := env.getModuleIdx? target
    | throwError "Target module {target} is absent from the imported environment"
  let names := env.constants.fold (init := #[]) fun ns n _ =>
    if env.getModuleIdxFor? n == some idx then ns.push n else ns
  let names := names.qsort Name.lt
  let mut rows : Array Json := #[]
  let mut allAxioms : NameSet := {}
  let mut theoremCount := 0
  let mut nonstandardDeclarations := 0
  let mut directAxiomCount := 0
  for n in names do
    let some ci := env.find? n
      | throwError "Owned constant {n} was enumerated but could not be found"
    let axs ← collectAxioms n
    let other := axs.filter (!standardAxiom ·)
    allAxioms := axs.foldl (fun s a => s.insert a) allAxioms
    if ci.isTheorem then theoremCount := theoremCount + 1
    if auditKind ci == "axiom" then directAxiomCount := directAxiomCount + 1
    if !other.isEmpty then nonstandardDeclarations := nonstandardDeclarations + 1
    let ty ← (Meta.ppExpr ci.type).run'
    rows := rows.push <| Json.mkObj [
      ("name", toJson n.toString),
      ("owner_module", toJson target.toString),
      ("kind", toJson (auditKind ci)),
      ("is_theorem", toJson ci.isTheorem),
      ("type", toJson ty.pretty),
      ("axioms", jsonNames axs),
      ("nonstandard_axioms", jsonNames other),
      ("uses_sorryAx", toJson (axs.contains ``sorryAx))]
  let all := allAxioms.toArray.qsort Name.lt
  return Json.mkObj [
    ("declaration_count", toJson names.size),
    ("theorem_count", toJson theoremCount),
    ("owned_axiom_count", toJson directAxiomCount),
    ("declarations_using_nonstandard_axioms", toJson nonstandardDeclarations),
    ("all_axioms", jsonNames all),
    ("nonstandard_axioms", jsonNames (all.filter (!standardAxiom ·))),
    ("uses_sorryAx", toJson (all.contains ``sorryAx)),
    ("declarations", toJson rows)]

unsafe def main (args : List String) : IO UInt32 := do
  try
    let [arg] := args
      | throw <| IO.userError "usage: lean --run AuditModule.lean Target.Module"
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
    let directImports := parts[0].1.imports
    enableInitializersExecution
    let env ← importModules #[{ module := target }] {} (loadExts := true)
    let owned ← (auditOwned target).toIO' {
      fileName := "<module-axiom-audit>", fileMap := default,
      options := ({} : Options).set `maxRecDepth (1000000 : Nat) |>.set `maxHeartbeats (0 : Nat)
    } { env }
    let output := Json.mkObj [
      ("schema_version", toJson (1 : Nat)),
      ("target_module", toJson target.toString),
      ("lean_version", toJson Lean.versionString),
      ("object_path", toJson objectPath.toString),
      ("object_parts", toJson (files.map (·.toString))),
      ("direct_imports", toJson (directImports.map importJson)),
      ("scope", toJson "Every declaration owned by the target module, including private and generated declarations; excludes imported owners."),
      ("method", toJson "Lean getModuleIdxFor? ownership and collectAxioms; no kernel replay performed by this program."),
      ("allowed_axioms", toJson #["propext", "Classical.choice", "Quot.sound"]),
      ("audit", owned)]
    IO.println output.compress
    return (0 : UInt32)
  catch e =>
    IO.eprintln <| (Json.mkObj [("error", toJson e.toString)]).compress
    return (1 : UInt32)
