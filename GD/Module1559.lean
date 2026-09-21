
import GD.Module1557
import Lean.Util.CollectAxioms
set_option warningAsError true
open Lean Elab Command
run_cmd do
  let prefixes : List Name := [`GD.N0100.N0347]
  let names := (← getEnv).constants.toList.filterMap fun (n, _) =>
    if prefixes.any (fun p => p.isPrefixOf n) then some n else none
  for n in names do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "Unexpected axioms {n}: {axs}"
    logInfo m!"AUDIT|{n}|{axs}"
  logInfo m!"AUDITED_DECLARATIONS|{names.length}"
