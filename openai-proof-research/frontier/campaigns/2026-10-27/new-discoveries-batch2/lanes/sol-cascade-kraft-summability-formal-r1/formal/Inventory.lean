import KraftSummability
import Lean
set_option autoImplicit false
set_option warningAsError true
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mods := #[`DepthDefs, `SourceDefs, `TreeConstruction, `KraftSummability]
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    if mods.contains modName then
      for name in env.header.moduleData[i]!.constNames do
        logInfo m!"DECL {modName} {name}"
