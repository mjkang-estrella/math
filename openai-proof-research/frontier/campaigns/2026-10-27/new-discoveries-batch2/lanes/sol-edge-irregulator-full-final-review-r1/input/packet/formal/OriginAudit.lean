import Result
import Lean
set_option autoImplicit false
set_option warningAsError true
set_option pp.all true
set_option pp.privateNames true
set_option pp.maxSteps 1000000
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mods := #[`Source, `Boundary, `Gadget, `Edges, `Degrees, `Local, `Lower, `Charges, `Transport, `Refutation, `UpperWitness, `UpperDegrees, `Upper, `Result]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut names : Array Name := #[]
  for (name, ci) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if mods.contains modName then
        let axs ← collectAxioms name
        for ax in axs do
          unless allowed.contains ax do
            throwError "Forbidden dependency {name}: {ax}"
        if ci.isUnsafe || ci.isAxiom || ci.isPartial then
          throwError "Forbidden flag {name}"
        logInfo m!"AUDIT {modName} {name}\nTYPE {ci.type}\nAXIOMS {axs}\nFLAGS unsafe={ci.isUnsafe} partial={ci.isPartial} axiom={ci.isAxiom}"
        names := names.push name
  let mut moduleCount := 0
  for i in [:env.header.moduleNames.size] do
    if mods.contains env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        unless names.contains name do
          throwError "Missing actual module declaration {name}"
        moduleCount := moduleCount+1
  unless moduleCount == names.size do
    throwError "Inventory mismatch"
  logInfo m!"AUDIT_TOTAL {names.size}"
  liftIO <| IO.FS.writeFile "dependencies.txt" (String.intercalate "\n" (env.header.moduleNames.toList.map toString))
