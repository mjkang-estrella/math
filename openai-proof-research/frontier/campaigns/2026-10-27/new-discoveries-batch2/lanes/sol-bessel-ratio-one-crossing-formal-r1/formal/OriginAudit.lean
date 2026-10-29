import Cases
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Elab.Command
set_option autoImplicit false
set_option warningAsError true
set_option pp.all true
set_option pp.privateNames true
set_option pp.maxSteps 1000000
set_option maxRecDepth 10000
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mods := #[`Crossing, `Transfer, `Cases]
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
  let mut pending := names.toList
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    let some ci := env.find? name | throwError "Unknown dependency {name}"
    if ci.isUnsafe || ci.isPartial || (ci.isAxiom && !allowed.contains name) then
      throwError "Unsafe transitive dependency {name}"
    pending := ci.getUsedConstantsAsSet.toList ++ pending
  logInfo m!"SAFETY_CLOSURE {seen.size}"
  liftIO <| IO.FS.writeFile "dependencies.txt" (String.intercalate "\n" (env.header.moduleNames.toList.map toString))
