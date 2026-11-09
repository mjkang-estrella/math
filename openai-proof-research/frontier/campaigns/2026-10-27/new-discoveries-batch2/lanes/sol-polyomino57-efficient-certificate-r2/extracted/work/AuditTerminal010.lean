import Terminal010
import Lean
set_option autoImplicit false
set_option warningAsError true
set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs false
set_option pp.maxSteps 1000000
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "dependencies.txt" (String.intercalate "\n" (env.header.moduleNames.toList.map toString))
  let mods := #[`Terminal010]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    if mods.contains modName then
      for name in env.header.moduleData[i]!.constNames do
        let ci := env.find? name |>.get!
        let axs ← collectAxioms name
        for ax in axs do
          unless allowed.contains ax do
            throwError "Forbidden dependency {name}: {ax}"
        if ci.isUnsafe || ci.isAxiom then
          throwError "Forbidden flag {name}"
        logInfo m!"AUDIT {modName} {name}\nTYPE {ci.type}\nAXIOMS {axs}\nFLAGS unsafe={ci.isUnsafe} partial={ci.isPartial} axiom={ci.isAxiom}"
        count := count + 1
  logInfo m!"AUDIT_TOTAL {count}"
