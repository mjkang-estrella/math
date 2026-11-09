import SourceTheorem
import FiniteAbel
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
  let mods := #[`MeanAnalyticDefs,`MeanDerivatives,`MeanSourceDefs,`Stolarsky,`Transfer,`GapAnalytic,`Centered,`MeanExpansion,`MeanFiniteCertificate,`ExpPolynomial,`MeanEExpansion,`MeanWeights,`MeanEHighPositive,`MeanJets0,`MeanJets1,`MeanJets2,`MeanJet12,`MeanJet13,`MeanJet14,`MeanJet15,`MeanJets3,`MeanJet16,`MeanJet17,`MeanJet18,`MeanJet19,`MeanJets4,`MeanJet20,`MeanJet21,`MeanJet22,`MeanJet23,`MeanJets5,`MeanEPositive,`GapMonotonicity,`SourceTheorem,`FiniteAbel]
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
