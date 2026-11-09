import SourceTheorem
import FiniteAbel
set_option autoImplicit false
set_option warningAsError true
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mods := #[`MeanAnalyticDefs, `MeanDerivatives, `MeanSourceDefs, `Stolarsky, `Transfer, `GapAnalytic, `Centered, `MeanExpansion, `MeanFiniteCertificate, `ExpPolynomial, `MeanEExpansion, `MeanWeights, `MeanEHighPositive, `MeanJets0, `MeanJets1, `MeanJets2, `MeanJet12, `MeanJet13, `MeanJet14, `MeanJet15, `MeanJets3, `MeanJet16, `MeanJet17, `MeanJet18, `MeanJet19, `MeanJets4, `MeanJet20, `MeanJet21, `MeanJet22, `MeanJet23, `MeanJets5, `MeanEPositive, `GapMonotonicity, `SourceTheorem, `FiniteAbel]
  let mut total := 0
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    if mods.contains modName then
      let data := env.header.moduleData[i]!
      let mut actual : Array Name := #[]
      for (n, _) in env.constants.toList do
        if env.getModuleIdxFor? n == some i then
          actual := actual.push n
      unless actual.size == data.constNames.size && actual.all data.constNames.contains do
        logInfo m!"ORIGIN_DIFFERENCE {modName}: map-only={actual.filter (fun n => !data.constNames.contains n)}; data-only={data.constNames.filter (fun n => !actual.contains n)}"
      for n in actual do
        let ci := env.find? n |>.get!
        let axs ← collectAxioms n
        unless !ci.isUnsafe && !ci.isAxiom && axs.all (#[`propext, `Classical.choice, `Quot.sound].contains) do
          throwError "Forbidden actual declaration {n}"
        if !data.constNames.contains n then
          logInfo m!"MAP_ONLY_TYPE {n}: {ci.type}; AXIOMS {axs}; unsafe={ci.isUnsafe} partial={ci.isPartial} axiom={ci.isAxiom}"
      total := total + actual.size
      logInfo m!"ORIGIN {modName} {actual.size}"
      for n in data.extraConstNames do
        match env.find? n with
        | none => logInfo m!"IR_ONLY {modName} {n}: no kernel declaration/type"
        | some ci => logInfo m!"EXTRA_KERNEL {modName} {n}: {ci.type}; unsafe={ci.isUnsafe}"
  logInfo m!"ORIGIN_TOTAL {total}"
#print LogArctangentSource.SourceClaim
#print LogArctangentSource.source_conjecture37
#print axioms LogArctangentSource.source_conjecture37
