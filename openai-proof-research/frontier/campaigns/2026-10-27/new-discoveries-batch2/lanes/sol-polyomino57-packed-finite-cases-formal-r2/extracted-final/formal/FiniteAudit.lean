import Completed
import Large16
import PackedFull
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
  liftIO <| IO.FS.writeFile "dependencies.txt"
    (String.intercalate "\n" (env.header.moduleNames.toList.map toString))
  let mods := #[`Grid, `Growth, `Normalization, `Bounds, `Witness, `Diagonal, `Spans, `Placement, `Symmetry, `SignedNormalization, `CanonicalCoverage, `Potential, `Bridge, `FiniteBridge, `SmallData, `SmallGeometry, `SmallBase, `SmallEdge, `SmallMerge, `SmallFull, `SmallCase, `Empty00, `Empty01, `Empty02, `Empty03, `Empty04, `Empty05, `Empty06, `Empty07, `Empty08, `Empty09, `Empty10, `Empty11, `Empty12, `Empty13, `Empty14, `Empty15, `Empty16, `Empty17, `Empty18, `Empty19, `Empty20, `Empty21, `Empty22, `Empty23, `Empty24, `Empty25, `Empty26, `Empty27, `Empty28, `Empty29, `Empty30, `Empty31, `Empty32, `Empty33, `Empty34, `Forced730, `Completed, `Large16, `PackedRows, `PackedBits, `PackedFull0, `PackedFull1, `PackedFull2, `PackedFull3, `PackedFull4, `PackedFull5, `PackedFull6, `PackedFull7, `PackedFull]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut names : Array String := #[]
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    if mods.contains modName then
      for name in env.header.moduleData[i]!.constNames do
        let ci := env.find? name |>.get!
        let axs ← collectAxioms name
        for ax in axs do
          unless allowed.contains ax do
            throwError "Forbidden dependency {name}: {ax}"
        if ci.isUnsafe || ci.isAxiom || (ci.isPartial && name != `Polyomino57.attachCheck._unsafe_rec) then
          throwError "Forbidden flag {name}"
        names := names.push name.toString
        logInfo m!"AUDIT {modName} {name}\nTYPE {ci.type}\nAXIOMS {axs}\nFLAGS unsafe={ci.isUnsafe} partial={ci.isPartial} axiom={ci.isAxiom}"
  liftIO <| IO.FS.writeFile "declaration-names.txt" (String.intercalate "\n" names.toList)
  logInfo m!"AUDIT_TOTAL {names.size}"
