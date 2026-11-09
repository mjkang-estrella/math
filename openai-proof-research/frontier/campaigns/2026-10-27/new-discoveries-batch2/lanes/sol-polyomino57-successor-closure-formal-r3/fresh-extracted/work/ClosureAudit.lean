import SevenCoverage
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
  let mods := #[`Grid, `Growth, `Normalization, `Bounds, `Witness, `Efficient, `Coverage, `Existence, `ListCertificate, `Assembly, `SortedCertificate, `PlacementTree, `LocalAssembly, `Layer6, `Layer7, `Closure5C000, `Closure5C001, `Closure5C002, `Closure5C003, `Closure5C004, `Closure5C005, `Closure5C006, `Closure5C007, `Closure5, `Closure6C000, `Closure6C001, `Closure6C002, `Closure6C003, `Closure6C004, `Closure6C005, `Closure6C006, `Closure6C007, `Closure6C008, `Closure6C009, `Closure6C010, `Closure6C011, `Closure6C012, `Closure6C013, `Closure6C014, `Closure6C015, `Closure6C016, `Closure6C017, `Closure6C018, `Closure6C019, `Closure6C020, `Closure6C021, `Closure6C022, `Closure6C023, `Closure6C024, `Closure6C025, `Closure6C026, `Closure6, `ClosureChain, `SmallClosure, `SevenCoverage]
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
