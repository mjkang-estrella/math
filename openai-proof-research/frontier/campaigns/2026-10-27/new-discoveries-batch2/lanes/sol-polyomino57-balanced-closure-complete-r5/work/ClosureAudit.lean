import Grid
import Growth
import Normalization
import Bounds
import Witness
import Efficient
import Coverage
import Existence
import ListCertificate
import Assembly
import SortedCertificate
import PlacementTree
import LocalAssembly
import Layer6
import Layer7
import Closure5C000
import Closure5C001
import Closure5C002
import Closure5C003
import Closure5C004
import Closure5C005
import Closure5C006
import Closure5C007
import Closure5
import Closure6C000
import Closure6C001
import Closure6C002
import Closure6C003
import Closure6C004
import Closure6C005
import Closure6C006
import Closure6C007
import Closure6C008
import Closure6C009
import Closure6C010
import Closure6C011
import Closure6C012
import Closure6C013
import Closure6C014
import Closure6C015
import Closure6C016
import Closure6C017
import Closure6C018
import Closure6C019
import Closure6C020
import Closure6C021
import Closure6C022
import Closure6C023
import Closure6C024
import Closure6C025
import Closure6C026
import Closure6
import ClosureChain
import SmallClosure
import SevenCoverage
import FamilyAssembly
import FamilyTree
import Layer8
import Closure7C000
import Closure7C047
import Closure7C094
import Local7N8
import Local7N32
import Local7N128
import Local8N8
import Local8N32
import Local8N128
import Local9N8
import Local9N32
import Local9N128
import Local10N8
import Local10N32
import Local10N128
import TreeBlock000
import TreeBlock001
import TreeBlock002
import TreeBlock003
import TreeBlock004
import TreeBlock005
import TreeBlock006
import TreeBlock007
import TreeBlock008
import TreeBlock009
import TreeBlock010
import TreeBlock011
import TreeBlock012
import TreeBlock013
import TreeBlock014
import TreeBlock015
import TreeBlock016
import TreeBlock017
import TreeBlock018
import TreeBlock019
import TreeBlock020
import TreeBlock021
import TreeBlock022
import TreeBlock023
import TreeBlock024
import TreeBlock025
import TreeBlock026
import TreeBlock027
import TreeBlock028
import TreeBlock029
import TreeBlock030
import TreeBlock031
import TreeBlock032
import TreeBlock033
import TreeBlock034
import TreeBlock035
import TreeBlock036
import TreeBlock037
import TreeBlock038
import TreeBlock039
import TreeBlock040
import TreeBlock041
import TreeBlock042
import TreeBlock043
import TreeBlock044
import TreeBlock045
import TreeBlock046
import TreeBlock047
import TreeBlock048
import TreeBlock049
import TreeBlock050
import TreeBlock051
import TreeBlock052
import TreeBlock053
import TreeBlock054
import TreeBlock055
import TreeBlock056
import TreeBlock057
import TreeBlock058
import TreeBlock059
import TreeBlock060
import TreeBlock061
import TreeBlock062
import TreeBlock063
import TreeBlock064
import TreeBlock065
import TreeBlock066
import TreeAll
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
  let mods := #[`Grid, `Growth, `Normalization, `Bounds, `Witness, `Efficient, `Coverage, `Existence, `ListCertificate, `Assembly, `SortedCertificate, `PlacementTree, `LocalAssembly, `Layer6, `Layer7, `Closure5C000, `Closure5C001, `Closure5C002, `Closure5C003, `Closure5C004, `Closure5C005, `Closure5C006, `Closure5C007, `Closure5, `Closure6C000, `Closure6C001, `Closure6C002, `Closure6C003, `Closure6C004, `Closure6C005, `Closure6C006, `Closure6C007, `Closure6C008, `Closure6C009, `Closure6C010, `Closure6C011, `Closure6C012, `Closure6C013, `Closure6C014, `Closure6C015, `Closure6C016, `Closure6C017, `Closure6C018, `Closure6C019, `Closure6C020, `Closure6C021, `Closure6C022, `Closure6C023, `Closure6C024, `Closure6C025, `Closure6C026, `Closure6, `ClosureChain, `SmallClosure, `SevenCoverage, `FamilyAssembly, `FamilyTree, `Layer8, `Closure7C000, `Closure7C047, `Closure7C094, `Local7N8, `Local7N32, `Local7N128, `Local8N8, `Local8N32, `Local8N128, `Local9N8, `Local9N32, `Local9N128, `Local10N8, `Local10N32, `Local10N128, `TreeBlock000, `TreeBlock001, `TreeBlock002, `TreeBlock003, `TreeBlock004, `TreeBlock005, `TreeBlock006, `TreeBlock007, `TreeBlock008, `TreeBlock009, `TreeBlock010, `TreeBlock011, `TreeBlock012, `TreeBlock013, `TreeBlock014, `TreeBlock015, `TreeBlock016, `TreeBlock017, `TreeBlock018, `TreeBlock019, `TreeBlock020, `TreeBlock021, `TreeBlock022, `TreeBlock023, `TreeBlock024, `TreeBlock025, `TreeBlock026, `TreeBlock027, `TreeBlock028, `TreeBlock029, `TreeBlock030, `TreeBlock031, `TreeBlock032, `TreeBlock033, `TreeBlock034, `TreeBlock035, `TreeBlock036, `TreeBlock037, `TreeBlock038, `TreeBlock039, `TreeBlock040, `TreeBlock041, `TreeBlock042, `TreeBlock043, `TreeBlock044, `TreeBlock045, `TreeBlock046, `TreeBlock047, `TreeBlock048, `TreeBlock049, `TreeBlock050, `TreeBlock051, `TreeBlock052, `TreeBlock053, `TreeBlock054, `TreeBlock055, `TreeBlock056, `TreeBlock057, `TreeBlock058, `TreeBlock059, `TreeBlock060, `TreeBlock061, `TreeBlock062, `TreeBlock063, `TreeBlock064, `TreeBlock065, `TreeBlock066, `TreeAll]
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
