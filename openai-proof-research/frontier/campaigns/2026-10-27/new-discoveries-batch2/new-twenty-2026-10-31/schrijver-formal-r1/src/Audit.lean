import Data27
import Controls
import Lean.Util.CollectAxioms
open Lean
set_option pp.all true
set_option pp.universes true
set_option pp.proofs true
set_option pp.maxSteps 2000000
set_option pp.deepTerms true
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let modName := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.header.mainModule
    if modName == `Definitions || modName == `Checkers || modName == `Data27 || modName == `Controls then
      count := count + 1
      let axs ← collectAxioms n
      let impl := Lean.Compiler.getImplementedBy? env n
      let ext := isExtern env n
      logInfo m!"DECL {n}\nMODULE {modName}\nUNSAFE {ci.isUnsafe}\nPARTIAL {ci.isPartial}\nIMPLEMENTED_BY {impl}\nEXTERN {ext}\nTYPE {ci.type}\nBODY {ci.value? (allowOpaque := true)}\nAXIOMS {axs}"
      if ci.isUnsafe || ci.isPartial || impl.isSome || ext || n.toString.endsWith "_unsafe_rec" then
        throwError "Forbidden declaration property: {n}"
      for ax in axs do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "Forbidden axiom {ax} in {n}"
  logInfo m!"TOTAL_LOCAL_DECLARATIONS {count}"
