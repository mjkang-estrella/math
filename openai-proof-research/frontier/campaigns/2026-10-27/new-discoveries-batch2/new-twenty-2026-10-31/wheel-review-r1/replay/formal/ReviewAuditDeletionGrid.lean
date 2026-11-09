import LowerWeighted
import Lean.Util.CollectAxioms
open Lean
set_option pp.all true
set_option pp.universes true
set_option pp.proofs true
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let modName := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.header.mainModule
    if modName == `DeletionGrid then
      count := count + 1
      let axs ← collectAxioms n
      logInfo m!"DECL {n}\nMODULE {modName}\nUNSAFE {ci.isUnsafe}\nPARTIAL {ci.isPartial}\nTYPE {ci.type}\nBODY_PRESENT {(ci.value? (allowOpaque := true)).isSome}
KIND {match ci with | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"}\nAXIOMS {axs}"
      if ci.isUnsafe || ci.isPartial then throwError "Forbidden safety flag: {n}"
      for ax in axs do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "Forbidden axiom {ax} in {n}"
  logInfo m!"TOTAL_LOCAL_DECLARATIONS {count}"
