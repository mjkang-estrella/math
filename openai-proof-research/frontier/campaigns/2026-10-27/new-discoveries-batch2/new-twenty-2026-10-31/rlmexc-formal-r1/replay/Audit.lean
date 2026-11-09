import Endpoint
import Control

#print axioms AK350721.conjecture_refuted
#print axioms AK350721.nonvacuity_control
#print axioms AK350721.characterization9
#print axioms AK350721.coeff_rawSum

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`Definitions, `Bridge, `Finite, `Concrete,
    `Arithmetic, `Characterization, `Endpoint, `Control, `Audit]
  let names := env.allImportedModuleNames
  let mut count : Nat := 0
  for (name, ci) in env.constants.toList do
    let own := match env.getModuleIdxFor? name with
      | some idx => modules.contains (names[idx.toNat]!)
      | none => true
    if own then
      count := count + 1
      if ci.isUnsafe || ci.isPartial ||
          (Compiler.implementedByAttr.getParam? env name).isSome ||
          (getExternAttrData? env name).isSome ||
          (name.toString.contains "_unsafe_rec") then
        throwError "Forbidden metadata on {name}"
      if let .axiomInfo _ := ci then
        throwError "Forbidden new assumption {name}"
  logInfo m!"Local declaration metadata audit passed: {count} declarations"
