import Sigma.Endpoint
import NegativeControls
import ReviewerSanity
import Lean.Util.CollectAxioms

open Lean Elab Command Meta
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.maxSteps 10000000

run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[idx.toNat]!
      if origin.toString.startsWith "Sigma." || origin.toString == "NegativeControls" || origin.toString == "ReviewerSanity" then
        let axioms ← collectAxioms name
        if ci.isUnsafe || ci.isPartial || !(ci.value? true).isSome then
          throwError "invalid declaration {name}"
        for ax in axioms do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError "forbidden axiom {ax} in {name}"
        let ty ← liftTermElabM <| Meta.ppExpr ci.type
        logInfo <| Json.compress <| Json.mkObj [
          ("name", toJson name.toString), ("module", toJson origin.toString),
          ("type", toJson ty.pretty), ("type_raw", toJson (reprStr ci.type)),
          ("value_present", toJson (ci.value? true).isSome), ("unsafe", toJson ci.isUnsafe),
          ("partial", toJson ci.isPartial), ("axioms", toJson (axioms.map Name.toString))]
        count := count + 1
  logInfo m!"AUDIT_COUNT {count}"
