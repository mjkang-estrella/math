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
  let e ← getEnv
  let mut total : Nat := 0
  for (nm, info) in e.constants.toList do
    let some ix := e.getModuleIdxFor? nm | continue
    let source := e.header.moduleNames[ix.toNat]!
    unless source.toString.startsWith "Sigma." || #["NegativeControls", "ReviewerSanity"].contains source.toString do continue
    let axs ← collectAxioms nm
    unless !info.isUnsafe && !info.isPartial && (info.value? true).isSome do
      throwError "bad body or safety: {nm}"
    for a in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "bad dependency {a} of {nm}"
    let typ ← liftTermElabM <| Meta.ppExpr info.type
    logInfo <| Json.compress <| Json.mkObj [
      ("declaration", toJson nm.toString), ("origin", toJson source.toString),
      ("full_type", toJson typ.pretty), ("raw_type", toJson (reprStr info.type)),
      ("raw_body", toJson (reprStr (info.value? true))),
      ("value_present", toJson (info.value? true).isSome),
      ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial),
      ("axioms", toJson (axs.map Name.toString))]
    total := total + 1
  logInfo m!"REVIEWER_TOTAL {total}"
#print Sigma365710.extremal_completeBipartite
#print Sigma365710.attainer_classification
#print Sigma365710.mathdb_365710
