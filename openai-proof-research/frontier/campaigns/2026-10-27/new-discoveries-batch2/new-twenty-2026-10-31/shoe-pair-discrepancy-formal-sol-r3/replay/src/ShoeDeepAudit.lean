import ShoeEndpoint
import ShoeControls
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  liftIO <| IO.println "AUDIT_BEGIN"
  let names := env.constants.fold (fun ns n _ => ns.push n) (#[] : Array Name)
  for n in names do
    let some ci := env.find? n | continue
    let td := ci.type.getUsedConstants.map Name.toString
    let vd := match ci.value? (allowOpaque := true) with
      | some v => v.getUsedConstants.map Name.toString
      | none => #[]
    let origin := match env.getModuleIdxFor? n with
      | some k => env.header.moduleNames[k]!.toString
      | none => "CURRENT"
    liftIO <| IO.println ("AUDIT_NODE " ++ (Json.mkObj [
      ("name",toJson n.toString),("origin",toJson origin),
      ("hasBody",toJson (ci.value? (allowOpaque := true)).isSome),
      ("typeDependencies",toJson td),("bodyDependencies",toJson vd),
      ("isAxiom",toJson (match ci with | .axiomInfo _ => true | _ => false))]).compress)
  let endpoints := #[``Shoe.source_strict_universal_supremum,
    ``Shoe.winningLaw_minorization, ``Shoe.sourceTV_eq_countableTV,
    ``Shoe.sourceY_eq, ``Shoe.conditionalColorMeasure_toPMF]
  let mut reports : Array Json := #[]
  for endpoint in endpoints do
    let axioms ← collectAxioms endpoint
    reports := reports.push (Json.mkObj [("endpoint",toJson endpoint.toString),
      ("axioms",toJson (axioms.map Name.toString))])
  liftIO <| IO.println ("AUDIT_ENDPOINTS " ++ (toJson reports).compress)

#print axioms Shoe.source_strict_universal_supremum
