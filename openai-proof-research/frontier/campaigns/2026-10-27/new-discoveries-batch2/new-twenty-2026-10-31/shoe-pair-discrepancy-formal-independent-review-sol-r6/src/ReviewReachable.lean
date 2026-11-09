import ShoeColorPMF
import ShoeColorControls
import ShoeSemanticControls
import ShoeAxiomAudit
import ShoeEndpointAxioms
import Lean.Util.CollectAxioms

/-! Audit tool only, never imported by a mathematical endpoint.
Enumerate production origin declarations (including private/generated names),
then visit only their shared transitive type/body closure. -/
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let production := #["ShoeBase", "ShoeProbability", "ShoeStopping", "ShoeBlock",
    "ShoePair", "ShoeConditional", "ShoeDiagonal", "ShoeTermination",
    "ShoeBlockProbability", "ShoeCollision", "ShoeBlockSum", "ShoeScale",
    "ShoeMinorization", "ShoeTV", "ShoeSourceTV", "ShoeEndpoint", "ShoeRelabel",
    "ShoeColorMeasure", "ShoeColorWinner", "ShoeColorConditional", "ShoeColorEndpoint", "ShoeColorControls", "ShoeColorNormalization", "ShoeColorPMF",
    "ShoeControls", "ShoeSemanticControls", "ShoeAxiomAudit", "ShoeEndpointAxioms"]
  let originOf := fun n => match env.getModuleIdxFor? n with
    | some k => env.header.moduleNames[k]!.toString
    | none => "CURRENT"
  for (n, ci) in env.constants.toList do
    liftIO <| IO.println ("AUDIT_ORIGIN " ++ (Json.mkObj [("name", toJson n.toString), ("origin", toJson (originOf n)), ("unsafe", toJson ci.isUnsafe)]).compress)
  let roots := env.constants.fold (fun acc n _ =>
    if production.contains (originOf n) then acc.push n else acc) (#[] : Array Name)
  let endpoints := #[``Shoe.source_strict_universal_supremum,
    ``Shoe.countable_color_strict_universal_supremum,
    ``Shoe.colorConditional_toPMF_transport, ``Shoe.colorWinner_toPMF_transport,
    ``Shoe.color_nontermination_probability_zero,
    ``Shoe.winner_relabel_of_terminates, ``Shoe.finite_winner_zeroExtension,
    ``Shoe.winningLaw_minorization, ``Shoe.sourceTV_eq_countableTV,
    ``Shoe.sourceY_eq, ``Shoe.conditionalColorMeasure_toPMF]
  liftIO <| IO.println ("AUDIT_ROOTS " ++ (toJson (roots.map Name.toString)).compress)
  liftIO <| IO.println ("AUDIT_ENDPOINTS " ++ (toJson (endpoints.map Name.toString)).compress)
  let mut pending := roots
  let mut visited : NameHashSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if visited.contains n then continue
    visited := visited.insert n
    let some ci := env.find? n | throwError "missing reachable declaration {n}"
    let td := ci.type.getUsedConstants
    let value := ci.value? (allowOpaque := true)
    let vd := match value with
      | some v => v.getUsedConstants
      | none => #[]
    liftIO <| IO.println ("AUDIT_NODE " ++ (Json.mkObj [
      ("name", toJson n.toString), ("origin", toJson (originOf n)),
      ("hasBody", toJson value.isSome), ("unsafe", toJson ci.isUnsafe),
      ("typeDependencies", toJson (td.map Name.toString)),
      ("bodyDependencies", toJson (vd.map Name.toString)),
      ("isAxiom", toJson (match ci with | .axiomInfo _ => true | _ => false))]).compress)
    pending := pending ++ td ++ vd
  liftIO <| IO.println s!"AUDIT_COMPLETE {visited.size}"
