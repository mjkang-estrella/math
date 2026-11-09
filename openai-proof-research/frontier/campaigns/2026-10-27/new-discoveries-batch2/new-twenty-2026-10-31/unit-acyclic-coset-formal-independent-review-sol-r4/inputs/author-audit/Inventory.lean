import Sequence
import Lean
open Lean Elab Command
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
run_cmd do
  let env := (← getEnv).setExporting false
  let modules := #[`Matching, `Bridges, `Coset, `Controls, `Sequence]
  let mut locals : Array Name := #[]
  for (n, _) in env.constants.toList do
    if let some i := env.getModuleIdxFor? n then
      if modules.contains env.header.moduleNames[i.toNat]! then
        locals := locals.push n
  let mut rows : Array Json := #[]
  let mut todo := locals.toList
  let mut seen : NameSet := {}
  let mut forbidden : Array String := #[]
  for _ in [:200000] do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | throwError "Missing dependency {n}"
      let mut deps := ci.type.getUsedConstants
      if let some v := ci.value? true then
        deps := deps ++ v.getUsedConstants
      if let .inductInfo v := ci then
        deps := deps ++ v.ctors.toArray
      let origin := match env.getModuleIdxFor? n with
        | some i => toString env.header.moduleNames[i.toNat]!
        | none => "current"
      let ax := match ci with | .axiomInfo _ => true | _ => false
      if ci.isUnsafe then forbidden := forbidden.push s!"unsafe:{n}"
      if ax && !(#[`propext, `Classical.choice, `Quot.sound].contains n) then
        forbidden := forbidden.push s!"axiom:{n}"
      let localDecl := locals.contains n
      rows := rows.push <| Json.mkObj [
        ("name", toJson (toString n)), ("origin", toJson origin),
        ("local", toJson localDecl), ("unsafe", toJson ci.isUnsafe),
        ("axiom", toJson ax), ("dependencies", toJson (deps.map toString)),
        ("type", toJson (if localDecl then reprStr ci.type else "upstream")),
        ("body", toJson (if localDecl then (ci.value? true).map reprStr |>.getD "no value (constructor/recursor/axiom)" else "upstream"))]
      todo := deps.toList ++ todo
  unless todo.isEmpty do throwError "DAG traversal fuel exhausted"
  let axioms ← collectAxioms `UnitCoset.refutation
  let out := Json.mkObj [("local_count", toJson locals.size),
    ("local_names", toJson (locals.map toString)), ("closure_count", toJson rows.size),
    ("refutation_axioms", toJson (axioms.map toString)),
    ("forbidden", toJson forbidden), ("declarations", Json.arr rows)]
  liftIO <| IO.FS.writeFile "audit/inventory.json" out.pretty
  logInfo m!"locals={locals.size} closure={rows.size} axioms={axioms} forbidden={forbidden}"
  unless forbidden.isEmpty do throwError "Forbidden dependencies"
#print UnitCoset.Conjecture
#print UnitCoset.Standing
#print UnitCoset.Admissible
#print UnitCoset.multiplicity
#print UnitCoset.sequence
#print UnitCoset.UnitSequence
#print UnitCoset.Acyclic
#print axioms UnitCoset.refutation
#print axioms UnitCoset.constant_acyclic
#print axioms UnitCoset.identity_unit
