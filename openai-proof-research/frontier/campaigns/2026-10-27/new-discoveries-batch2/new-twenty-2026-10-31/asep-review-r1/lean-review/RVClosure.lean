import ASEPArcs
import RVRestate

/-! Closure of the endpoints (and of the reviewer's restatement): which local / suspicious constants are reached. -/
open Lean Elab Command

partial def rvClosureOf (env : Environment) (todo : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}; let mut st := todo
  while h : st.size > 0 do
    let c := st.back; st := st.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      let mut es : Array Expr := #[ci.type]
      match ci with
      | .defnInfo v => es := es.push v.value
      | .thmInfo v => es := es.push v.value
      | .opaqueInfo v => es := es.push v.value
      | .inductInfo v => st := st ++ v.ctors.toArray
      | .ctorInfo v => st := st.push v.induct
      | _ => pure ()
      for e in es do
        for d in e.getUsedConstants do
          if !seen.contains d then st := st.push d
  return seen

elab "#rvclosure" : command => do
  let env := (← getEnv).setExporting false
  let eps := #[``ASEP.arc_counterexample, ``ASEP.arc_neighborhood_tour_conjecture_false, ``ASEP.counterexample,
    ``ASEP.neighborhood_tour_conjecture_false, ``ASEP.segment_not_face, ``ASEP.segment_not_exposed,
    ``RV.conjecture1_false, ``RV.counterexample]
  for ep in eps do
    let s := rvClosureOf env #[ep]
    let names := s.toList
    let unsafeRec := names.filter (fun n => (n.toString.splitOn "_unsafe_rec").length > 1)
    let bad := names.filter (fun n => n == ``sorryAx || n == ``Lean.ofReduceBool || n == ``Lean.ofReduceNat || n == ``Lean.trustCompiler)
    let nonSafe := names.filter (fun n => match env.find? n with
      | some ci => ci.isUnsafe || ci.isPartial | none => false)
    let axs := names.filter (fun n => match env.find? n with | some (.axiomInfo _) => true | _ => false)
    let chunkOk := names.filter (fun n => (n.toString.splitOn "_ok").length > 1 && (n.toString.splitOn "chunk").length > 1)
    logInfo m!"RVCLOSURE {ep} size={names.length} axioms={axs} unsafe_rec={unsafeRec} forbidden={bad} unsafe_or_partial={nonSafe} chunk_ok_count={chunkOk.length} certs_cover={s.contains `ASEP.certs_cover}"

#rvclosure
