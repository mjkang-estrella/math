import PDTAR.FinalComplete
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mods := #[`PDTAR.Defs, `PDTAR.Basic, `PDTAR.FortDuality, `PDTAR.KstFamily, `PDTAR.Core, `PDTAR.Remaining, `PDTAR.CoreProofLocal, `PDTAR.ReductionTransport, `PDTAR.CoreProofHub, `PDTAR.CoreProofIndependent, `PDTAR.ReductionFlip, `PDTAR.SmallEdge, `PDTAR.CoreProofDegree, `PDTAR.ReductionCube, `PDTAR.SmallObligations, `PDTAR.CoreProofComplete, `PDTAR.ReductionBasis, `PDTAR.CoreProofFinal, `PDTAR.ReductionMetric, `PDTAR.CoreProofAssembly, `PDTAR.ReductionPaths, `PDTAR.CoreSmallProof, `PDTAR.ReductionProof, `PDTAR.SmallTwoFamily, `PDTAR.SmallTwoWitness, `PDTAR.SmallStatement, `PDTAR.Final, `PDTAR.SmallStarLocal, `PDTAR.SmallStarRigidity, `PDTAR.SmallStarComplete, `PDTAR.SmallK33Local, `PDTAR.SmallK33Degree, `PDTAR.SmallK33Complete, `PDTAR.FinalComplete]
  let closure := env.header.moduleNames.filter (fun n => n.toString.startsWith "PDTAR.")
  unless closure.size == mods.size && closure.all (fun n => mods.contains n) do
    throwError "closure differs from audited module set: {closure} versus {mods}"
  logInfo m!"CLOSURE_EQUALS_AUDITED {closure.size}; modules={closure}"
  let mut ids := #[]
  for m in mods do
    let some i := env.getModuleIdx? m | throwError "missing module {m}"
    ids := ids.push i
  let mut total : Nat := 0
  for (n, ci) in env.constants.toList do
    let some i := env.getModuleIdxFor? n | continue
    unless ids.contains i do continue
    total := total + 1
    let kind := match ci with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    let imp := (Compiler.getImplementedBy? env n).isSome
    let ext := (externAttr.getParam? env n).isSome
    let axs ← Lean.collectAxioms n
    logInfo m!"DECL {n} kind={kind} unsafe={ci.isUnsafe} partial={ci.isPartial} implemented_by={imp} extern={ext} axioms={axs}"
    if ci.isUnsafe || ci.isPartial || imp || ext || kind == "axiom" ||
        (n.toString.splitOn "_unsafe_rec").length > 1 then
      throwError "forbidden declaration {n}"
    for a in axs do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        throwError "forbidden axiom {a} in {n}"
  logInfo m!"AUDIT_TOTAL {total}; violations 0"
