import PDTAR.ReductionProof
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mods := #[`PDTAR.Defs, `PDTAR.Basic, `PDTAR.FortDuality, `PDTAR.KstFamily, `PDTAR.Core, `PDTAR.Remaining, `PDTAR.ReductionTransport, `PDTAR.ReductionFlip, `PDTAR.ReductionCube, `PDTAR.ReductionBasis, `PDTAR.ReductionMetric, `PDTAR.ReductionPaths, `PDTAR.ReductionProof]
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
