import WeakMarkov333569
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (n, c) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    if m.toString.endsWith "333569" then
      let ax ← Lean.collectAxioms n
      let kind := match c with
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .thmInfo _ => "theorem"
        | .opaqueInfo _ => "opaque"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | .quotInfo _ => "quotient"
      logInfo m!"INVENTORY|{m}|{n}|{kind}|{c.isUnsafe}|{ax.toList}"
#print MathDB333569.fullySupported_stationary_oneStep_localMaximum
#print axioms MathDB333569.fullySupported_stationary_oneStep_localMaximum
#print MeasureTheory.ProbabilityMeasure.instTopologicalSpace
