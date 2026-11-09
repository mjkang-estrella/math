import SourceEndpoint
import FrameBoundaryChecks
set_option pp.all true
set_option pp.proofs false
set_option pp.width 120
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let selected : List String := ["ScalarCore", "SpectralCore", "PolarFrameBridge", "HSBridge", "ContractiveBridge", "GradedSpectralBridge", "GradingConsequences", "BoundaryChecks", "FrameReconstruction", "FrameBlocks", "FrameInequality", "FrameBoundaryChecks", "ProjectionFrames", "RangeFrames", "SourceEndpoint"]
  let names := env.constants.toList.filterMap fun (n, _) =>
    match env.getModuleIdxFor? n with
    | some i => if selected.contains (env.header.moduleNames[i]!.toString) then some n else none
    | none => none
  for n in names.mergeSort (fun a b => a.toString ≤ b.toString) do
    logInfo m!"INVENTORY|{n}"
    elabCommand (← `(#check $(mkIdent n)))
    elabCommand (← `(#print axioms $(mkIdent n)))
