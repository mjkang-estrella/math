import Endpoint
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let pkt : Array Name := #[`GroupSemantics, `NormalForm, `TraceAction, `AutomatonSemantics, `SpectralDefinitions, `WordCounting, `ConcreteMachine, `MachineInvariant, `SpectralAData, `SpectralAPQRows0, `SpectralAPQRows10, `SpectralAPQRows15, `SpectralAPQRows5, `SpectralAPQ, `SpectralAQPRows0, `SpectralAQPRows10, `SpectralAQPRows15, `SpectralAQPRows5, `SpectralAQP, `SpectralAIntertwineRows0, `SpectralAIntertwineRows10, `SpectralAIntertwineRows15, `SpectralAIntertwineRows5, `SpectralAIntertwine, `SpectralAResult, `SpectralCData, `SpectralCPQRows0, `SpectralCPQRows10, `SpectralCPQRows15, `SpectralCPQRows5, `SpectralCPQ, `SpectralCQPRows0, `SpectralCQPRows10, `SpectralCQPRows15, `SpectralCQPRows5, `SpectralCQP, `SpectralCIntertwineRows0, `SpectralCIntertwineRows10, `SpectralCIntertwineRows15, `SpectralCIntertwineRows5, `SpectralCIntertwine, `SpectralCResult, `SpectralLData, `SpectralLPQRows0, `SpectralLPQRows10, `SpectralLPQRows15, `SpectralLPQRows5, `SpectralLPQ, `SpectralLQPRows0, `SpectralLQPRows10, `SpectralLQPRows15, `SpectralLQPRows5, `SpectralLQP, `SpectralLIntertwineRows0, `SpectralLIntertwineRows10, `SpectralLIntertwineRows15, `SpectralLIntertwineRows5, `SpectralLIntertwine, `SpectralTrees, `SpectralIntrinsicG, `SpectralIntrinsicH, `SpectralWitness, `Endpoint, `StatementClosure]
  let mut n : Nat := 0
  let mut bad : Array Name := #[]
  for (c, ci) in env.constants.toList do
    match env.getModuleIdxFor? c with
    | some idx =>
      if pkt.contains env.header.moduleNames[idx.toNat]! then
        n := n + 1
        let unsafeOrPartial : Bool := ci.isUnsafe || ci.isPartial
        if unsafeOrPartial then bad := bad.push c
        if (Lean.Compiler.getImplementedBy? env c).isSome then bad := bad.push c
        if Lean.isExtern env c then bad := bad.push c
        if (c.toString.splitOn "_unsafe_rec").length > 1 then bad := bad.push c
    | none => pure ()
  logInfo m!"ROOT_META packet_modules={pkt.size} local={n} flagged={bad}"
#print axioms MathDB330264.conjecture_false
#print axioms MathDB330264.counterexample
#check @MathDB330264.conjecture_false
