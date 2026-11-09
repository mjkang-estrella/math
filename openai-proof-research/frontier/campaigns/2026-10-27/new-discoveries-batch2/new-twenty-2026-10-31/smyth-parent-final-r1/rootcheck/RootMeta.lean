import Endpoint
import Controls
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let pkt : Array Name := #[`Base, `Controls, `Bridges, `CountBase, `S00, `S01, `S02, `S03, `S04, `S05, `S06, `S07, `S08, `S09, `S10, `S11, `S12, `S13, `S14, `S15, `S16, `S17, `S18, `S19, `T00, `T01, `T02, `T03, `T04, `T05, `T06, `T07, `T08, `T09, `T10, `T11, `T12, `T13, `T14, `T15, `T16, `T17, `T18, `T19, `T20, `Counts, `Endpoint, `Audit]
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
#print axioms Smyth1512.not_conjecture15
#print axioms Smyth1512.nonvacuity
#check @Smyth1512.not_conjecture15
