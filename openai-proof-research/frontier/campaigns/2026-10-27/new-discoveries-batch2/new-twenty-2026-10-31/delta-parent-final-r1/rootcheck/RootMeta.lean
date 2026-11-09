import Round2Final
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let pkt := (← IO.FS.readFile "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/delta-parent-final-r1/rootcheck/order.txt").splitOn "\n" |>.filter (· ≠ "")
  let mut n : Nat := 0
  let mut bad : Array Name := #[]
  for (c, ci) in env.constants.toList do
    match env.getModuleIdxFor? c with
    | some idx =>
      if pkt.contains (env.header.moduleNames[idx.toNat]!).toString then
        n := n + 1
        let unsafeOrPartial : Bool := ci.isUnsafe || ci.isPartial
        if unsafeOrPartial then bad := bad.push c
        if (Lean.Compiler.getImplementedBy? env c).isSome then bad := bad.push c
        if Lean.isExtern env c then bad := bad.push c
        if (c.toString.splitOn "_unsafe_rec").length > 1 then bad := bad.push c
    | none => pure ()
  logInfo m!"ROOT_META packet_modules={pkt.length} local={n} flagged={bad}"
#print axioms Round2.literal_negation
#check @Round2.literal_negation
