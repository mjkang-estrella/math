import Certificates
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let pkt := (← IO.FS.readFile "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/slownim-parent-final-r1/rootcheck/order.txt").splitOn "\n" |>.filter (· ≠ "")
  let isLocal : Name → Bool := fun c => match env.getModuleIdxFor? c with
    | some idx => pkt.contains (env.header.moduleNames[idx.toNat]!).toString
    | none => false
  let mut n : Nat := 0
  let mut bad : Array Name := #[]
  for (c, ci) in env.constants.toList do
    if isLocal c then
      n := n + 1
      if ci.isUnsafe || ci.isPartial then bad := bad.push c
      if (Lean.Compiler.getImplementedBy? env c).isSome then bad := bad.push c
      if Lean.isExtern env c then bad := bad.push c
      if (c.toString.splitOn "_unsafe_rec").length > 1 then bad := bad.push c
  logInfo m!"ROOT_META packet_modules={pkt.length} local={n} flagged={bad}"
  let mut stack : Array Name := #[`SlowNim360653.conjecture1_false]
  let mut seen : NameSet := {}
  let mut reach : Nat := 0
  let mut badReach : Array Name := #[]
  let mut steps : Nat := 0
  while stack.size > 0 && steps < 1000000 do
    steps := steps + 1
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    if !isLocal c then continue
    reach := reach + 1
    if bad.contains c then badReach := badReach.push c
    match env.find? c with
    | none => badReach := badReach.push c
    | some ci =>
      let mut used := ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then used := used ++ v.getUsedConstants
      for u in used do
        if !seen.contains u then stack := stack.push u
  logInfo m!"ROOT_CLOSURE endpoint=SlowNim360653.conjecture1_false local_reachable={reach} flagged_reachable={badReach} steps={steps}"
#print axioms SlowNim360653.conjecture1_false
#check @SlowNim360653.conjecture1_false
#print axioms SlowNim360653.two_every_profile_nash
#print axioms SlowNim360653.literal_bridge
#print SlowNim360653.Conjecture
#print SlowNim360653.IsNash
#print SlowNim360653.Admissible
#print SlowNim360653.payoff
#print SlowNim360653.loser
#print SlowNim360653.length
#print SlowNim360653.run
#print SlowNim360653.GMProfile
#print SlowNim360653.GM
#print SlowNim360653.gm
#print SlowNim360653.pivotValue
#print SlowNim360653.multiples
#print SlowNim360653.Strategy
#print SlowNim360653.Legal
#print SlowNim360653.move
#print SlowNim360653.Terminal
#print SlowNim360653.replace
