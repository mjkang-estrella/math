import Endpoint
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let pkt := (← IO.FS.readFile "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/nanostar-parent-final-r1/rootcheck/order.txt").splitOn "\n" |>.filter (· ≠ "")
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
  let mut stack : Array Name := #[`R162.not_conjecture349177]
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
  logInfo m!"ROOT_CLOSURE endpoint=R162.not_conjecture349177 local_reachable={reach} flagged_reachable={badReach} steps={steps}"
#print axioms R162.not_conjecture349177
#check @R162.not_conjecture349177
#print R162.Conjecture349177
#print R162.Realizable
#print R162.phiGraph
#print R162.orbit
#print R162.nanostar
#print R162.arm
